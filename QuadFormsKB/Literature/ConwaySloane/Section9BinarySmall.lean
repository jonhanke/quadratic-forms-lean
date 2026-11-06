/-
# Conway–Sloane, Ch. 15, §9.7, Cor. 22, $n = 2$: binary genera of determinant $\lvert d\rvert \le 16$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, p. 395–396
(`conwaysloane1999`).

**Layer:** symmetric integer $2 \times 2$ matrices, congruence over $\mathbb Z$ (`CongrIn ℤ`), the genus
`Siegel.SameGenus`; finite data in `Section9BinaryData.lean` (checked by kernel evaluation).

**Proves**
* `reduce_neg`: every symmetric integral $2 \times 2$ matrix of negative determinant is congruent over $\mathbb Z$ to a
  *reduced* one ($\lvert 2b\rvert \le \lvert a\rvert$, $a^2 \le \lvert d\rvert$; or $a = 0$, $0 < b$, $0 \le c < 2b$);
* `valMod_of_sameGenus`: the values of a form modulo a prime power $p^k$ are a genus invariant (the $\mathbb Z_p$
  component);
* `binaryOneClassUpTo16`: for $\lvert d\rvert \le 16$ an indefinite binary form has only one class in its genus.
  The reduced forms of each determinant fall into finitely many $\mathrm{GL}_2(\mathbb Z)$ classes (explicit
  matrices, `tbl_ok`), and two inequivalent classes of one determinant are separated by the parity of the diagonal or
  by the values mod some prime power (`certs_ok`, `sep_all`); hence classes are determined by the genus;
* `corollary22_uncond`: Corollary 22, unconditional.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Cor22
import QuadFormsKB.Literature.ConwaySloane.Section9Binary
import QuadFormsKB.Literature.ConwaySloane.Section9BinaryData

namespace QuadFormsKB.ConwaySloane

open Siegel Lattices Matrix

namespace BinSmall

/-- The symmetric matrix of a triple. -/
def mat3 (f : Tri) : Matrix (Fin 2) (Fin 2) ℤ := !![f.1, f.2.1; f.2.1, f.2.2]

theorem mat3_mk (a b c : ℤ) : mat3 (a, b, c) = !![a, b; b, c] := rfl

theorem mat3_transpose (f : Tri) : (mat3 f)ᵀ = mat3 f := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mat3]

/-- Congruence by a unimodular matrix: $M^{\mathsf T}\,\mathrm{mat}(f)\,M = \mathrm{mat}(M\cdot f)$. -/
theorem congr_act (f : Tri) (M : ℤ × ℤ × ℤ × ℤ) (h : detM M = 1 ∨ detM M = -1) :
    CongrIn ℤ (mat3 f) (mat3 (actT f M)) := by
  obtain ⟨a, b, c⟩ := f
  obtain ⟨p, q, r, s⟩ := M
  refine congrIn_of_mul !![p, q; r, s] ?_ ?_
  · rw [Matrix.det_fin_two_of]
    simp only [detM] at h
    rcases h with h | h <;> rw [h]
    · exact isUnit_one
    · exact isUnit_one.neg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [actT, mat3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Congruent matrices have the same determinant. -/
theorem det_eq_of_congrIn {M M' : Matrix (Fin 2) (Fin 2) ℤ} (h : CongrIn ℤ M M') : M'.det = M.det := by
  obtain ⟨g, rfl⟩ := h
  have hu : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rcases Int.isUnit_iff.1 hu with h | h <;> rw [h] <;> ring

theorem det_mat3 (f : Tri) : (mat3 f).det = detT f := by
  simp [mat3, Matrix.det_fin_two_of, detT]; ring

/-! ### Reduction -/

/-- The case $a = 0$: reduce $c$ modulo $2b$. -/
theorem red_zero (b c : ℤ) (hb : b ≠ 0) : ∃ f : Tri, RedT f ∧ CongrIn ℤ !![0, b; b, c] (mat3 f) := by
  obtain ⟨b', hb'pos, h1⟩ : ∃ b' : ℤ, 0 < b' ∧ CongrIn ℤ !![0, b; b, c] !![0, b'; b', c] := by
    rcases lt_or_gt_of_ne hb with h | h
    · exact ⟨-b, by omega, congrIn_neg 0 b c⟩
    · exact ⟨b, h, CongrIn.refl _⟩
  have h2b : (2 * b') ≠ 0 := by omega
  refine ⟨(0, b', c % (2 * b')), Or.inr ⟨rfl, hb'pos, Int.emod_nonneg _ h2b,
    Int.emod_lt_of_pos _ (by omega)⟩, h1.trans ?_⟩
  rw [mat3_mk]
  exact congrIn_shear 0 b' c (-(c / (2 * b'))) b' (c % (2 * b')) (by ring) (by rw [Int.emod_def]; ring)

/-- **Reduction.** Every symmetric $2 \times 2$ integer matrix of negative determinant is congruent over $\mathbb Z$
to a reduced one (descent on $\lvert a\rvert$: a shear makes $2\lvert b\rvert \le \lvert a\rvert$, then either swap
(if $\lvert c\rvert < \lvert a\rvert$) or the form is reduced). -/
theorem reduce_neg (n : ℕ) : ∀ a b c : ℤ, a.natAbs = n → a * c - b ^ 2 < 0 →
    ∃ f : Tri, RedT f ∧ CongrIn ℤ !![a, b; b, c] (mat3 f) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c hn hd
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by rintro rfl; simp at hd
    exact red_zero b c hb
  · -- a shear making `2 |b'| ≤ |a|`
    have hr0 : 0 ≤ b % a := Int.emod_nonneg _ ha
    have hr1 : b % a < |a| := by rw [Int.abs_eq_natAbs]; exact Int.emod_lt _ ha
    have hrb : b % a = b - a * (b / a) := Int.emod_def _ _
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, -|a| ≤ 2 * (b + k * a) ∧ 2 * (b + k * a) ≤ |a| := by
      by_cases h2 : 2 * (b % a) ≤ |a|
      · refine ⟨-(b / a), ?_, ?_⟩ <;> nlinarith [abs_nonneg a]
      · rcases lt_or_gt_of_ne ha with ha' | ha'
        · rw [abs_of_neg ha'] at h2 hr1 ⊢
          refine ⟨-(b / a) + 1, ?_, ?_⟩ <;> nlinarith
        · rw [abs_of_pos ha'] at h2 hr1 ⊢
          refine ⟨-(b / a) - 1, ?_, ?_⟩ <;> nlinarith
    obtain ⟨b', hb'⟩ : ∃ b', b' = b + k * a := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c', c' = c + 2 * k * b + k ^ 2 * a := ⟨_, rfl⟩
    have hsh := congrIn_shear a b c k b' c' hb' hc'
    have hdd : a * c' - b' ^ 2 = a * c - b ^ 2 := by rw [hb', hc']; ring
    rw [← hb'] at hk1 hk2
    by_cases hlt : c'.natAbs < a.natAbs
    · obtain ⟨f, hf, hcf⟩ := ih c'.natAbs (hn ▸ hlt) c' b' a rfl (by linarith [mul_comm a c'])
      exact ⟨f, hf, (hsh.trans (congrIn_swap a b' c')).trans hcf⟩
    · refine ⟨(a, b', c'), Or.inl ⟨ha, hk1, hk2, ?_⟩, hsh⟩
      show a ^ 2 ≤ |a * c' - b' ^ 2|
      have hcge : |a| ≤ |c'| := by
        rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]; exact_mod_cast (not_lt.1 hlt)
      have hac : a ^ 2 ≤ |a * c'| := by
        rw [abs_mul, sq]
        calc a * a = |a| * |a| := (abs_mul_abs_self a).symm
          _ ≤ |a| * |c'| := mul_le_mul_of_nonneg_left hcge (abs_nonneg a)
      have hb2 : 4 * b' ^ 2 ≤ a ^ 2 := by
        have h1 : |2 * b'| ≤ |a| := abs_le.2 ⟨hk1, hk2⟩
        have := sq_le_sq.2 h1
        nlinarith
      have ha2 : 0 < a ^ 2 := by positivity
      rcases le_or_gt 0 (a * c') with h0 | h0
      · rw [abs_of_nonneg h0] at hac
        exfalso
        nlinarith
      · rw [abs_of_neg h0] at hac
        rw [abs_of_neg (by linarith)]
        nlinarith [sq_nonneg b']

/-- The bounds on a reduced form with $-16 \le d \le -2$. -/
theorem red_bounds {a b c : ℤ} (h : RedT (a, b, c)) (h1 : -16 ≤ detT (a, b, c)) (h2 : detT (a, b, c) ≤ -2) :
    a ∈ Finset.Icc (-4 : ℤ) 4 ∧ b ∈ Finset.Icc (-4 : ℤ) 4 ∧ c ∈ Finset.Icc (-16 : ℤ) 16 := by
  simp only [Finset.mem_Icc]
  dsimp only [RedT, detT] at h h1 h2
  rcases h with ⟨ha, hb1, hb2, hq⟩ | ⟨ha, hb0, hc0, hc1⟩
  · rw [abs_of_neg (by linarith)] at hq
    have ha4 : a ≤ 4 := by by_contra hh; push Not at hh; nlinarith
    have ha4' : -4 ≤ a := by by_contra hh; push Not at hh; nlinarith
    have habs : |a| ≤ 4 := abs_le.2 ⟨by linarith, ha4⟩
    have hb : -2 ≤ b ∧ b ≤ 2 := ⟨by linarith, by linarith⟩
    have hb4 : b ^ 2 ≤ 4 := by nlinarith
    have hac : |a * c| ≤ 16 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
    have ha1 : 1 ≤ |a| := Int.one_le_abs ha
    have hc : |c| ≤ 16 := by
      rw [abs_mul] at hac
      nlinarith [abs_nonneg c]
    obtain ⟨hc1', hc2'⟩ := abs_le.1 hc
    exact ⟨⟨ha4', ha4⟩, ⟨by linarith, by linarith⟩, ⟨hc1', hc2'⟩⟩
  · subst ha
    have hb4 : b ≤ 4 := by by_contra hh; push Not at hh; nlinarith
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith, hb4⟩, ⟨by linarith, by linarith⟩⟩

/-! ### Values modulo a prime power are a genus invariant -/

/-- The form $f$ takes the value $r$ modulo $m$: $m \mid f(x, y) - r$ for some integers $x, y$. -/
def ValMod (m : ℕ) (f : Tri) (r : ℤ) : Prop := ∃ x y : ℤ, (m : ℤ) ∣ valT f x y - r

/-- **Values modulo $p^k$ are a genus invariant** (the $\mathbb Z_p$ component, reduced mod $p^k$): if the forms
`X`, `Y` are in one genus and `X` takes the value `r` mod $p^k$, so does `Y`. -/
theorem valMod_of_sameGenus {X Y : Tri} (h : SameGenus (Cassels.Ch8Ex2.gramForm (mat3 Y))
    (Cassels.Ch8Ex2.gramForm (mat3 X))) (p k : ℕ) [Fact p.Prime] (r : ℤ) (hv : ValMod (p ^ k) X r) :
    ValMod (p ^ k) Y r := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨x, y, hxy⟩ := hv
  obtain ⟨g, hg⟩ := h.1 p
  have key := hg ![(x : ℤ_[p]), (y : ℤ_[p])]
  rw [gramForm_map, gramForm_map, eval_gramForm, eval_gramForm] at key
  generalize g.val *ᵥ ![(x : ℤ_[p]), (y : ℤ_[p])] = w at key
  have key2 := congrArg (PadicInt.toZModPow k) key
  have hxy' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ k)).2 hxy
  refine ⟨((PadicInt.toZModPow k (w 0)).val : ℤ), ((PadicInt.toZModPow k (w 1)).val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.map_apply, mat3, map_add, map_mul,
    eq_intCast, map_intCast] at key2
  simp only [valT, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at hxy' ⊢
  simp at key2
  linear_combination key2 + hxy'

/-- A value not attained among the residues $0 \le x, y < m$ is not attained at all. -/
theorem not_valMod_of_bounded {m : ℕ} (hm : 0 < m) (g : Tri) (r : ℤ)
    (h : ∀ x < m, ∀ y < m, (valT g x y - r) % (m : ℤ) ≠ 0) : ¬ ValMod m g r := by
  rintro ⟨x, y, hd⟩
  have : NeZero m :=NeZero.of_pos hm
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hx0 : 0 ≤ x % (m : ℤ) := Int.emod_nonneg x hm'.ne'
  have hy0 : 0 ≤ y % (m : ℤ) := Int.emod_nonneg y hm'.ne'
  have hx1 : x % (m : ℤ) < m := Int.emod_lt_of_pos x hm'
  have hy1 : y % (m : ℤ) < m := Int.emod_lt_of_pos y hm'
  apply h (x % (m : ℤ)).toNat (by omega) (y % (m : ℤ)).toNat (by omega)
  apply Int.emod_eq_zero_of_dvd
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hd' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).2 hd
  simp only [valT, Int.cast_sub, Int.cast_add, Int.cast_mul] at hd' ⊢
  rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0]
  simpa [ZMod.intCast_mod] using hd'

theorem ms_pp : ∀ m ∈ ms, ∃ p k : ℕ, p.Prime ∧ m = p ^ k := by
  intro m hm
  simp only [ms, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 2, Nat.prime_two, rfl⟩
  · exact ⟨2, 3, Nat.prime_two, rfl⟩
  · exact ⟨2, 4, Nat.prime_two, rfl⟩
  · exact ⟨2, 5, Nat.prime_two, rfl⟩
  · exact ⟨3, 1, Nat.prime_three, rfl⟩
  · exact ⟨3, 2, Nat.prime_three, rfl⟩
  · exact ⟨5, 1, by norm_num, rfl⟩
  · exact ⟨5, 2, by norm_num, rfl⟩
  · exact ⟨7, 1, by norm_num, rfl⟩
  · exact ⟨7, 2, by norm_num, rfl⟩
  · exact ⟨11, 1, by norm_num, rfl⟩
  · exact ⟨13, 1, by norm_num, rfl⟩

/-- A certificate rules out one genus: if `c.f = X` and `c.g = Y`, then `X`, `Y` are not in one genus. -/
theorem cert_contra {X Y : Tri} (h : SameGenus (Cassels.Ch8Ex2.gramForm (mat3 Y))
    (Cassels.Ch8Ex2.gramForm (mat3 X))) (c : Cert) (hc : c ∈ certs) (hcf : c.f = X) (hcg : c.g = Y) :
    False := by
  obtain ⟨hm, hv, hb⟩ := certs_ok c hc
  obtain ⟨p, k, hp, hmk⟩ := ms_pp c.m hm
  have : Fact p.Prime := ⟨hp⟩
  have hX : ValMod c.m X c.r := ⟨c.x, c.y, by rw [← hcf]; exact Int.dvd_of_emod_eq_zero hv⟩
  rw [hmk] at hX
  have hY := valMod_of_sameGenus h p k c.r hX
  rw [← hmk] at hY
  exact not_valMod_of_bounded (by rw [hmk]; exact pow_pos hp.pos _) Y c.r (by rw [← hcg]; exact hb) hY

/-- **Every symmetric matrix of determinant $d \in [-16, -2]$ is congruent to a class representative of the
table:** reduce (`reduce_neg`), then use the table of reduced forms (`cover`, `tbl_ok`). -/
theorem key_rep {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : Aᵀ = A) (d : ℤ) (hd1 : -16 ≤ d) (hd2 : d ≤ -2)
    (hAd : A.det = d) : ∃ f ∈ reps, CongrIn ℤ A (mat3 f) := by
  have hAe := eq_of_transpose_eq hA
  have h10 : A 1 0 = A 0 1 := by simpa using congrFun (congrFun hA 0) 1
  have hdA : A 0 0 * A 1 1 - A 0 1 ^ 2 = d := by rw [← hAd, Matrix.det_fin_two, h10]; ring
  obtain ⟨f, hf, hc⟩ := reduce_neg _ (A 0 0) (A 0 1) (A 1 1) rfl (by linarith)
  rw [← hAe] at hc
  have hdf : detT f = d := by rw [← det_mat3, det_eq_of_congrIn hc, hAd]
  obtain ⟨a, b, c⟩ := f
  obtain ⟨ha, hb, hc'⟩ := red_bounds hf (by rw [hdf]; exact hd1) (by rw [hdf]; exact hd2)
  obtain ⟨e, he, hef⟩ := cover a ha b hb c hc' hf (by rw [hdf]; exact hd1) (by rw [hdf]; exact hd2)
  obtain ⟨h1, h2, h3, h4⟩ := tbl_ok e he
  have hcg := congr_act e.rep e.M h2
  rw [h1, hef] at hcg
  exact ⟨e.rep, h3, hc.trans hcg.symm⟩

end BinSmall

open BinSmall

/-- **Binary genera of small determinant have one class** (Conway–Sloane, §9.7, Cor. 22, $n = 2$, "we find from
Table 15.2"): an indefinite classically integral binary form with $\lvert d\rvert \le 16$ has only one class in its
genus. *Proof.* $d = -1$ is `not_moreThanOneClass_of_det_eq_neg_one`, and $d > 0$ is not indefinite. For
$-16 \le d \le -2$ both $A$ and a form $B$ of its genus are congruent to table representatives (`key_rep`); the
representatives lie in one genus, so they coincide, since two distinct representatives of one determinant are
separated by the parity of the diagonal or by the values modulo a prime power (`sep_all`, `cert_contra`). -/
theorem binaryOneClassUpTo16 : BinaryOneClassUpTo16 := by
  refine ⟨fun A hA hd hind h16 => ?_⟩
  have hneg := det_neg_of_isIndefinite A hA hd hind
  by_cases h1 : A.det = -1
  · exact not_moreThanOneClass_of_det_eq_neg_one A hA h1
  rintro ⟨B, hB, hg, hne⟩
  apply hne
  have hdAB : B.det = A.det := by
    have := SameGenus.hessian_det_eq hg
    rw [det_hessian_gramForm_two hA, det_hessian_gramForm_two hB] at this
    linarith
  have h16' : -16 ≤ A.det ∧ A.det ≤ -2 := by omega
  obtain ⟨fA, hfA, hcA⟩ := key_rep hA A.det h16'.1 h16'.2 rfl
  obtain ⟨fB, hfB, hcB⟩ := key_rep hB A.det h16'.1 h16'.2 hdAB
  have gA : SameGenus (Cassels.Ch8Ex2.gramForm A) (Cassels.Ch8Ex2.gramForm (mat3 fA)) :=
    IntEquiv.sameGenus ((isometricGL_gramForm_iff hA (mat3_transpose _)).2 hcA)
  have gB : SameGenus (Cassels.Ch8Ex2.gramForm B) (Cassels.Ch8Ex2.gramForm (mat3 fB)) :=
    IntEquiv.sameGenus ((isometricGL_gramForm_iff hB (mat3_transpose _)).2 hcB)
  have hgen : SameGenus (Cassels.Ch8Ex2.gramForm (mat3 fA)) (Cassels.Ch8Ex2.gramForm (mat3 fB)) :=
    gA.symm.trans (hg.trans gB)
  have heq : fA = fB := by
    by_contra hne'
    have hdet : detT fA = detT fB := by
      rw [← det_mat3, ← det_mat3, det_eq_of_congrIn hcA, det_eq_of_congrIn hcB, hdAB]
    rcases sep_all fA hfA fB hfB hdet hne' with hp | ⟨c, hc, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · apply hp
      have := even_diag_of_sameGenus (mat3_transpose fA) (mat3_transpose fB) hgen
      simpa [parT, mat3, Int.even_iff] using this
    · exact cert_contra hgen.symm c hc h1 h2
    · exact cert_contra hgen c hc h1 h2
  subst heq
  exact (isometricGL_gramForm_iff hA hB).2 (hcA.trans hcB.symm)

/-- **Conway–Sloane, Corollary 22** (§9.7, p. 395), unconditional: an indefinite form of dimension $n \ge 2$ and
determinant $d$ with more than one class in its genus has $\lvert d\rvert \ge d_0(n)$, where $d_0 = 17, 128,
5^{\binom n2}, 2\cdot5^{\binom n2}$ for $n = 2$, $3$, even $n \ge 4$, odd $n \ge 5$. The case $n = 2$ is
`binaryOneClassUpTo16`, the case $n \ge 3$ is `corollary22_ge_three`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Cor. 22, p. 395 (all n, unconditional)"]
theorem corollary22_uncond : Corollary22Statement := corollary22 binaryOneClassUpTo16

end QuadFormsKB.ConwaySloane
