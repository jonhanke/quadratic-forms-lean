/-
# Conway–Sloane, Ch. 15, §3.4: the forms of determinant $-7$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §3.4, pp. 365–366
(`conwaysloane1999`): the binary forms of determinant $-7$ make up two proper classes, those of
$\begin{pmatrix}1&0\\0&-7\end{pmatrix}$ and $\begin{pmatrix}3&2\\2&-1\end{pmatrix}$.

**Proves** `det7_classes : Det7ClassesStatement` (stated in `BinaryExtra.lean`; formerly open because it needs
Theorem 1 for all forms, now `Binary.theorem1`). *Proof:* the sequence (5) of $f$ is ultimately periodic and its cycle
consists of reduced forms (12) of determinant $-7$ (`cycleSet_isReducedIndef`); there are exactly eight of them, and they
form the two cycles of `det7_cycles`; every form is properly equivalent to the forms of its sequence.
-/
import QuadFormsKB.Literature.ConwaySloane.BinaryExtra
import QuadFormsKB.Literature.ConwaySloane.BinaryTheorem1

namespace QuadFormsKB.ConwaySloane.Binary

/-- The reduced indefinite forms (12) of determinant $-7$. -/
theorem reduced_det7 {a b c : ℤ} (h : IsReducedIndef a b c) (hd : a * c - b ^ 2 = -7) :
    (a, b, c) ∈ [(3, 1, -2), (-2, 1, 3), (2, 1, -3), (-3, 1, 2), (3, 2, -1), (-1, 2, 3), (1, 2, -3),
      (-3, 2, 1)] := by
  obtain ⟨hb, h1, h2, h3⟩ := h
  have hac : a * c = b ^ 2 - 7 := by linarith
  have hb2 : b ^ 2 < 7 := by nlinarith
  have hb' : b ≤ 2 := by nlinarith
  have ha0 : a ≠ 0 := by rintro rfl; nlinarith
  have hc0 : c ≠ 0 := by rintro rfl; nlinarith
  have hab : |a| ≤ 6 := by
    have : |a| * |c| = |b ^ 2 - 7| := by rw [← abs_mul, hac]
    have hc1 : 1 ≤ |c| := Int.one_le_abs hc0
    have : |b ^ 2 - 7| ≤ 6 := by rw [abs_le]; constructor <;> nlinarith
    nlinarith [abs_nonneg a]
  have hcb : |c| ≤ 6 := by
    have : |a| * |c| = |b ^ 2 - 7| := by rw [← abs_mul, hac]
    have ha1 : 1 ≤ |a| := Int.one_le_abs ha0
    have : |b ^ 2 - 7| ≤ 6 := by rw [abs_le]; constructor <;> nlinarith
    nlinarith [abs_nonneg c]
  obtain ⟨ha1, ha2⟩ := abs_le.mp hab
  obtain ⟨hc1, hc2⟩ := abs_le.mp hcb
  have hb1 : 1 ≤ b := hb
  clear hab hcb hb2 hb ha0 hc0
  revert h1 h2 h3 hac
  interval_cases b <;> interval_cases a <;> interval_cases c <;> decide

/-- **The forms of determinant $-7$ form the two proper classes** of $\begin{pmatrix}1&0\\0&-7\end{pmatrix}$ and
$\begin{pmatrix}3&2\\2&-1\end{pmatrix}$ (Conway–Sloane §3.4, p. 366; the two classes are distinct by
`det7_not_equiv`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 366 (determinant −7: two classes)"]
theorem det7_classes : Det7ClassesStatement := by
  intro f hf
  have hsq : ¬ IsSquare (-f.det) := by
    rw [hf]
    exact not_isSquare_of_between (k := 2) (by norm_num) (by norm_num) (by norm_num)
  have hper := ((theorem1.holds f f hsq hsq).1)
  obtain ⟨x, hx⟩ := recurrentSet_nonempty hper
  obtain ⟨n, -, hn⟩ := hx 0
  have hfx : ProperEquiv f x := hn ▸ (properEquiv_sequenceOf hsq n).1
  have hxdet : x.det = -7 := by rw [← hn, (properEquiv_sequenceOf hsq n).2, hf]
  have hred := cycleSet_isReducedIndef (by rw [hf]; norm_num) hsq x hx
  have hmem := reduced_det7 hred hxdet
  obtain ⟨hc1, hc2⟩ := det7_cycles
  have hsq7 : ¬ IsSquare (-(BinForm.det ⟨3, 2, -1⟩)) := by
    have : -(BinForm.det ⟨3, 2, -1⟩) = 7 := by decide
    rw [this]; exact not_isSquare_of_between (k := 2) (by norm_num) (by norm_num) (by norm_num)
  have hsq7' : ¬ IsSquare (-(BinForm.det ⟨2, 1, -3⟩)) := by
    have : -(BinForm.det ⟨2, 1, -3⟩) = 7 := by decide
    rw [this]; exact not_isSquare_of_between (k := 2) (by norm_num) (by norm_num) (by norm_num)
  -- every element of a cycle list is properly equivalent to the start of the cycle
  have hin : ∀ (g : BinForm) (P : ℕ) (L : List BinForm), ¬ IsSquare (-g.det) → CycleData g P L →
      x ∈ L → ProperEquiv g x := by
    intro g P L hg hcd hxL
    have hxc : x ∈ cycleSet g := by rw [hcd.cycleSet_eq.2]; exact hxL
    obtain ⟨m, -, hm⟩ := hxc 0
    exact hm ▸ (properEquiv_sequenceOf hg m).1
  have hx3 : x = ⟨x.a, x.b, x.c⟩ := rfl
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h <;> obtain ⟨ha, hb, hc⟩ := h
  -- the cycle of `3^2(-1)`: `⟨3,2,-1⟩, ⟨-1,2,3⟩, ⟨3,1,-2⟩, ⟨-2,1,3⟩`
  · right; exact hfx.trans (hin _ _ _ hsq7 hc1 (by rw [hx3, ha, hb, hc]; decide)).symm
  · right; exact hfx.trans (hin _ _ _ hsq7 hc1 (by rw [hx3, ha, hb, hc]; decide)).symm
  · left; exact hfx.trans ((hin _ _ _ hsq7' hc2 (by rw [hx3, ha, hb, hc]; decide)).symm.trans det7_principal.1)
  · left; exact hfx.trans ((hin _ _ _ hsq7' hc2 (by rw [hx3, ha, hb, hc]; decide)).symm.trans det7_principal.1)
  · right; exact hfx.trans (hin _ _ _ hsq7 hc1 (by rw [hx3, ha, hb, hc]; decide)).symm
  · right; exact hfx.trans (hin _ _ _ hsq7 hc1 (by rw [hx3, ha, hb, hc]; decide)).symm
  · left; exact hfx.trans ((hin _ _ _ hsq7' hc2 (by rw [hx3, ha, hb, hc]; decide)).symm.trans det7_principal.1)
  · left; exact hfx.trans ((hin _ _ _ hsq7' hc2 (by rw [hx3, ha, hb, hc]; decide)).symm.trans det7_principal.1)

end QuadFormsKB.ConwaySloane.Binary
