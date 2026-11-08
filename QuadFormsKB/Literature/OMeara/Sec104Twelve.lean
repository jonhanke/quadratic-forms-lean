/-
# O'Meara Example 104:12, lattice part: odd unimodular indefinite $\mathbb Z$-lattices

**Layer:** integral forms `QuadForm ℤ n` (the lattice $L = \mathbb Z^n$ with O'Meara's $B(x, x) = Q(x)$), as in
`Sec104Indef.lean`.

**Proves** the second part of Example 104:12 (O'Meara 1973, §104, p. 321): a unimodular $\mathbb Z$-lattice $L$
($\tfrac12H_Q$ integral of determinant $\pm1$) with norm $\mathfrak nL = \mathbb Z$ on a space with $V_\infty$ isotropic
is isometric to $\langle 1\rangle^p \perp \langle -1\rangle^q$:
* `omeara104_12_lattice`, and `omeara104_12Lattice_holds : OMeara104_12Lattice Q` (the named statement of
  `Sec102To104.lean`), unconditionally.

**Route.** O'Meara deduces the lattice statement from the space statement (`omeara104_12_space`) and the theory of
§§92–93 and 104:5. Here the elementary route of Serre (*A Course in Arithmetic*, Ch. V, §2.2, Thm. 4), already in the
library as `Cassels.Ch9Ex11.exists_signDiag`, is used: an indefinite, properly primitive, classically integral form of
determinant $\pm 1$ is $\mathbb Z$-equivalent to a sign-diagonal form $\sum_i \varepsilon_ix_i^2$. The hypotheses
translate: $V_\infty$ isotropic and $V$ regular give that $Q$ takes both signs over $\mathbb R$; $\mathfrak nL = \mathbb Z$
gives an odd diagonal coefficient (properly primitive); a permutation of the variables sorts the signs.
-/
import QuadFormsKB.Literature.OMeara.Sec102To104
import QuadFormsKB.Literature.Cassels.Ch9.Ex11Serre
import QuadFormsKB.Literature.Cassels.Ch9.Ex11Cancel

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open QuadFormsKB.Siegel QuadFormsKB.Cassels.Ch9Ex11

variable {n : ℕ}

/-- **A regular real form with an isotropic vector takes both signs**: if $\det H_Q \ne 0$ and $Q(x) = 0$ for some
$x \ne 0$ in $\mathbb R^n$, then $Q$ is indefinite (`Cassels.Ch9Ex11.IsIndefinite`: a positive and a negative real
value). *Proof:* with $y = xH$ one has $Q(x + ty) = t\,c + t^2Q(y)$, $c = y \cdot y > 0$. -/
theorem isIndefinite_of_isotropic_real (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) {x : Fin n → ℝ} (hx : x ≠ 0)
    (hQx : Q.evalIn ℝ x = 0) : Cassels.Ch9Ex11.IsIndefinite Q := by
  set H := Q.hessian.map (algebraMap ℤ ℝ) with hH
  have hHdet : H.det ≠ 0 := by
    have h := RingHom.map_det (algebraMap ℤ ℝ) Q.hessian
    rw [RingHom.mapMatrix_apply] at h
    rw [hH, ← h]; exact (map_ne_zero_iff _ (algebraMap ℤ ℝ).injective_int).mpr hdet
  set y : Fin n → ℝ := x ᵥ* H with hy
  have hy0 : y ≠ 0 := by
    intro h
    exact hx (Matrix.eq_zero_of_vecMul_eq_zero hHdet h)
  set c : ℝ := y ⬝ᵥ y with hc
  have hcpos : 0 < c := by
    rw [hc]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra h; push Not at h; exact hy0 (funext h)
    have : y ⬝ᵥ y = ∑ j, y j ^ 2 := by simp [dotProduct, sq]
    rw [this]
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun j _ => sq_nonneg (y j))
      (Finset.mem_univ i))
  set d := Q.evalIn ℝ y
  have key : ∀ t : ℝ, Q.evalIn ℝ (x + t • y) = t * c + t ^ 2 * d := by
    intro t
    have hp := QuadForm.polar_eq_hessian ℝ Q x (t • y)
    rw [hQx, Cassels.Ch9Ex11.evalIn_smul] at hp
    have : x ⬝ᵥ (H *ᵥ (t • y)) = t * c := by
      rw [Matrix.mulVec_smul, dotProduct_smul, Matrix.dotProduct_mulVec, smul_eq_mul, hc]
    rw [← hH, this] at hp
    linarith
  rcases lt_trichotomy d 0 with hd | hd | hd
  · refine ⟨⟨x + (-c / (2 * d)) • y, ?_⟩, ⟨x + (-1 : ℝ) • y, ?_⟩⟩
    · rw [key]
      have : -c / (2 * d) * c + (-c / (2 * d)) ^ 2 * d = -(c ^ 2) / (4 * d) := by field_simp; ring
      rw [this]
      exact div_pos_of_neg_of_neg (by nlinarith) (by linarith)
    · rw [key]; nlinarith
  · refine ⟨⟨x + (1 : ℝ) • y, ?_⟩, ⟨x + (-1 : ℝ) • y, ?_⟩⟩ <;> rw [key, hd] <;> nlinarith
  · refine ⟨⟨x + (1 : ℝ) • y, ?_⟩, ⟨x + (-c / (2 * d)) • y, ?_⟩⟩
    · rw [key]; nlinarith
    · rw [key]
      have : -c / (2 * d) * c + (-c / (2 * d)) ^ 2 * d = -(c ^ 2) / (4 * d) := by field_simp; ring
      rw [this]
      exact div_neg_of_neg_of_pos (by nlinarith) (by linarith)

/-- The sign-diagonal form $\langle 1\rangle^p \perp \langle -1\rangle^{n-p}$ has $n - p$ entries $-1$ (for
$p \le n$). -/
theorem negCountR_signDiag (p : ℕ) :
    HasseIsoNF.negCountR (fun i : Fin n => (((if i.val < p then 1 else -1 : ℤ)) : ℝ)) = n - p := by
  rw [card_neg_eq]
  have e : ∀ i : Fin n, (decide ((if i.val < p then 1 else -1 : ℤ) < 0) = true) ↔ p ≤ i.val := by
    intro i; split_ifs with h <;> simp <;> omega
  rw [Fintype.card_subtype]
  have hf : (Finset.univ.filter fun i : Fin n => decide ((if i.val < p then 1 else -1 : ℤ) < 0) = true) =
      Finset.univ.filter fun i : Fin n => p ≤ i.val := Finset.filter_congr fun i _ => e i
  rw [hf]
  have hmap : (Finset.univ.filter fun i : Fin n => p ≤ i.val).map Fin.valEmbedding = Finset.Ico p n := by
    ext k; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨a, h, rfl⟩; exact ⟨h, a.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨k, h2⟩, h1, rfl⟩
  rw [← Finset.card_map, hmap, Nat.card_Ico]

/-- **Example 104:12, lattice part** (O'Meara 1973, §104, p. 321): let $Q$ be a form over $\mathbb Z$ in $n$
variables whose lattice $\mathbb Z^n$ is unimodular in O'Meara's sense (`IsClassicallyIntegral Q` and
$\det H_Q = \pm 2^n$, i.e. $\tfrac12H_Q$ integral of determinant $\pm 1$), of norm $\mathbb Z$ (the values $Q(x)$
generate $\mathbb Z$), with $V_\infty$ isotropic. Then $Q$ is $\mathbb Z$-equivalent to
$\langle 1\rangle^p \perp \langle -1\rangle^{n-p}$ for some $p$. Unconditional. -/
@[kb "omeara1963" "§104, 104:12, p. 321 (lattice part: L ≅ ⟨1⟩ᵖ ⊥ ⟨−1⟩^q)"]
theorem omeara104_12_lattice (Q : QuadForm ℤ n) (hci : IsClassicallyIntegral Q)
    (hdet : Q.hessian.det = 2 ^ n ∨ Q.hessian.det = -2 ^ n)
    (hnorm : Ideal.span (Set.range Q.eval) = ⊤)
    (hiso : (Q.map (Int.castRingHom ℚ)).IsotropicIn ℝ) :
    ∃ p : ℕ, Q.IsometricIn ℤ (signDiag ℤ p) := by
  classical
  obtain ⟨x, hx, hQx⟩ := hiso
  rw [Cassels.Ch9Ex11.evalIn_real_map_rat] at hQx
  have hdet0 : Q.hessian.det ≠ 0 := by
    rcases hdet with h | h <;> rw [h] <;> simp
  have hind : Cassels.Ch9Ex11.IsIndefinite Q := isIndefinite_of_isotropic_real Q hdet0 hx hQx
  have hn : 0 < n := by have := two_le_of_isIndefinite hind; omega
  -- unimodular in Cassels' sense
  have hu : IsUnimodularCI Q := by
    refine ⟨hci, ?_⟩
    have h2 := hessian_det_eq_casselsMat hci
    have hpos : (2 : ℤ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    rcases hdet with h | h
    · left
      have : (2 : ℤ) ^ n * (casselsMat Q).det = 2 ^ n * 1 := by rw [← h2, h, mul_one]
      exact mul_left_cancel₀ hpos this
    · right
      have : (2 : ℤ) ^ n * (casselsMat Q).det = 2 ^ n * (-1) := by rw [← h2, h]; ring
      exact mul_left_cancel₀ hpos this
  -- properly primitive: some diagonal coefficient is odd
  have hpp : IsProperlyPrimitive Q := by
    refine ⟨isPrimitiveCI_of_unimodular hn hu, ?_⟩
    by_contra h
    push Not at h
    have hev := (diag_even_iff hci).mp h
    have hle : Ideal.span (Set.range Q.eval) ≤ Ideal.span {(2 : ℤ)} := by
      rw [Ideal.span_le]
      rintro _ ⟨z, rfl⟩
      exact Ideal.mem_span_singleton.mpr (hev z)
    rw [hnorm, top_le_iff, Ideal.span_singleton_eq_top] at hle
    exact absurd hle (by decide)
  obtain ⟨ε, hε, hQε⟩ := exists_signDiag n Q hu hind hpp
  -- sort the signs
  obtain ⟨q, hqdef⟩ : ∃ q, q = HasseIsoNF.negCountR (fun i => (ε i : ℝ)) := ⟨_, rfl⟩
  have hq : q ≤ n := by
    rw [hqdef, card_neg_eq]
    exact (Fintype.card_subtype_le _).trans (by simp)
  set s : Fin n → ℤ := fun i => if i.val < n - q then 1 else -1 with hs
  have hsv : IsSignVec s := fun i => by simp only [hs]; split_ifs <;> simp
  have hcount : HasseIsoNF.negCountR (fun i => (ε i : ℝ)) = HasseIsoNF.negCountR (fun i => (s i : ℝ)) := by
    rw [hs, negCountR_signDiag (n - q), ← hqdef]; omega

  obtain ⟨σ, hσ⟩ := exists_perm_of_negCount hε hsv hcount
  have hperm : IntEquiv (QuadForm.diag ε) (QuadForm.diag s) := by
    refine intEquiv_of_perm σ.symm fun y => ?_
    rw [eval_diag_int, eval_diag_int]
    rw [← Equiv.sum_comp σ (fun j => ε j * (y ∘ ⇑σ.symm) j ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hσ]
  refine ⟨n - q, ?_⟩
  have hfin : IntEquiv Q (QuadForm.diag s) := IsometricGL.trans hQε hperm
  exact (isometricGL_iff_isometricIn Q _).mp hfin

/-- **The named statement `OMeara104_12Lattice` holds** for every form over $\mathbb Z$ (O'Meara 1973, §104, 104:12,
p. 321), unconditionally (`omeara104_12_lattice`). -/
@[kb "omeara1963" "§104, 104:12, p. 321 (lattice part: L ≅ ⟨1⟩ᵖ ⊥ ⟨−1⟩^q)"]
theorem omeara104_12Lattice_holds (Q : QuadForm ℤ n) : OMeara104_12Lattice Q :=
  ⟨fun hci hdet hnorm hiso => omeara104_12_lattice Q hci hdet hnorm hiso⟩

end QuadFormsKB.Lattices
