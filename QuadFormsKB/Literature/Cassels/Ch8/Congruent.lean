import Mathlib
import QuadFormsKB.Citation

/-!
# Cassels, Chapter 8, Lemma 5.1: forms congruent modulo a high power of $p$ are $\mathbb Z_p$-equivalent

**Setting.** $F, G$ are symmetric $n \times n$ matrices over $\mathbb Z_p$ (`Matrix (Fin n) (Fin n) ℤ_[p]`), with
$\det F \ne 0$; the quadratic forms are $x \mapsto x^{t}Fx$ and $x \mapsto x^{t}Gx$. Indices are 0-based; $n$ is the
dimension. $\lvert\cdot\rvert_p$ is the $p$-adic absolute value (`‖·‖`).

**Proves** (`exists_equiv_of_congruent`, `exists_equiv_of_dvd_pow`): if $G \equiv F$ modulo something smaller than
$\lvert 4\det F\rvert_p$ (equivalently $G \equiv F \pmod{p^k}$ entrywise with $k > v_p(4\det F) = 2v_p(2) + v_p(\det F)$),
then $G = T^{t}FT$ for some $T \in \mathrm{GL}_n(\mathbb Z_p)$ with $T \equiv 1 \pmod p$.

**Provenance.** Checked against the printed page (p. 123) on 2026-10-27: the same statement. Cassels takes
$f$ classically integral with $d(f) = d \ne 0$, $\lvert d\rvert = p^{-\delta}$, $\lambda = 1$ for $p = 2$ and $0$ otherwise,
and assumes $g_{ij} \equiv f_{ij} \pmod{p^{\delta + 2\lambda + 1}}$ (it holds for all $p$, odd or not). The hypothesis
below ($\varepsilon < \lvert 4\det F\rvert_p$) is the same condition written with absolute values. The conclusion
(a $T$ of unit determinant with $T^tFT = G$) is stated here with $T \equiv 1 \pmod p$, which is what the proof gives.

**Proof notes.** Newton iteration. Given symmetric $A = T^{t}FT$ and $G$ with $G - A$ of size $\varepsilon \le
\lvert 2\det A\rvert$, put $Y = \tfrac12 A^{-1}(G - A)$ (integral, by the adjugate formula and the size bound); then
$(1+Y)^{t}A(1+Y) - G = Y^{t}AY = \tfrac12 Y^{t}(G - A)$ has size $\varepsilon^2/\lvert 4\det A\rvert$, and
$\lvert\det A\rvert = \lvert\det F\rvert$ since $\det T$ is a unit. So with $\rho = \varepsilon_0/\lvert 4\det F\rvert < 1$
the error after $m$ steps is $\lvert 4\det F\rvert\rho^{2^m}$ and $T_m \equiv 1 \pmod p$ throughout. Instead of
proving that $T_m$ is Cauchy, the limit is extracted by compactness of $M_n(\mathbb Z_p)$ (a convergent subsequence);
continuity gives $T^{t}FT = G$, and $T \equiv 1 \pmod p$ gives a unit determinant.
-/

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- Every entry of the matrix $M$ over $\mathbb Z_p$ has $p$-adic absolute value at most $\varepsilon$. -/
def EntryNormLE (M : Matrix (Fin n) (Fin n) ℤ_[p]) (ε : ℝ) : Prop := ∀ i j, ‖M i j‖ ≤ ε

theorem EntryNormLE.mul {M N : Matrix (Fin n) (Fin n) ℤ_[p]} {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : EntryNormLE M a) (hb : EntryNormLE N b) : EntryNormLE (M * N) (a * b) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha0 hb0) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (ha i k) (hb k j) (norm_nonneg _) ha0

theorem EntryNormLE.add {M N : Matrix (Fin n) (Fin n) ℤ_[p]} {a : ℝ}
    (ha : EntryNormLE M a) (hb : EntryNormLE N a) : EntryNormLE (M + N) a := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i j) (hb i j))

theorem EntryNormLE.transpose {M : Matrix (Fin n) (Fin n) ℤ_[p]} {a : ℝ} (h : EntryNormLE M a) :
    EntryNormLE Mᵀ a := fun i j => h j i

theorem EntryNormLE.mono {M : Matrix (Fin n) (Fin n) ℤ_[p]} {a b : ℝ} (h : EntryNormLE M a) (hab : a ≤ b) :
    EntryNormLE M b := fun i j => (h i j).trans hab

theorem entryNormLE_one (M : Matrix (Fin n) (Fin n) ℤ_[p]) : EntryNormLE M 1 := fun _ _ =>
  PadicInt.norm_le_one _

theorem EntryNormLE.neg {M : Matrix (Fin n) (Fin n) ℤ_[p]} {a : ℝ} (h : EntryNormLE M a) :
    EntryNormLE (-M) a := fun i j => by simpa using h i j

theorem EntryNormLE.sub {M N : Matrix (Fin n) (Fin n) ℤ_[p]} {a : ℝ}
    (ha : EntryNormLE M a) (hb : EntryNormLE N a) : EntryNormLE (M - N) a := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

/-- In $\mathbb Z_p$, a nonzero element divides every element of smaller or equal absolute value. -/
theorem padicInt_dvd_of_norm_le {a b : ℤ_[p]} (ha : a ≠ 0) (h : ‖b‖ ≤ ‖a‖) : ∃ z : ℤ_[p], b = a * z := by
  have ha' : (a : ℚ_[p]) ≠ 0 := fun h => ha (PadicInt.coe_eq_zero.1 h)
  have hz : ‖(b : ℚ_[p]) / (a : ℚ_[p])‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.2 ha')]
    exact h
  refine ⟨⟨_, hz⟩, ?_⟩
  apply Subtype.ext
  show (b : ℚ_[p]) = (a : ℚ_[p]) * ((b : ℚ_[p]) / (a : ℚ_[p]))
  field_simp

theorem isUnit_det_one_add {P : Matrix (Fin n) (Fin n) ℤ_[p]} {ρ : ℝ} (hρ : ρ < 1)
    (hP : EntryNormLE P ρ) : IsUnit (1 + P).det := by
  have hmem : ∀ i j, P i j ∈ IsLocalRing.maximalIdeal ℤ_[p] := fun i j => by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    exact (hP i j).trans_lt hρ
  have h1 : (PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix (1 + P) = 1 := by
    ext i j
    have : PadicInt.toZMod (P i j) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod]; exact hmem i j
    simp [Matrix.one_apply, this]
  have h2 := RingHom.map_det (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (1 + P)
  rw [h1, Matrix.det_one] at h2
  by_contra hnu
  have hm : (1 + P).det ∈ IsLocalRing.maximalIdeal ℤ_[p] := (IsLocalRing.mem_maximalIdeal _).2 hnu
  have hm' : (1 + P).det - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, h2, map_one, sub_self]
  have : (1 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    have := Ideal.sub_mem _ hm hm'
    simp at this
  exact (IsLocalRing.mem_maximalIdeal _).1 this isUnit_one

/-- One Newton step. If $A, B$ are symmetric over $\mathbb Z_p$, $\det A \ne 0$ and $B - A$ has entries of
absolute value at most $\varepsilon \le \lvert 2\det A\rvert$, then there is $Y$ with entries of absolute value at
most $\varepsilon/\lvert 2\det A\rvert$ such that $(1+Y)^{t}A(1+Y) - B$ has entries of absolute value at most
$(\varepsilon/\lvert 2\det A\rvert)\,\varepsilon/\lvert 2\rvert$. -/
theorem newton_step (A B : Matrix (Fin n) (Fin n) ℤ_[p]) (hA : Aᵀ = A) (hB : Bᵀ = B) (hdet : A.det ≠ 0)
    (ε : ℝ) (hε : 0 ≤ ε) (hBA : EntryNormLE (B - A) ε) (hle : ε ≤ ‖(2 : ℤ_[p]) * A.det‖) :
    ∃ Y : Matrix (Fin n) (Fin n) ℤ_[p], EntryNormLE Y (ε / ‖(2 : ℤ_[p]) * A.det‖) ∧
      EntryNormLE ((1 + Y)ᵀ * A * (1 + Y) - B) (ε / ‖(2 : ℤ_[p]) * A.det‖ * ε / ‖(2 : ℤ_[p])‖) := by
  have h2 : (2 : ℤ_[p]) ≠ 0 := two_ne_zero
  have h2d : (2 : ℤ_[p]) * A.det ≠ 0 := mul_ne_zero h2 hdet
  have hpos : 0 < ‖(2 : ℤ_[p]) * A.det‖ := norm_pos_iff.2 h2d
  have h2pos : 0 < ‖(2 : ℤ_[p])‖ := norm_pos_iff.2 h2
  set S : Matrix (Fin n) (Fin n) ℤ_[p] := A.adjugate * (B - A) with hS
  have hSb : EntryNormLE S ε := by
    have := EntryNormLE.mul zero_le_one hε (entryNormLE_one A.adjugate) hBA
    simpa using this
  have hdv : ∀ i j, ∃ z : ℤ_[p], S i j = (2 * A.det) * z := fun i j =>
    padicInt_dvd_of_norm_le h2d ((hSb i j).trans hle)
  choose Y hY using hdv
  set Ym : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of Y with hYm
  have hSY : S = ((2 : ℤ_[p]) * A.det) • Ym := by
    ext i j; simp [hYm, hY i j]
  have hYb : EntryNormLE Ym (ε / ‖(2 : ℤ_[p]) * A.det‖) := by
    intro i j
    rw [le_div_iff₀ hpos]
    have := hSb i j
    rw [hY i j, norm_mul] at this
    simpa [hYm, mul_comm] using this
  have hAY : (2 : ℤ_[p]) • (A * Ym) = B - A := by
    have h1 : A * S = A.det • (B - A) := by
      rw [hS, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
    rw [hSY, Matrix.mul_smul] at h1
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at this ⊢
    have h3 : A.det * (2 * (A * Ym) i j) = A.det * (B i j - A i j) := by linear_combination this
    exact mul_left_cancel₀ hdet h3
  have hYA : (2 : ℤ_[p]) • (Ymᵀ * A) = B - A := by
    have := congrArg Matrix.transpose hAY
    rw [Matrix.transpose_smul, Matrix.transpose_mul, hA, Matrix.transpose_sub, hA, hB] at this
    exact this
  refine ⟨Ym, hYb, ?_⟩
  have hkey : (2 : ℤ_[p]) • ((1 + Ym)ᵀ * A * (1 + Ym) - B) = Ymᵀ * (B - A) := by
    have e : (1 + Ym)ᵀ * A * (1 + Ym) - B = Ymᵀ * (A * Ym) + A * Ym + Ymᵀ * A + A - B := by
      simp only [Matrix.transpose_add, Matrix.transpose_one, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_assoc]
      abel
    rw [e, smul_sub, smul_add, smul_add, smul_add, ← Matrix.mul_smul, hAY, hYA, two_smul, two_smul]
    abel
  have hb1 : EntryNormLE (Ymᵀ * (B - A)) (ε / ‖(2 : ℤ_[p]) * A.det‖ * ε) :=
    EntryNormLE.mul (div_nonneg hε hpos.le) hε hYb.transpose hBA
  intro i j
  have := hb1 i j
  rw [← hkey, Matrix.smul_apply, smul_eq_mul, norm_mul] at this
  rw [le_div_iff₀ h2pos]
  rw [mul_comm]; exact this

theorem norm_four_mul (a : ℤ_[p]) : ‖(4 : ℤ_[p]) * a‖ = ‖(2 : ℤ_[p])‖ * ‖(2 : ℤ_[p])‖ * ‖a‖ := by
  rw [show (4 : ℤ_[p]) = 2 * 2 by norm_num, norm_mul, norm_mul]

/-- Successive approximation: for every $m$ there is $T \equiv 1 \pmod p$ with $T^{t}FT - G$ having entries of
absolute value at most $\lvert 4\det F\rvert\rho^{2^m}$. -/
theorem exists_approx (F G : Matrix (Fin n) (Fin n) ℤ_[p]) (hF : Fᵀ = F) (hG : Gᵀ = G) (hdet : F.det ≠ 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (h0 : EntryNormLE (F - G) (‖(4 : ℤ_[p]) * F.det‖ * ρ)) (m : ℕ) :
    ∃ T : Matrix (Fin n) (Fin n) ℤ_[p], EntryNormLE (T - 1) ρ ∧
      EntryNormLE (Tᵀ * F * T - G) (‖(4 : ℤ_[p]) * F.det‖ * ρ ^ (2 ^ m)) := by
  induction m with
  | zero => exact ⟨1, fun i j => by simpa using hρ0, by simpa using h0⟩
  | succ m ih =>
    obtain ⟨T, hT1, hT2⟩ := ih
    set A : Matrix (Fin n) (Fin n) ℤ_[p] := Tᵀ * F * T with hAdef
    have hu : IsUnit T.det := by
      have := isUnit_det_one_add hρ hT1
      simpa using this
    have hTd : ‖T.det‖ = 1 := PadicInt.isUnit_iff.1 hu
    have hAdet : ‖A.det‖ = ‖F.det‖ := by
      rw [hAdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, norm_mul, norm_mul, hTd]; ring
    have hAne : A.det ≠ 0 := by
      intro h; rw [h, norm_zero] at hAdet; exact hdet (norm_eq_zero.1 hAdet.symm)
    have hAsym : Aᵀ = A := by
      rw [hAdef, Matrix.transpose_mul, Matrix.transpose_mul, hF, Matrix.transpose_transpose, Matrix.mul_assoc]
    set u : ℝ := ‖(2 : ℤ_[p])‖ with hu_def
    set d : ℝ := ‖F.det‖ with hd_def
    have hu0 : 0 < u := norm_pos_iff.2 two_ne_zero
    have hu1 : u ≤ 1 := PadicInt.norm_le_one _
    have hd0 : 0 < d := norm_pos_iff.2 hdet
    set N : ℕ := 2 ^ m with hN
    have hN0 : N ≠ 0 := by positivity
    have hρN1 : ρ ^ N ≤ 1 := pow_le_one₀ hρ0 hρ.le
    have hρN : ρ ^ N ≤ ρ := pow_le_of_le_one hρ0 hρ.le hN0
    have hρN0 : 0 ≤ ρ ^ N := pow_nonneg hρ0 N
    rw [norm_four_mul] at hT2 ⊢
    have hBA : EntryNormLE (G - A) (u * u * d * ρ ^ N) := by
      rw [← neg_sub]; exact hT2.neg
    have hnA : ‖(2 : ℤ_[p]) * A.det‖ = u * d := by rw [norm_mul, hAdet]
    have hle : u * u * d * ρ ^ N ≤ ‖(2 : ℤ_[p]) * A.det‖ := by
      rw [hnA]
      have : 0 ≤ u * d := by positivity
      nlinarith [mul_nonneg this hρN0]
    obtain ⟨Y, hY1, hY2⟩ := newton_step A G hAsym hG hAne _ (by positivity) hBA hle
    rw [hnA] at hY1 hY2
    have hYe : u * u * d * ρ ^ N / (u * d) = u * ρ ^ N := by field_simp
    rw [hYe] at hY1
    have hY2e : u * ρ ^ N * (u * u * d * ρ ^ N) / u = u * u * d * ρ ^ (2 ^ (m + 1)) := by
      rw [pow_succ, pow_mul, sq]; field_simp; ring
    rw [hYe, hY2e] at hY2
    refine ⟨T * (1 + Y), ?_, ?_⟩
    · have e : T * (1 + Y) - 1 = (T - 1) + T * Y := by rw [mul_add, mul_one]; abel
      rw [e]
      refine hT1.add ?_
      have := EntryNormLE.mul zero_le_one (by positivity) (entryNormLE_one T) hY1
      rw [one_mul] at this
      exact this.mono (by nlinarith)
    · have e : (T * (1 + Y))ᵀ * F * (T * (1 + Y)) = (1 + Y)ᵀ * A * (1 + Y) := by
        simp only [hAdef, Matrix.transpose_mul, Matrix.mul_assoc]
      rw [e]
      exact hY2

open Filter Topology in
/-- **Cassels, Ch. 8, Lemma 5.1** (Hensel-type successive approximation; checked against the printed page, p. 123, on
2026-10-27: the same statement, see the module docstring): let $F, G$ be symmetric
$n \times n$ matrices over $\mathbb Z_p$ with $\det F \ne 0$, and suppose that every entry of $F - G$ has
$p$-adic absolute value at most some $\varepsilon < \lvert 4\det F\rvert_p$ (that is, $G \equiv F$ modulo a power of
$p$ larger than $p^{\,2v_p(2) + v_p(\det F)}$; see `exists_equiv_of_dvd_pow`). Then there is a matrix
$T \in \mathrm{GL}_n(\mathbb Z_p)$, congruent to the identity matrix modulo $p$ (every entry of $T - 1$ has absolute
value $< 1$), such that $T^{t}FT = G$; that is, the quadratic forms with matrices $F$ and $G$ are equivalent over
$\mathbb Z_p$. -/
@[kb "cassels1978" "Ch. 8, Lemma 5.1, p. 123"]
theorem exists_equiv_of_congruent (F G : Matrix (Fin n) (Fin n) ℤ_[p]) (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hdet : F.det ≠ 0)
    (hcong : ∃ ε : ℝ, ε < ‖(4 : ℤ_[p]) * F.det‖ ∧ ∀ i j, ‖F i j - G i j‖ ≤ ε) :
    ∃ T : GL (Fin n) ℤ_[p], (∀ i j, ‖T.val i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j‖ < 1) ∧
      (T.val)ᵀ * F * T.val = G := by
  obtain ⟨ε, hεc, hε⟩ := hcong
  have hc : 0 < ‖(4 : ℤ_[p]) * F.det‖ := norm_pos_iff.2 (mul_ne_zero (by norm_num) hdet)
  set c := ‖(4 : ℤ_[p]) * F.det‖ with hc_def
  set ρ : ℝ := max ε 0 / c with hρ_def
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hc).2 (max_lt hεc hc)
  have h0 : EntryNormLE (F - G) (c * ρ) := by
    intro i j
    rw [hρ_def, mul_div_cancel₀ _ hc.ne', Matrix.sub_apply]
    exact (hε i j).trans (le_max_left _ _)
  choose T hT1 hT2 using exists_approx F G hF hG hdet ρ hρ0 hρ1 h0
  have : FirstCountableTopology (Matrix (Fin n) (Fin n) ℤ_[p]) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℤ_[p]))
  have : CompactSpace (Matrix (Fin n) (Fin n) ℤ_[p]) :=
    inferInstanceAs (CompactSpace (Fin n → Fin n → ℤ_[p]))
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq T
  have hf : Continuous (fun M : Matrix (Fin n) (Fin n) ℤ_[p] => Mᵀ * F * M - G) :=
    ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).sub
      continuous_const
  have hzero : Tendsto (fun k => (T (φ k))ᵀ * F * T (φ k) - G) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine squeeze_zero_norm (a := fun k => c * ρ ^ k) (fun k => ?_) ?_
    · refine (hT2 (φ k) i j).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      refine pow_le_pow_of_le_one hρ0 hρ1.le ?_
      exact (hφ.id_le k).trans (Nat.lt_two_pow_self).le
    · simpa using (tendsto_const_nhds (x := c)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1)
  have hfa : aᵀ * F * a - G = 0 :=
    tendsto_nhds_unique ((hf.tendsto a).comp hlim) hzero
  have hbd : EntryNormLE (a - 1) ρ := by
    intro i j
    have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℤ_[p] => ‖(M - 1) i j‖) :=
      continuous_norm.comp (Continuous.matrix_elem (continuous_id.sub continuous_const) i j)
    exact le_of_tendsto' ((hcont.tendsto a).comp hlim) (fun k => hT1 (φ k) i j)
  have hunit : IsUnit a.det := by
    have := isUnit_det_one_add hρ1 hbd
    simpa using this
  have hU : IsUnit a := (Matrix.isUnit_iff_isUnit_det a).2 hunit
  refine ⟨hU.unit, fun i j => (hbd i j).trans_lt hρ1, ?_⟩
  rw [IsUnit.unit_spec]
  exact sub_eq_zero.1 hfa

/-- **Cassels, Ch. 8, Lemma 5.1**, divisibility form: if $F, G$ are symmetric over $\mathbb Z_p$ with
$\det F \ne 0$ and $G \equiv F \pmod{p^k}$ entrywise, where $k$ exceeds the $p$-adic valuation of $4\det F$ (that is,
$k > 2v_p(2) + v_p(\det F)$; for odd $p$ this reads $k > v_p(\det F)$), then $T^{t}FT = G$ for some
$T \in \mathrm{GL}_n(\mathbb Z_p)$ with $T \equiv 1 \pmod p$. -/
@[kb "cassels1978" "Ch. 8, Lemma 5.1, p. 123"]
theorem exists_equiv_of_dvd_pow (F G : Matrix (Fin n) (Fin n) ℤ_[p]) (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hdet : F.det ≠ 0) (k : ℕ) (hk : ((4 : ℤ_[p]) * F.det).valuation < k)
    (hdvd : ∀ i j, (p : ℤ_[p]) ^ k ∣ F i j - G i j) :
    ∃ T : GL (Fin n) ℤ_[p], (∀ i j, ‖T.val i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j‖ < 1) ∧
      (T.val)ᵀ * F * T.val = G := by
  have h4 : (4 : ℤ_[p]) * F.det ≠ 0 := mul_ne_zero (by norm_num) hdet
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  refine exists_equiv_of_congruent F G hF hG hdet ⟨(p : ℝ) ^ (-(k : ℤ)), ?_, fun i j => ?_⟩
  · rw [PadicInt.norm_eq_zpow_neg_valuation h4]
    refine zpow_lt_zpow_right₀ hp1 ?_
    have : (((4 : ℤ_[p]) * F.det).valuation : ℤ) < k := by exact_mod_cast hk
    linarith
  · exact (PadicInt.norm_le_pow_iff_mem_span_pow _ k).2 (Ideal.mem_span_singleton.2 (hdvd i j))

end QuadFormsKB.Cassels
