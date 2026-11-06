/-
# Cassels, Chapter 12, Notes: the best Hermite constant is attained at an extreme form

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, Notes, p. 281: "To obtain the best possible value of $\gamma_n$
one need consider only extreme forms." This file **proves** the named statement `ExtremeFormsSuffice n` of
`Ch12/NotesVoronoi.lean` for every $n \ge 1$ (`extremeFormsSuffice_holds`), with the corrected definition of extreme
forms (`IsExtreme`: the determinant is a local *minimum* among forms of minimum $1$; the book's "local maximum" is an
erratum, see the docstring of `IsExtreme` and `exists_det_gt_of_two_le`).

**Proof** (Mahler's compactness argument, made explicit with Minkowski reduction):
* the Hermite quotient $\min f / d(f)^{1/n}$ (`hermiteQuotient`) is invariant under integral unimodular substitution
  and under scaling (`hermiteQuotient_act`, `hermiteQuotient_smul`), and bounded by $n$ (Theorem 2.1,
  `hermiteConstantBound_n`), so its supremum $s$ over strictly positive definite forms exists;
* every strictly positive definite form is equivalent to a scaled Minkowski-reduced form $G$ with $g_{00} = \min g = 1$
  (`exists_normal`); for such $G$, $\det G = q^{-n}$ where $q$ is the quotient, $g_{jj} \ge 1$, and
  $g_{jj} \le \prod_i g_{ii} \le (9/4)^{n^2}\prod_i M_i \le (9/4)^{n^2}n^n\det G$ (Theorem 3.1 (ii) and Theorem 2.2), and
  $|g_{ij}| \le \tfrac12 g_{ii}$ (Lemma 1.1);
* so a maximizing sequence of normalized forms lies in a compact box of matrices; a convergent subsequence has a limit
  $H$ that is positive semidefinite with $\det H = s^{-n} > 0$, hence strictly positive definite, with
  $h(\vec m) \ge 1$ for $\vec m \ne 0$ and $h_{00} = 1$; its quotient is $s$, the maximum; and a form of minimum $1$
  maximizing the quotient has the least determinant among forms of minimum $1$, so it is extreme.

For $n = 0$ the statement `ExtremeFormsSuffice 0` is false (there is no nonzero integral vector, so no form has
minimum $1$); Cassels' $n$ is at least $1$.
-/
import QuadFormsKB.Literature.Cassels.Ch12.NotesVoronoi
import QuadFormsKB.Literature.Cassels.Ch12.Sec2Minima
import QuadFormsKB.Literature.Cassels.Ch12.Sec3

open Matrix Filter Topology

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- Helper: the set of values $f(\vec m)$, $\vec m \in \mathbb Z^n \setminus 0$. -/
abbrev valSet (F : Matrix (Fin n) (Fin n) ℝ) : Set ℝ := (fun m : Fin n → ℤ => val F (cast m)) '' {m | m ≠ 0}

/-- Helper: an integral unimodular substitution does not change the set of values at nonzero integral vectors. -/
theorem valSet_act (F : Matrix (Fin n) (Fin n) ℝ) (T : GL (Fin n) ℤ) : valSet (act T.val F) = valSet F := by
  ext v
  simp only [valSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨T.val *ᵥ m, fun h => hm ?_, by rw [val_act_cast]⟩
    have : T⁻¹.val *ᵥ (T.val *ᵥ m) = m := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← this, h, Matrix.mulVec_zero]
  · rintro ⟨m, hm, rfl⟩
    refine ⟨T⁻¹.val *ᵥ m, fun h => hm ?_, ?_⟩
    · have : T.val *ᵥ (T⁻¹.val *ᵥ m) = m := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← this, h, Matrix.mulVec_zero]
    · rw [val_act_cast, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]

/-- The Hermite quotient is invariant under integral unimodular substitution. -/
theorem hermiteQuotient_act (F : Matrix (Fin n) (Fin n) ℝ) (T : GL (Fin n) ℤ) :
    hermiteQuotient (act T.val F) = hermiteQuotient F := by
  unfold hermiteQuotient
  rw [show ((fun m : Fin n → ℤ => val (act T.val F) (cast m)) '' {m | m ≠ 0}) = valSet (act T.val F) from rfl,
    valSet_act, det_act]

/-- Helper: scaling a form scales its values. -/
theorem valSet_smul (F : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : valSet (c • F) = (fun v => c * v) '' valSet F := by
  ext v
  simp only [valSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨_, ⟨m, hm, rfl⟩, by simp [val, Matrix.smul_mulVec, dotProduct_smul]⟩
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, by simp [val, Matrix.smul_mulVec, dotProduct_smul]⟩

/-- Helper: for a strictly positive definite form and $n \ge 1$, the set of values at nonzero integral vectors is
nonempty and bounded below by $0$. -/
theorem valSet_nonempty (F : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n) : (valSet F).Nonempty :=
  ⟨_, Pi.single ⟨0, hn⟩ 1, fun h => by simpa using congrFun h ⟨0, hn⟩, rfl⟩

theorem valSet_bddBelow {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) : BddBelow (valSet F) :=
  ⟨0, by rintro _ ⟨m, -, rfl⟩; exact ((posSemidef_iff F).1 hF.posSemidef).2 (cast m)⟩

/-- The Hermite quotient is invariant under scaling by $c > 0$ ($n \ge 1$). -/
theorem hermiteQuotient_smul {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) (hn : 0 < n) {c : ℝ} (hc : 0 < c) :
    hermiteQuotient (c • F) = hermiteQuotient F := by
  unfold hermiteQuotient
  rw [show ((fun m : Fin n → ℤ => val (c • F) (cast m)) '' {m | m ≠ 0}) = valSet (c • F) from rfl, valSet_smul,
    Matrix.det_smul, Fintype.card_fin]
  have hmono : Monotone fun v : ℝ => c * v := fun a b h => mul_le_mul_of_nonneg_left h hc.le
  rw [← hmono.map_csInf_of_continuousAt (by fun_prop : Continuous fun v : ℝ => c * v).continuousAt
    (valSet_nonempty F hn) (valSet_bddBelow hF)]
  have hd : 0 < F.det := hF.det_pos
  rw [Real.mul_rpow (by positivity) hd.le, ← Real.rpow_natCast, ← Real.rpow_mul hc.le,
    mul_one_div_cancel (by exact_mod_cast hn.ne'), Real.rpow_one]
  field_simp

/-- Helper: $f(c\vec x)$ for the scaled matrix: $(cF)(\vec x) = c\,f(\vec x)$. -/
theorem val_smul_matrix (F : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) : val (c • F) x = c * val F x := by
  simp [val, Matrix.smul_mulVec, dotProduct_smul]

/-- Helper: for a strictly positive definite $G$ whose values at nonzero integral vectors have greatest lower bound
$1$, the Hermite quotient is $1 / (\det G)^{1/n}$. -/
theorem hermiteQuotient_of_isGLB {G : Matrix (Fin n) (Fin n) ℝ} (hn : 0 < n) (hG : IsGLB (valSet G) 1) :
    hermiteQuotient G = 1 / G.det ^ ((1 : ℝ) / n) := by
  unfold hermiteQuotient
  rw [show ((fun m : Fin n → ℤ => val G (cast m)) '' {m | m ≠ 0}) = valSet G from rfl,
    hG.csInf_eq (valSet_nonempty G hn)]

/-- Helper: $(x^{1/n})^n = x$ for $x \ge 0$, $n \ge 1$. -/
theorem rpow_one_div_pow {x : ℝ} (hx : 0 ≤ x) (hn : 0 < n) : (x ^ ((1 : ℝ) / n)) ^ n = x := by
  rw [one_div]; exact Real.rpow_inv_natCast_pow hx hn.ne'

/-- **Normal form for the Hermite quotient**: every strictly positive definite form $F$ in $n \ge 1$ variables has
the same Hermite quotient as some Minkowski-reduced $G$ (a positive multiple of a form integrally equivalent to $F$)
with $g_{00} = 1$ and $g(\vec m) \ge 1$ for all nonzero integral $\vec m$. -/
theorem exists_normal (hn : 0 < n) {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) :
    ∃ G : Matrix (Fin n) (Fin n) ℝ, IsMinkowskiReduced G ∧ hermiteQuotient G = hermiteQuotient F ∧
      G ⟨0, hn⟩ ⟨0, hn⟩ = 1 ∧ ∀ m : Fin n → ℤ, m ≠ 0 → 1 ≤ val G (cast m) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨T, hR⟩ := exists_isMinkowskiReduced hF
  set R := act T.val F with hRdef
  have hRpd : R.PosDef := hR.1
  set a := R 0 0 with ha
  have hmin : ∀ m : Fin (k + 1) → ℤ, m ≠ 0 → a ≤ val R (cast m) := by
    intro m hm
    have h1 := hR.diag_le_succMin 0
    simp only [Fin.val_zero, pow_zero, one_mul] at h1
    exact h1.trans ((succMin_zero_spec hRpd).2 m hm)
  have hapos : 0 < a := lt_of_lt_of_le (succMin_pos hRpd 0) (hR.succMin_le_diag 0)
  refine ⟨a⁻¹ • R, ⟨hRpd.smul (inv_pos.2 hapos), fun j e he => ?_⟩, ?_, ?_, fun m hm => ?_⟩
  · rw [val_smul_matrix, Matrix.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hR.2 j e he) (inv_pos.2 hapos).le
  · rw [hermiteQuotient_smul hRpd (Nat.succ_pos k) (inv_pos.2 hapos), hRdef, hermiteQuotient_act]
  · show (a⁻¹ • R) 0 0 = 1
    simp [← ha, hapos.ne']
  · rw [val_smul_matrix, ← div_eq_inv_mul, le_div_iff₀ hapos, one_mul]
    exact hmin m hm

/-- Helper: a normalized form ($g_{00} = 1$, values $\ge 1$) has greatest lower bound $1$ of its values. -/
theorem isGLB_of_normal (hn : 0 < n) {G : Matrix (Fin n) (Fin n) ℝ} (h0 : G ⟨0, hn⟩ ⟨0, hn⟩ = 1)
    (h1 : ∀ m : Fin n → ℤ, m ≠ 0 → 1 ≤ val G (cast m)) : IsGLB (valSet G) 1 := by
  refine ⟨by rintro _ ⟨m, hm, rfl⟩; exact h1 m hm, fun b hb => ?_⟩
  have := hb ⟨Pi.single ⟨0, hn⟩ 1, fun h => by simpa using congrFun h ⟨0, hn⟩, rfl⟩
  simp only at this
  rwa [cast_single, val_single, h0] at this

/-- **Bounded entries** (Cassels, Ch. 12, Thm. 2.2, Thm. 3.1 (ii) and Lemma 1.1): for a Minkowski-reduced $G$ in
$n \ge 1$ variables with $g_{00} = 1$, every entry satisfies $|g_{ij}| \le (9/4)^{n^2}n^n\det G$. -/
theorem abs_entry_le_of_normal (hn : 0 < n) {G : Matrix (Fin n) (Fin n) ℝ} (hG : IsMinkowskiReduced G)
    (h0 : G ⟨0, hn⟩ ⟨0, hn⟩ = 1) (i j : Fin n) :
    |G i j| ≤ (9 / 4 : ℝ) ^ (n * n) * (n : ℝ) ^ n * G.det := by
  have hpd := hG.1
  have hge : ∀ i, 1 ≤ G i i := fun i => h0 ▸ hG.diag_mono (Fin.mk_le_mk.2 (Nat.zero_le _) |>.trans le_rfl)
  -- the diagonal bound
  have hprod : ∏ i, G i i ≤ (9 / 4 : ℝ) ^ (n * n) * (n : ℝ) ^ n * G.det := by
    calc ∏ i, G i i ≤ ∏ i : Fin n, ((9 / 4 : ℝ) ^ n * succMin G i) := by
          refine Finset.prod_le_prod₀ (fun i _ => (zero_le_one.trans (hge i))) fun i _ => ?_
          refine (hG.diag_le_succMin i).trans (mul_le_mul_of_nonneg_right ?_ (succMin_pos hpd i).le)
          exact pow_le_pow_right₀ (by norm_num) i.isLt.le
      _ = ((9 / 4 : ℝ) ^ (n * n)) * ∏ i, succMin G i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      _ ≤ (9 / 4 : ℝ) ^ (n * n) * ((n : ℝ) ^ n * G.det) :=
          mul_le_mul_of_nonneg_left (prod_succMin_le hpd (hermiteConstantBound_n hn)) (by positivity)
      _ = _ := by ring
  have hdiag : ∀ k, G k k ≤ (9 / 4 : ℝ) ^ (n * n) * (n : ℝ) ^ n * G.det := by
    intro k
    refine le_trans ?_ hprod
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    have h1 : (1 : ℝ) ≤ ∏ i ∈ Finset.univ.erase k, G i i := by
      calc (1 : ℝ) = ∏ i ∈ Finset.univ.erase k, (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => hge i
    nlinarith [hge k]
  have hs : G.IsSymm := ((posDef_iff G).1 hpd).1
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := hG.abs_two_mul_le hij
    rw [abs_mul, abs_two] at this
    linarith [hdiag i, abs_nonneg (G i j), hge i]
  · rw [abs_of_pos (zero_lt_one.trans_le (hge i))]; exact hdiag i
  · have := hG.abs_two_mul_le hij
    rw [abs_mul, abs_two] at this
    have hji : G i j = G j i := by simpa using congrFun (congrFun hs j) i
    rw [hji]
    linarith [hdiag j, abs_nonneg (G j i), hge j]

/-- Helper: the Hermite quotient of a strictly positive definite form in $n \ge 1$ variables is at most $n$
(Theorem 2.1 with $\gamma_n = n$, `hermiteConstantBound_n`). -/
theorem hermiteQuotient_le_n (hn : 0 < n) {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) :
    hermiteQuotient F ≤ n := by
  obtain ⟨m, hm, hle⟩ := hermiteConstantBound_n hn F hF
  have hp : 0 < F.det ^ ((1 : ℝ) / n) := Real.rpow_pos_of_pos hF.det_pos _
  unfold hermiteQuotient
  rw [div_le_iff₀ hp]
  exact (csInf_le (valSet_bddBelow hF) ⟨m, hm, rfl⟩).trans hle

/-- Helper: the data of a normalized form: Minkowski-reduced, $g_{00} = 1$, values $\ge 1$; then its Hermite quotient
is positive and $\det G = q^{-n}$. -/
theorem det_of_normal (hn : 0 < n) {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (hglb : IsGLB (valSet G) 1) :
    0 < hermiteQuotient G ∧ G.det = (1 / hermiteQuotient G) ^ n := by
  rw [hermiteQuotient_of_isGLB hn hglb]
  have hp : 0 < G.det ^ ((1 : ℝ) / n) := Real.rpow_pos_of_pos hG.det_pos _
  refine ⟨by positivity, ?_⟩
  rw [one_div_one_div, rpow_one_div_pow hG.det_pos.le hn]

/-- **Cassels, Ch. 12, Notes, p. 281: "to obtain the best possible value of $\gamma_n$ one need consider only extreme
forms"** — proved for every $n \ge 1$: some extreme form (`IsExtreme`, corrected definition: the determinant is a local
minimum among forms of minimum $1$) has the largest Hermite quotient $\min f / d(f)^{1/n}$ among all strictly positive
definite real forms $f$ in $n$ variables. This discharges the named statement `ExtremeFormsSuffice n`. Argument:
`hn : 0 < n`. *Proof:* Mahler's compactness argument via Minkowski reduction (see the module docstring). -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (best γ_n: only extreme forms need be considered)"]
theorem extremeFormsSuffice_holds (hn : 0 < n) : ExtremeFormsSuffice n := by
  classical
  set S : Set ℝ := hermiteQuotient '' {F : Matrix (Fin n) (Fin n) ℝ | F.PosDef} with hSdef
  have hSne : S.Nonempty := ⟨_, 1, Matrix.PosDef.one, rfl⟩
  have hSbdd : BddAbove S := ⟨n, by rintro _ ⟨F, hF, rfl⟩; exact hermiteQuotient_le_n hn hF⟩
  obtain ⟨u, hmono, hlim, hmem⟩ := exists_seq_tendsto_sSup hSne hSbdd
  set s := sSup S with hs
  -- normalized forms along the sequence
  have hnorm : ∀ k, ∃ G : Matrix (Fin n) (Fin n) ℝ, IsMinkowskiReduced G ∧ hermiteQuotient G = u k ∧
      G ⟨0, hn⟩ ⟨0, hn⟩ = 1 ∧ ∀ m : Fin n → ℤ, m ≠ 0 → 1 ≤ val G (cast m) := by
    intro k
    obtain ⟨F, hF, hFk⟩ := hmem k
    obtain ⟨G, hG, hq, h0, h1⟩ := exists_normal hn hF
    exact ⟨G, hG, hq.trans hFk, h0, h1⟩
  choose G hGred hGq hG0 hG1 using hnorm
  have hGglb : ∀ k, IsGLB (valSet (G k)) 1 := fun k => isGLB_of_normal hn (hG0 k) (hG1 k)
  have hdetG : ∀ k, (G k).det = (1 / u k) ^ n := fun k => by
    rw [← hGq k]; exact (det_of_normal hn (hGred k).1 (hGglb k)).2
  have hu0 : 0 < u 0 := by rw [← hGq 0]; exact (det_of_normal hn (hGred 0).1 (hGglb 0)).1
  have hupos : ∀ k, 0 < u k := fun k => hu0.trans_le (hmono (Nat.zero_le k))
  have hspos : 0 < s := hu0.trans_le (le_csSup hSbdd (hmem 0))
  -- a uniform bound on the entries
  set B : ℝ := (9 / 4 : ℝ) ^ (n * n) * (n : ℝ) ^ n * (1 / u 0) ^ n with hB
  have hbound : ∀ k i j, |G k i j| ≤ B := by
    intro k i j
    refine (abs_entry_le_of_normal hn (hGred k) (hG0 k) i j).trans ?_
    rw [hdetG k, hB]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (one_div_pos.2 (hupos k)).le ?_ n) (by positivity)
    exact one_div_le_one_div_of_le hu0 (hmono (Nat.zero_le k))
  -- compactness
  set K : Set (Fin n → Fin n → ℝ) :=
    Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Set.Icc (-B) B with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hGK : ∀ k, (fun i j => G k i j) ∈ K := fun k =>
    Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => abs_le.1 (hbound k i j)
  obtain ⟨H₀, -, φ, hφ, hHlim₀⟩ := hKc.tendsto_subseq hGK
  set H : Matrix (Fin n) (Fin n) ℝ := Matrix.of H₀ with hHdef
  have hHlim : Tendsto (fun k => G (φ k)) atTop (𝓝 H) := hHlim₀
  -- limits of entries, values and determinants
  have hentry : ∀ i j, Tendsto (fun k => G (φ k) i j) atTop (𝓝 (H i j)) := fun i j =>
    ((continuous_id.matrix_elem i j).tendsto H).comp hHlim
  have hvalc : ∀ x : Fin n → ℝ, Continuous fun M : Matrix (Fin n) (Fin n) ℝ => val M x := fun x => by
    unfold val; fun_prop
  have hval : ∀ x : Fin n → ℝ, Tendsto (fun k => val (G (φ k)) x) atTop (𝓝 (val H x)) := fun x =>
    (hvalc x).continuousAt.tendsto.comp hHlim
  have hdet : Tendsto (fun k => (G (φ k)).det) atTop (𝓝 H.det) :=
    (continuous_id.matrix_det).continuousAt.tendsto.comp hHlim
  have hdet' : Tendsto (fun k => (G (φ k)).det) atTop (𝓝 ((1 / s) ^ n)) := by
    simp only [hdetG]
    exact (((hlim.comp hφ.tendsto_atTop).inv₀ hspos.ne').pow n).congr' (Eventually.of_forall fun k => by
      simp [one_div]) |>.trans (by simp [one_div])
  have hHdet : H.det = (1 / s) ^ n := tendsto_nhds_unique hdet hdet'
  -- properties of the limit
  have hH1 : ∀ m : Fin n → ℤ, m ≠ 0 → 1 ≤ val H (cast m) := fun m hm =>
    ge_of_tendsto' (hval (cast m)) fun k => hG1 (φ k) m hm
  have hH0 : H ⟨0, hn⟩ ⟨0, hn⟩ = 1 :=
    tendsto_nhds_unique (hentry _ _) (by simp only [hG0]; exact tendsto_const_nhds)
  have hHsymm : H.IsSymm := by
    ext i j
    refine tendsto_nhds_unique (hentry j i) ?_
    refine (hentry i j).congr fun k => ?_
    have := ((posDef_iff _).1 (hGred (φ k)).1).1
    simpa using (congrFun (congrFun this i) j).symm
  have hHpsd : H.PosSemidef := (posSemidef_iff H).2 ⟨hHsymm, fun x =>
    ge_of_tendsto' (hval x) fun k => ((posSemidef_iff _).1 (hGred (φ k)).1.posSemidef).2 x⟩
  have hHpd : H.PosDef := hHpsd.posDef_iff_det_ne_zero.2 (by rw [hHdet]; positivity)
  have hHglb : IsGLB (valSet H) 1 := isGLB_of_normal hn hH0 hH1
  have hHq : hermiteQuotient H = s := by
    rw [hermiteQuotient_of_isGLB hn hHglb, hHdet,
      show ((1 / s) ^ n) ^ ((1 : ℝ) / n) = 1 / s by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_one_div_cancel (by exact_mod_cast hn.ne'),
          Real.rpow_one]]
    field_simp
  have hmax : ∀ F : Matrix (Fin n) (Fin n) ℝ, F.PosDef → hermiteQuotient F ≤ hermiteQuotient H := fun F hF =>
    hHq ▸ le_csSup hSbdd ⟨F, hF, rfl⟩
  refine ⟨⟨H, ⟨hHpd, hHglb, Set.univ, Filter.univ_mem, fun G' _ hG' hG'glb => ?_⟩, hmax⟩⟩
  have hle := hmax G' hG'
  rw [hermiteQuotient_of_isGLB hn hG'glb, hermiteQuotient_of_isGLB hn hHglb] at hle
  have hp1 : 0 < G'.det ^ ((1 : ℝ) / n) := Real.rpow_pos_of_pos hG'.det_pos _
  have hp2 : 0 < H.det ^ ((1 : ℝ) / n) := Real.rpow_pos_of_pos hHpd.det_pos _
  rw [div_le_div_iff₀ hp1 hp2, one_mul, one_mul] at hle
  have := pow_le_pow_left₀ hp2.le hle n
  rwa [rpow_one_div_pow hHpd.det_pos.le hn, rpow_one_div_pow hG'.det_pos.le hn] at this

/-! ### The printed definition (erratum) -/

/-- **The printed definition of extreme forms is never satisfied for $n \ge 2$** (Cassels, Ch. 12, Notes, p. 281,
erratum): for every strictly positive definite $H$ of minimum $1$ in $n \ge 2$ variables and every neighbourhood $U$ of
$H$, some strictly positive definite $G \in U$ of minimum $1$ has $\det G > \det H$. So "$d(h)$ is a local maximum
among forms of minimum $1$", as printed, holds for no form, and the corrected definition `IsExtreme` (local minimum)
is the one meant. *Proof:* take a minimal vector $\vec m_0$ ($h(\vec m_0) = 1$), a nonzero real $\vec v$ orthogonal
to it, and $G = H + \varepsilon\,\vec v\vec v^{\mathsf T}$ with small $\varepsilon > 0$: $g \ge h$, $g(\vec m_0) = 1$,
and $\det G = \det H\,(1 + \varepsilon\,\vec v^{\mathsf T}H^{-1}\vec v) > \det H$ (matrix determinant lemma).
Arguments: `hn : 2 ≤ n`, `hH` positive definiteness, `hglb` minimum $1$, `hU` the neighbourhood. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (extreme forms; the printed 'local maximum' is never attained)"]
theorem exists_det_gt_of_two_le (hn : 2 ≤ n) {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    (hglb : IsGLB (valSet H) 1) {U : Set (Matrix (Fin n) (Fin n) ℝ)} (hU : U ∈ 𝓝 H) :
    ∃ G ∈ U, G.PosDef ∧ IsGLB (valSet G) 1 ∧ H.det < G.det := by
  classical
  -- a minimal vector
  obtain ⟨m₀, hm₀, hval₀⟩ : ∃ m₀ : Fin n → ℤ, m₀ ≠ 0 ∧ val H (cast m₀) = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨⟨m, hm, hmv⟩, hall⟩ := succMin_zero_spec hH
    refine ⟨m, hm, le_antisymm ?_ (hglb.1 ⟨m, hm, rfl⟩)⟩
    rw [hmv]
    exact hglb.2 (by rintro _ ⟨m', hm', rfl⟩; exact hall m' hm')
  set w : Fin n → ℝ := cast m₀ with hw
  have hw0 : w ≠ 0 := by
    intro h; apply hm₀; funext i; have := congrFun h i; simpa [hw, cast] using this
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h; push Not at h; exact hw0 (funext h)
  obtain ⟨j, hij⟩ : ∃ j : Fin n, j ≠ i := by
    by_cases h : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
  set v : Fin n → ℝ := Pi.single i (w j) - Pi.single j (w i) with hv
  have hvw : v ⬝ᵥ w = 0 := by
    simp [hv, sub_dotProduct, single_dotProduct]; ring
  have hv0 : v ≠ 0 := by
    intro h; have := congrFun h j; simp [hv, hij, hi] at this
  -- the perturbation
  set E : Matrix (Fin n) (Fin n) ℝ := vecMulVec v v with hE
  have hvalE : ∀ x, val E x = (v ⬝ᵥ x) ^ 2 := fun x => by
    simp only [val, hE, vecMulVec_mulVec, dotProduct_smul]
    rw [dotProduct_comm x v, op_smul_eq_mul]; ring
  have hEs : E.IsSymm := by simp [hE, Matrix.IsSymm, transpose_vecMulVec]
  have hHs : H.IsSymm := ((posDef_iff H).1 hH).1
  have hvalG : ∀ (ε : ℝ) x, val (H + ε • E) x = val H x + ε * (v ⬝ᵥ x) ^ 2 := fun ε x => by
    rw [← hvalE, ← val_smul_matrix]; simp [val, add_mulVec, dotProduct_add]
  have hGpd : ∀ ε : ℝ, 0 ≤ ε → (H + ε • E).PosDef := fun ε hε => by
    rw [posDef_iff]
    refine ⟨hHs.add (hEs.smul ε), fun x hx => ?_⟩
    rw [hvalG]
    have := ((posDef_iff H).1 hH).2 x hx
    positivity
  have hGglb : ∀ ε : ℝ, 0 ≤ ε → IsGLB (valSet (H + ε • E)) 1 := fun ε hε => by
    refine ⟨by rintro _ ⟨m, hm, rfl⟩; show 1 ≤ val (H + ε • E) (cast m); rw [hvalG]; nlinarith [hglb.1 ⟨m, hm, rfl⟩, sq_nonneg (v ⬝ᵥ cast m)],
      fun b hb => ?_⟩
    have := hb ⟨m₀, hm₀, rfl⟩
    simp only [hvalG, ← hw, hvw, hval₀] at this
    simpa using this
  have hGdet : ∀ ε : ℝ, 0 < ε → H.det < (H + ε • E).det := fun ε hε => by
    have hu : IsUnit H.det := hH.det_pos.ne'.isUnit
    have hEq : ε • E = replicateCol Unit (ε • v) * replicateRow Unit v := by
      rw [hE, ← vecMulVec_eq (ι := Unit), smul_vecMulVec]
    rw [hEq, det_add_replicateCol_mul_replicateRow (ι := Unit) hu,
      Matrix.det_unique (1 + replicateRow Unit v * H⁻¹ * replicateCol Unit (ε • v))]
    have hq : 0 < v ⬝ᵥ (H⁻¹ *ᵥ v) := by
      have := ((posDef_iff _).1 hH.inv).2 v hv0
      simpa [val] using this
    have : ((1 : Matrix Unit Unit ℝ) + replicateRow Unit v * H⁻¹ * replicateCol Unit (ε • v)) default default =
        1 + ε * (v ⬝ᵥ (H⁻¹ *ᵥ v)) := by
      simp [Matrix.mul_apply, replicateRow, replicateCol, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul,
        mul_comm, mul_left_comm]
      have hsI : ∀ a b, H⁻¹ a b = H⁻¹ b a := fun a b => by
        have := ((posDef_iff _).1 hH.inv).1
        simpa using (congrFun (congrFun this b) a)
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [hsI x y]
    rw [this]
    have := hH.det_pos
    nlinarith [mul_pos hε hq]
  -- small ε
  have hcont : Tendsto (fun ε : ℝ => H + ε • E) (𝓝[>] 0) (𝓝 H) := by
    have : Continuous fun ε : ℝ => H + ε • E := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hεU, hε⟩ := ((hcont.eventually hU).and self_mem_nhdsWithin).exists
  exact ⟨_, hεU, hGpd ε (le_of_lt hε), hGglb ε (le_of_lt hε), hGdet ε hε⟩

end QuadFormsKB.Reduction
