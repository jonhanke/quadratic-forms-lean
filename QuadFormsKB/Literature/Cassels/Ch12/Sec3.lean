/-
# Cassels, Chapter 12, §3: reduced forms lie in a Siegel domain

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §3, pp. 263–266.

* Theorem 3.1 (`thm_3_1`): for a Minkowski-reduced form, written as $\sum_j h_j(x_j + c_{j,j+1}x_{j+1} + \cdots)^2$
  (`IsSqDecomp`), with successive minima $M_j$ (`succMin`), the ratios of any two of $h_j$, $f_{jj}$, $M_j$ are bounded
  by constants depending only on $n$.
* Lemma 1.3 (`exists_siegelDomain_of_isMinkowskiReduced`), stated in §1, p. 259, and proved at the end of §3 (12.p1):
  there are $\delta_n, \eta_n$ with every reduced form in $\mathcal S(\delta_n, \eta_n)$.

The list (i)–(v) of Theorem 3.1 is partly lost in the machine-read text (only (i) $h_j \le f_{jj}$ survives on p. 263);
(ii)–(v) are reconstructed from the proofs on pp. 264–265: (ii) $f_{jj} \le C_1(j)M_j$, (iii) $M_j \le C_2(n)h_j$,
(iv) $f_{jj} \le C_3(n)h_j$ ("follows immediately from (ii) and (iii)"), (v) $M_j \le f_{jj}$ ("trivial").
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec2Minima

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- Helper: the value of a positive definite form is nonnegative. -/
private theorem val_nonneg_of_posDef {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef) (x : Fin n → ℝ) :
    0 ≤ val F x :=
  ((posSemidef_iff F).1 hF.posSemidef).2 x

/-- Helper: the first `j+1` standard basis vectors are linearly independent. -/
private theorem single_li (j : Fin n) :
    LinearIndependent ℝ (fun k : Fin (j.val + 1) =>
      cast (Pi.single (Fin.castLE (Nat.succ_le_of_lt j.isLt) k) (1 : ℤ) : Fin n → ℤ)) := by
  have := (Pi.basisFun ℝ (Fin n)).linearIndependent.comp _ (Fin.castLE_injective (Nat.succ_le_of_lt j.isLt))
  convert this using 1
  ext k : 1
  rw [cast_single]
  simp

/-- Helper: `j+1` independent integral vectors of value `≤ M` give a span of dimension `≥ j+1`. -/
private theorem finrank_spanLE_ge {F : Matrix (Fin n) (Fin n) ℝ} {j : Fin n}
    (v : Fin (j.val + 1) → Fin n → ℤ) (hv : LinearIndependent ℝ fun k => cast (v k)) {M : ℝ}
    (hM : ∀ k, val F (cast (v k)) ≤ M) : j.val + 1 ≤ Module.finrank ℝ (spanLE F M) := by
  have h1 : Submodule.span ℝ (Set.range fun k => cast (v k)) ≤ spanLE F M := by
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨v k, hM k, rfl⟩
  have h2 := Submodule.finrank_mono h1
  rw [finrank_span_eq_card hv] at h2
  simpa using h2

/-- **Theorem 3.1, (v)** (Cassels, Ch. 12, p. 265, "trivial"): for a reduced form $M_j \le f_{jj}$
($e_0, \dots, e_j$ are $j+1$ independent vectors with $f(e_i) = f_{ii} \le f_{jj}$ by Lemma 1.1). -/
@[kb "cassels1978" "Ch. 12, §3, Thm. 3.1 (v), pp. 263, 265"]
theorem IsMinkowskiReduced.succMin_le_diag {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsMinkowskiReduced F)
    (j : Fin n) : succMin F j ≤ F j j := by
  classical
  have hmem : F j j ∈ {M : ℝ | j.val + 1 ≤ Module.finrank ℝ (spanLE F M)} := by
    apply finrank_spanLE_ge (fun k => Pi.single (Fin.castLE (Nat.succ_le_of_lt j.isLt) k) (1 : ℤ)) (single_li j)
    intro k
    rw [cast_single, val_single]
    exact hF.diag_mono (by rw [Fin.le_def]; simp; omega)
  have hbdd : BddBelow {M : ℝ | j.val + 1 ≤ Module.finrank ℝ (spanLE F M)} := by
    refine ⟨0, fun M hM => ?_⟩
    by_contra hlt
    push Not at hlt
    have : {m : Fin n → ℤ | val F (cast m) ≤ M} = ∅ :=
      Set.eq_empty_of_forall_notMem fun m hm =>
        absurd (val_nonneg_of_posDef hF.1 (cast m)) (not_le.2 (lt_of_le_of_lt hm hlt))
    have hb : spanLE F M = ⊥ := by rw [spanLE, this]; simp
    have hM' : j.val + 1 ≤ Module.finrank ℝ (spanLE F M) := hM
    rw [hb, finrank_bot] at hM'
    omega
  exact csInf_le hbdd hmem


/-- **Theorem 3.1, (ii)** (Cassels, Ch. 12, pp. 263–264): for a reduced form $f_{jj} \le C_1(j)M_j$ with
$C_1(j) = (9/4)^j$ (Cassels does not compute the constant). -/
@[kb "cassels1978" "Ch. 12, §3, Thm. 3.1 (ii), pp. 263–264"]
theorem IsMinkowskiReduced.diag_le_succMin {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsMinkowskiReduced F)
    (j : Fin n) : F j j ≤ (9 / 4 : ℝ) ^ j.val * succMin F j := by
  classical
  obtain ⟨m, hli, hm⟩ := exists_succMin_vectors hF.1
  have hle : j.val + 1 ≤ n := Nat.succ_le_of_lt j.isLt
  refine hF.diag_le_of_linearIndependent j (fun k => m (Fin.castLE hle k))
    (hli.comp _ (Fin.castLE_injective hle)) (fun k => ?_)
  rw [hm]
  exact succMin_mono hF.1 (by rw [Fin.le_def]; simp; omega)


/-- Helper: (iii) of Theorem 3.1 with the explicit constant $n^n(9/4)^{n^2}$. -/
private theorem succMin_le_const {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsMinkowskiReduced F)
    {h : Fin n → ℝ} {C : Matrix (Fin n) (Fin n) ℝ} (hd : IsSqDecomp F h C) (j : Fin n) :
    succMin F j ≤ ((n : ℝ) ^ n * (9 / 4 : ℝ) ^ (n * n)) * h j := by
  classical
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hh : ∀ i, 0 < h i := hd.pos hF.1
  set c : ℝ := (9 / 4 : ℝ) ^ n with hc
  have hc1 : 1 ≤ c := one_le_pow₀ (by norm_num)
  have hc0 : 0 < c := by linarith
  have hMi : ∀ i, h i / c ≤ succMin F i := by
    intro i
    have h1 : h i ≤ F i i := by
      rw [hd.diag_eq i]
      exact Finset.single_le_sum (f := fun k => h k * C k i ^ 2)
        (fun k _ => mul_nonneg (hh k).le (sq_nonneg _)) (Finset.mem_Iic.2 le_rfl) |>.trans_eq' (by
          simp [hd.2.1])
    have h2 := hF.diag_le_succMin i
    have h3 : (9 / 4 : ℝ) ^ i.val ≤ c := pow_le_pow_right₀ (by norm_num) i.isLt.le
    have hM0 := succMin_pos hF.1 i
    rw [div_le_iff₀ hc0]
    nlinarith
  have hprod := prod_succMin_le hF.1 (hermiteConstantBound_n hn)
  rw [hd.det_eq] at hprod
  rw [← Finset.mul_prod_erase Finset.univ (fun i => succMin F i) (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ j)] at hprod
  set P := ∏ i ∈ Finset.univ.erase j, h i with hP
  have hP0 : 0 < P := Finset.prod_pos fun i _ => hh i
  have hlow : P / c ^ (Finset.univ.erase j).card ≤ ∏ i ∈ Finset.univ.erase j, succMin F i := by
    rw [hP, ← Finset.prod_const, ← Finset.prod_div_distrib]
    gcongr
    · exact fun i _ => div_nonneg (hh i).le hc0.le
    · exact hMi _
  have hMj := succMin_pos hF.1 j
  have hcard : c ^ (Finset.univ.erase j).card ≤ c ^ n := by
    apply pow_le_pow_right₀ hc1
    rw [Finset.card_erase_of_mem (Finset.mem_univ j)]; simp
  have hck : 0 < c ^ (Finset.univ.erase j).card := pow_pos hc0 _
  have h4 : succMin F j * (P / c ^ (Finset.univ.erase j).card) ≤ (n : ℝ) ^ n * (h j * P) :=
    (mul_le_mul_of_nonneg_left hlow hMj.le).trans hprod
  rw [mul_div_assoc', div_le_iff₀ hck] at h4
  have h5 : succMin F j ≤ (n : ℝ) ^ n * h j * c ^ (Finset.univ.erase j).card := by
    refine le_of_mul_le_mul_right ?_ hP0
    nlinarith
  have hnn : 0 ≤ (n : ℝ) ^ n * h j := mul_nonneg (by positivity) (hh j).le
  calc succMin F j ≤ (n : ℝ) ^ n * h j * c ^ (Finset.univ.erase j).card := h5
    _ ≤ (n : ℝ) ^ n * h j * c ^ n := mul_le_mul_of_nonneg_left hcard hnn
    _ = ((n : ℝ) ^ n * (9 / 4 : ℝ) ^ (n * n)) * h j := by rw [hc, ← pow_mul]; ring

/-- **Theorem 3.1** (Cassels, Ch. 12, §3, pp. 263–265): there are constants $C_2(n), C_3(n)$ such that for every
Minkowski-reduced real form $f$ in $n$ variables, written as
$f = \sum_j h_j(x_j + c_{j,j+1}x_{j+1} + \cdots + c_{j,n-1}x_{n-1})^2$ ((3.1); `IsSqDecomp`), with successive minima
$M_0, \dots, M_{n-1}$, and every $j$:
(i) $h_j \le f_{jj}$; (ii) $f_{jj} \le C_1(j)M_j$ with $C_1(j) = (9/4)^j$; (iii) $M_j \le C_2(n)h_j$;
(iv) $f_{jj} \le C_3(n)h_j$; (v) $M_j \le f_{jj}$.
In particular the ratio of any two of $h_j, f_{jj}, M_j$ is bounded in terms of $n$ alone. *Proof of (iii)*
(Cassels'): $\prod_j h_j = D$ and $\prod_j M_j \le \gamma_n^nD$ (Theorem 2.2), while $M_i/h_i \ge 1/C_1(i)$ by (i) and
(ii). -/
@[kb "cassels1978" "Ch. 12, §3, Thm. 3.1, pp. 263–265"]
theorem thm_3_1 (n : ℕ) : ∃ C₂ C₃ : ℝ, ∀ F : Matrix (Fin n) (Fin n) ℝ, IsMinkowskiReduced F →
    ∀ (h : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ), IsSqDecomp F h C → ∀ j : Fin n,
      h j ≤ F j j ∧ F j j ≤ (9 / 4 : ℝ) ^ j.val * succMin F j ∧ succMin F j ≤ C₂ * h j ∧
        F j j ≤ C₃ * h j ∧ succMin F j ≤ F j j := by
  refine ⟨(n : ℝ) ^ n * (9 / 4 : ℝ) ^ (n * n), (9 / 4 : ℝ) ^ n * ((n : ℝ) ^ n * (9 / 4 : ℝ) ^ (n * n)),
    fun F hF h C hd j => ?_⟩
  have hh : ∀ i, 0 < h i := hd.pos hF.1
  have hi : h j ≤ F j j := by
    rw [hd.diag_eq j]
    refine (Finset.single_le_sum (f := fun k => h k * C k j ^ 2)
        (fun k _ => mul_nonneg (hh k).le (sq_nonneg _)) (Finset.mem_Iic.2 le_rfl)).trans_eq' ?_
    simp [hd.2.1]
  have hii := hF.diag_le_succMin j
  have hiii := succMin_le_const hF hd j
  have hv := hF.succMin_le_diag j
  refine ⟨hi, hii, hiii, ?_, hv⟩
  have hM0 := succMin_pos hF.1 j
  have h3 : (9 / 4 : ℝ) ^ j.val ≤ (9 / 4 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) j.isLt.le
  calc F j j ≤ (9 / 4 : ℝ) ^ j.val * succMin F j := hii
    _ ≤ (9 / 4 : ℝ) ^ n * succMin F j := mul_le_mul_of_nonneg_right h3 hM0.le
    _ ≤ (9 / 4 : ℝ) ^ n * (((n : ℝ) ^ n * (9 / 4 : ℝ) ^ (n * n)) * h j) :=
        mul_le_mul_of_nonneg_left hiii (by positivity)
    _ = _ := by ring

/-- Helper: the recursive bound $S_{i+1} = S_i + (K/2 + KS_i)^2$ for the sizes of the $c_{ij}$ in Lemma 1.3
(so that $|c_{ij}| \le K/2 + KS_i$). -/
private noncomputable def siegS (K : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => siegS K i + (K / 2 + K * siegS K i) ^ 2

/-- Helper: `siegS` is nonnegative for `K ≥ 0`. -/
private theorem siegS_nonneg {K : ℝ} (hK : 0 ≤ K) : ∀ i, 0 ≤ siegS K i
  | 0 => le_rfl
  | i + 1 => by
    have := siegS_nonneg hK i
    simp only [siegS]
    positivity

/-- Helper: `siegS` is monotone. -/
private theorem siegS_mono (K : ℝ) : Monotone (siegS K) :=
  monotone_nat_of_le_succ fun i => by
    simp only [siegS]
    exact le_add_of_nonneg_right (sq_nonneg _)

/-- Helper: `siegS` as a sum of the previous squared bounds. -/
private theorem siegS_eq_sum (K : ℝ) (i : ℕ) :
    siegS K i = ∑ l ∈ Finset.range i, (K / 2 + K * siegS K l) ^ 2 := by
  induction i with
  | zero => simp [siegS]
  | succ i ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- Helper: a sum over `Iio i` in `Fin n` as a sum over `range i`. -/
private theorem sum_Iio_fin (f : ℕ → ℝ) (i : Fin n) :
    ∑ k ∈ Finset.Iio i, f k.val = ∑ l ∈ Finset.range i.val, f l := by
  have h1 := Finset.sum_map (Finset.Iio i) Fin.valEmbedding f
  rw [Fin.map_valEmbedding_Iio, Nat.Iio_eq_range] at h1
  simpa using h1.symm

/-- **Lemma 1.3** (Cassels, Ch. 12, §1, p. 259; proved in §3, pp. 265–266): there are $\delta_n, \eta_n$, depending only
on $n$, such that every Minkowski-reduced real form in $n$ variables lies in the Siegel domain
$\mathcal S_n(\delta_n, \eta_n)$. *Proof* (Cassels'): $h_j \le f_{jj} \le f_{j+1,j+1} \le C_3h_{j+1}$, so
$\delta_n = C_3(n)$; and $|c_{ij}|$ is bounded by induction on $i$ from $f_{ij} = h_ic_{ij} + \sum_{k<i}h_kc_{ki}c_{kj}$
((3.5)–(3.6)), $|f_{ij}| \le \tfrac12 f_{ii}$ and $f_{ii} \le C_3h_i$. -/
@[kb "cassels1978" "Ch. 12, §1, Lemma 1.3, p. 259; proof in §3, pp. 265–266"]
theorem exists_siegelDomain_of_isMinkowskiReduced (n : ℕ) :
    ∃ δ η : ℝ, ∀ F : Matrix (Fin n) (Fin n) ℝ, IsMinkowskiReduced F → InSiegelDomain δ η F := by
  classical
  obtain ⟨C₂, C₃, hC⟩ := thm_3_1 n
  set K : ℝ := max C₃ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  refine ⟨K, K / 2 + K * siegS K n, fun F hF => ?_⟩
  obtain ⟨h, C, hd, hh⟩ := exists_isSqDecomp hF.1
  have hdiag : ∀ i, F i i ≤ K * h i := fun i =>
    (hC F hF h C hd i).2.2.2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hh i).le)
  have hhk : ∀ i k : Fin n, k ≤ i → h k ≤ K * h i := fun i k hki =>
    (hC F hF h C hd k).1.trans ((hF.diag_mono hki).trans (hdiag i))
  have key : ∀ m : ℕ, ∀ i : Fin n, i.val = m → ∀ j, i < j → |C i j| ≤ K / 2 + K * siegS K m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro i hi j hij
    have hoff := hd.offdiag_eq hij
    have hE : ∀ k : Fin n, k < i → ∀ j, k < j → |C k j| ≤ K / 2 + K * siegS K k.val :=
      fun k hk j hkj => ih k.val (hi ▸ hk) k rfl j hkj
    have hFij : |F i j| ≤ K * h i / 2 := by
      have h1 := hF.abs_two_mul_le hij
      rw [abs_mul, abs_two] at h1
      linarith [hdiag i]
    have hsum : |∑ k ∈ Finset.Iio i, h k * C k i * C k j| ≤
        ∑ k ∈ Finset.Iio i, K * h i * (K / 2 + K * siegS K k.val) ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
      have hki : k < i := Finset.mem_Iio.1 hk
      rw [abs_mul, abs_mul, abs_of_pos (hh k)]
      have e1 := hE k hki i hki
      have e2 := hE k hki j (hki.trans hij)
      have hE0 : 0 ≤ K / 2 + K * siegS K k.val := by
        have := siegS_nonneg hK0 k.val
        positivity
      calc h k * |C k i| * |C k j| ≤ (K * h i) * (K / 2 + K * siegS K k.val) *
            (K / 2 + K * siegS K k.val) := by
            have := hhk i k hki.le
            have h0 : 0 ≤ K * h i * (K / 2 + K * siegS K k.val) :=
              mul_nonneg (mul_nonneg hK0 (hh i).le) hE0
            have hE0' := (abs_nonneg (C k i))
            exact mul_le_mul (mul_le_mul this e1 hE0' (mul_nonneg hK0 (hh i).le)) e2 (abs_nonneg _)
              (mul_nonneg (mul_nonneg hK0 (hh i).le) hE0)
        _ = _ := by ring
    have hsumeq : ∑ k ∈ Finset.Iio i, K * h i * (K / 2 + K * siegS K k.val) ^ 2 =
        K * h i * siegS K m := by
      rw [← Finset.mul_sum, sum_Iio_fin (fun l => (K / 2 + K * siegS K l) ^ 2) i, hi,
        ← siegS_eq_sum]
    have hprod : |h i * C i j| ≤ h i * (K / 2 + K * siegS K m) := by
      have e : h i * C i j = F i j - ∑ k ∈ Finset.Iio i, h k * C k i * C k j := by
        rw [hoff]; ring
      rw [e]
      calc |F i j - ∑ k ∈ Finset.Iio i, h k * C k i * C k j|
          ≤ |F i j| + |∑ k ∈ Finset.Iio i, h k * C k i * C k j| := abs_sub _ _
        _ ≤ K * h i / 2 + K * h i * siegS K m := by
            rw [hsumeq] at hsum; linarith
        _ = _ := by ring
    rw [abs_mul, abs_of_pos (hh i)] at hprod
    exact le_of_mul_le_mul_left hprod (hh i)
  refine ⟨h, C, hd, hh, fun i j hij => ?_, fun i j hij => ?_⟩
  · exact hhk j i (by rw [Fin.le_def]; omega)
  · refine (key i.val i rfl j hij).trans ?_
    have := siegS_mono K (show i.val ≤ n from i.isLt.le)
    nlinarith

end QuadFormsKB.Reduction
