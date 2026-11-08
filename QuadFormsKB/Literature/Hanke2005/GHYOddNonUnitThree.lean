/-
# Gan–Hanke–Yu 2001, Table 4: the odd-rank row $\delta\notin A^\times$, $w = -1$, at every place

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), (6.6), (6.11), Table 4.

For odd rank $n = 2k+3$ and $\delta$ a uniformizer times a unit, the maximal lattice of $V_{\delta,-1}$ has the form
$\mathbb H^k\perp N$ with kernel $N = \langle\pi c\rangle\perp T$ of rank $3$ (`splitForm (π * c) T`), $T$ a unimodular
binary form whose reduction is anisotropic over the residue field, $c$ a unit. We compute its local density at every
level $k$ and at every residue characteristic ($e = \mathrm{ord}_\pi 2 \ge 0$; $e = 0$ is the non-dyadic case):
$$\beta(\mathbb H^k\perp N) = 4q^{e+1}(1 + q^{-1})\prod_{j<k}\rho_j(q),\qquad
\rho_j(q) = \frac{(q^{j+1}-1)(q^{3+j}+q)}{q^{2j+4}} = (1 - q^{-(j+1)})(1 + q^{-(j+2)}).$$

**Proves**
* `splitForm_piUnit_aniso`: $N$ is anisotropic over $R$ (descent on the valuation);
* `resZero_splitForm_piUnit`: $N \bmod \pi$ has exactly $q$ zeros (the residue form is $0\cdot x_0^2 + \bar T(y)$);
* `localDensityForm_piU_T_odd`, `localDensityForm_piU_T_any`: $\beta(N, T) = 2(q+1)/q$ at $\pi\nmid 2$, resp. at every prime
  (non-dyadic analogue of `localDensityForm_piU_T`; $|O(\bar T)| = 2(q+1)$ comes from the unimodular self-density
  and `localDensityForm_eq_of_isUnit`);
* `localDensityForm_splitForm_piUnit`: the level-$0$ value $\beta(N, N) = 4q^{e+1}(1 + q^{-1})$, from the frame lemma
  `localDensityForm_frame`, $\beta(N,N) = \beta(N,T)\,\beta(\langle\pi c\rangle,\langle\pi c\rangle)$, and
  $\beta(\langle\pi c\rangle) = q\cdot 2q^e$;
* **`localDensityForm_hypSum_piUnitT`**: the main formula above, by induction with `localDensityForm_hypSum_succ`;
* closed forms (real algebra, $q>1$, `ppow q k` $=\prod_{i<k}(1 - q^{-2(i+1)})$):
  $\prod_{j<k}\rho_j(q)|_{r=1} = 2(1 - q^{-k})\,\mathrm{ppow}_{k-1}$ for $k\ge1$ (`prod_rho_one_eq`) and
  $(1 + q^{-1})\prod_{j<k}\rho_j(q)|_{r=3} = (1 + q^{-(k+1)})\,\mathrm{ppow}_k$ (`prod_rho_three_eq`), giving the
  self-densities of the $w = 1$ row, $2q^{e+1}\cdot2(1 - q^{-k})\mathrm{ppow}_{k-1}$
  (`localDensityForm_hypSum_piUnit_closed`), and of the $w=-1$ row, $4q^{e+1}(1 + q^{-(k+1)})\mathrm{ppow}_k$
  (`localDensityForm_hypSum_piUnitT_closed`).

Indices are 0-based: the split-off coordinate of $N$ is $x_0$ and $T$ sees $x_1, x_2$ as its $x_0, x_1$.
-/
import QuadFormsKB.Literature.Hanke2005.GHYOddNonUnit
import QuadFormsKB.Literature.Hanke2005.MassFormula
import QuadFormsKB.Tamagawa.TernaryBadDVR
import QuadFormsKB.Tamagawa.TernaryRamDyadic

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.LocalDensity.HypFrame QuadFormsKB.Tamagawa
  QuadForm

/-! ### Closed forms (real algebra) -/

section Closed

theorem rpow_neg_natCast_ghy {q : ℝ} (hq : 0 < q) (m : ℕ) : q ^ (-(m : ℝ)) = (q ^ m)⁻¹ := by
  rw [Real.rpow_neg hq.le, Real.rpow_natCast]

theorem rho_one_eq {q : ℝ} (hq : 0 < q) (j : ℕ) :
    rho q 1 q j = (1 - (q ^ (j + 1))⁻¹) * (1 + (q ^ j)⁻¹) := by
  unfold rho
  have := pow_pos hq j
  have := pow_pos hq (j + 1)
  field_simp
  ring

theorem rho_three_eq {q : ℝ} (hq : 0 < q) (j : ℕ) :
    rho q 3 q j = (1 - (q ^ (j + 1))⁻¹) * (1 + (q ^ (j + 2))⁻¹) := by
  unfold rho
  have := pow_pos hq j
  have := pow_pos hq (j + 1)
  field_simp
  ring

theorem ppow_succ_ghy {q : ℝ} (hq : 0 < q) (m : ℕ) :
    ppow q (m + 1) = (1 - ((q ^ (m + 1))⁻¹) ^ 2) * ppow q m := by
  have := ppow_succ_eq hq.le (m + 1) (by omega)
  rw [this, Nat.add_sub_cancel]
  rw [rpow_neg_natCast_ghy hq (m + 1)]

/-- **The product of the $w = 1$ ratios** ($r = 1$, $Z = q$): for $k\ge1$,
$\prod_{j<k}\rho_j = 2(1 - q^{-k})\,\mathrm{ppow}_{k-1}(q)$. -/
theorem prod_rho_one_eq {q : ℝ} (hq : 1 < q) {k : ℕ} (hk : 1 ≤ k) :
    ∏ j ∈ Finset.range k, rho q 1 q j = 2 * (1 - q ^ (-(k : ℝ))) * ppow q (k - 1) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  clear hk
  rw [Nat.add_sub_cancel, rpow_neg_natCast_ghy hq0]
  induction m with
  | zero =>
    simp [ppow, rho_one_eq hq0]
    ring
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, rho_one_eq hq0, ppow_succ_ghy hq0 m]
    have := pow_pos hq0 (m + 1)
    have h : q ^ (m + 1 + 1) = q ^ (m + 1) * q := by ring
    simp only [h]
    field_simp
    ring

/-- **The product of the $w = -1$ ratios** ($r = 3$, $Z = q$): for every $k$,
$(1 + q^{-1})\prod_{j<k}\rho_j = (1 + q^{-(k+1)})\,\mathrm{ppow}_k(q)$. -/
theorem prod_rho_three_eq {q : ℝ} (hq : 1 < q) (k : ℕ) :
    (1 + q⁻¹) * ∏ j ∈ Finset.range k, rho q 3 q j = (1 + q ^ (-((k : ℝ) + 1))) * ppow q k := by
  have hq0 : 0 < q := by linarith
  have e : ∀ k : ℕ, q ^ (-((k : ℝ) + 1)) = (q ^ (k + 1))⁻¹ := fun k => by
    rw [← rpow_neg_natCast_ghy hq0]; push_cast; rfl
  rw [e]
  induction k with
  | zero => simp [ppow]
  | succ m ih =>
    rw [Finset.prod_range_succ, show ∀ a b c : ℝ, a * (b * c) = a * b * c from fun a b c => by ring, ih,
      rho_three_eq hq0, ppow_succ_ghy hq0 m]
    have := pow_pos hq0 (m + 1)
    have h : q ^ (m + 1 + 1) = q ^ (m + 1) * q := by ring
    simp only [h]
    field_simp
    ring

end Closed

/-! ### The kernel $N = \langle\pi c\rangle\perp T$ -/

section Kernel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem eval_scale_two_ghy (T : QuadForm R 2) (a : R) (y : Fin 2 → R) :
    T.eval (fun i => a * y i) = a * a * T.eval y := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two]
  ring

/-- In a DVR an element divisible by every power of $\pi$ is $0$. -/
theorem eq_zero_of_forall_pow_dvd_ghy {π : R} (hπ : Irreducible π) {a : R} (h : ∀ j : ℕ, π ^ j ∣ a) :
    a = 0 := by
  by_contra ha
  obtain ⟨e, -, he⟩ := exists_pow_dvd_not_dvd π hπ ha
  exact he (h _)

/-- **$N = \langle\pi c\rangle\perp T$ is anisotropic over $R$** ($c$ a unit, $T$ binary with $\bar T$ anisotropic):
if $\pi c t^2 + T(y) = 0$ then $\pi\mid T(y)$, so $\pi\mid y$, then $\pi\mid t$, and dividing by $\pi$ we descend;
hence $\pi^j$ divides every coordinate for all $j$. -/
theorem splitForm_piUnit_aniso {π : R} (hπ : Irreducible π) {c : R} (hc : IsUnit c) (T : QuadForm R 2)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    ∀ x, (splitForm (π * c) T).eval x = 0 → x = 0 := by
  have key : ∀ j : ℕ, ∀ (t : R) (y : Fin 2 → R), π * c * t * t + T.eval y = 0 →
      π ^ j ∣ t ∧ ∀ i, π ^ j ∣ y i := by
    intro j
    induction j with
    | zero => intro t y _; exact ⟨by simp, fun i => by simp⟩
    | succ j ih =>
      intro t y h
      have hdv : π ∣ T.eval y := ⟨-(c * t * t), by linear_combination h⟩
      have hy := haniso y hdv
      choose y' hy' using hy
      have hyy : y = fun i => π * y' i := funext hy'
      subst hyy
      rw [eval_scale_two_ghy] at h
      have h1 : c * t * t + π * T.eval y' = 0 := by
        apply mul_left_cancel₀ hπ.ne_zero
        linear_combination h
      have hdt : π ∣ c * (t * t) := ⟨-(T.eval y'), by linear_combination h1⟩
      have hp := hπ.prime
      rcases hp.dvd_or_dvd hdt with hc' | ht
      · exact absurd (isUnit_of_dvd_unit hc' hc) hπ.not_isUnit
      · have ht' : π ∣ t := by
          rcases hp.dvd_or_dvd ht with h' | h' <;> exact h'
        obtain ⟨t', rfl⟩ := ht'
        have h2 : π * c * t' * t' + T.eval y' = 0 := by
          apply mul_left_cancel₀ hπ.ne_zero
          linear_combination h1
        obtain ⟨h3, h4⟩ := ih t' y' h2
        exact ⟨by rw [pow_succ']; exact mul_dvd_mul_left π h3,
          fun i => by rw [pow_succ']; exact mul_dvd_mul_left π (h4 i)⟩
  intro x hx
  rw [← Fin.cons_self_tail x, eval_splitForm_cons] at hx
  have := fun j => key j (x 0) (Fin.tail x) hx
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact eq_zero_of_forall_pow_dvd_ghy hπ fun j => (this j).1
  · exact eq_zero_of_forall_pow_dvd_ghy hπ fun j => (this j).2 i

/-- If $\bar T$-anisotropy holds on lifts then $\bar T$ has only the trivial zero over the residue field. -/
theorem aniso_res_ghy {π : R} (hπ : Irreducible π) (T : QuadForm R 2)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    ∀ y : Fin 2 → IsLocalRing.ResidueField R, (T.map (IsLocalRing.residue R)).eval y = 0 → y = 0 := by
  intro y hy
  obtain ⟨y', rfl⟩ := res_surj_vec (R := R) y
  rw [eval_map_comp', res_eq_zero_iff' hπ] at hy
  funext i
  exact (res_eq_zero_iff' hπ _).2 (haniso y' hy i)

/-- **$N \bmod \pi$ has exactly $q$ zeros**: the residue form is $0\cdot x_0^2 + \bar T(y)$, zero iff $y = 0$. -/
theorem resZero_splitForm_piUnit {π : R} (hπ : Irreducible π) (c : R) (T : QuadForm R 2)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    (resZero π (splitForm (π * c) T) : ℝ) = q R := by
  rw [resZero_eq_zeroCount_res hπ]
  have hr : IsLocalRing.residue R (π * c) = 0 := (res_eq_zero_iff' hπ _).2 (dvd_mul_right _ _)
  have hA := aniso_res_ghy hπ T haniso
  unfold zeroCount
  rw [map_splitForm, hr]
  have e : {x : Fin 3 → IsLocalRing.ResidueField R //
      (splitForm 0 (T.map (IsLocalRing.residue R))).eval x = 0} ≃ IsLocalRing.ResidueField R :=
    { toFun := fun x => x.1 0
      invFun := fun t => ⟨Fin.cons t 0, by rw [eval_splitForm_cons]; simp [QuadForm.eval, QuadForm.evalIn]⟩
      left_inv := fun x => by
        apply Subtype.ext
        have hx := x.2
        rw [← Fin.cons_self_tail x.1, eval_splitForm_cons] at hx
        have := hA _ (by simpa using hx)
        conv_rhs => rw [← Fin.cons_self_tail x.1]
        simp [this]
      right_inv := fun t => rfl }
  rw [Nat.card_congr e]
  rfl

end Kernel

/-! ### The density $\beta(N, T)$ at $\pi\nmid2$ -/

section OddDensity

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem eval_two_ghy {A : Type*} [CommRing A] (S : QuadForm A 2) (x : Fin 2 → A) :
    S.eval x = S.coeff 0 0 * x 0 * x 0 + S.coeff 0 1 * x 0 * x 1 + S.coeff 1 1 * x 1 * x 1 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two]

theorem det_hessian_two_ghy {A : Type*} [CommRing A] (S : QuadForm A 2) :
    S.hessian.det = 4 * S.coeff 0 0 * S.coeff 1 1 - S.coeff 0 1 * S.coeff 0 1 := by
  have h10 : S.coeff 1 0 = 0 := S.upper (show (0 : Fin 2) < 1 by decide)
  simp only [hessian, det_fin_two, Matrix.add_apply, Matrix.transpose_apply, h10]
  ring

/-- Row splitting: representations of $T$ by $\langle0\rangle\perp T$ over a ring $A$ are a free first row times
the representations of $T$ by $T$. -/
theorem card_reps_splitForm_zero_ghy {A : Type*} [CommRing A] (T : QuadForm A 2) :
    Nat.card {Y : Matrix (Fin 3) (Fin 2) A // (splitForm 0 T).compMat Y = T} =
      Nat.card A ^ 2 * Nat.card {X : Matrix (Fin 2) (Fin 2) A // T.compMat X = T} := by
  simp_rw [splitForm_zero_compMat]
  let e : {Y : Matrix (Fin 3) (Fin 2) A // T.compMat (Matrix.of fun (i : Fin 2) (j : Fin 2) => Y i.succ j) = T} ≃
      (Fin 2 → A) × {X : Matrix (Fin 2) (Fin 2) A // T.compMat X = T} :=
    { toFun := fun Y => (fun j => Y.1 0 j, ⟨Matrix.of fun i j => Y.1 i.succ j, Y.2⟩)
      invFun := fun p => ⟨Matrix.of fun i j => Fin.cases (p.1 j) (fun i' => p.2.1 i' j) i, by
        convert p.2.2 using 2
        ext i j; rfl⟩
      left_inv := fun Y => Subtype.ext (by ext i j; refine Fin.cases rfl (fun i => rfl) i)
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_fin]

variable [Finite (IsLocalRing.ResidueField R)]

/-- For $\pi\nmid2$ and $\bar T$ anisotropic of unit determinant, the discriminant character of $T$ is $-1$. -/
theorem chiDisc_aniso_ghy [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
    {π : R} (hπ : Irreducible π) (h2π : ¬ π ∣ 2) (T : QuadForm R 2)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    chiDisc (R := R) (n := 2) T = -1 := by
  have hA := aniso_res_ghy hπ T haniso
  have h2F : (2 : IsLocalRing.ResidueField R) ≠ 0 := by
    have := res_ne_zero hπ h2π; rwa [map_ofNat] at this
  unfold chiDisc resGramDet
  rw [quadraticChar_neg_one_iff_not_isSquare, det_hessian_two_ghy]
  rintro ⟨s, hs⟩
  simp only [map_sub, map_mul, map_ofNat] at hs
  set a := IsLocalRing.residue R (T.coeff 0 0)
  set b := IsLocalRing.residue R (T.coeff 0 1)
  set c := IsLocalRing.residue R (T.coeff 1 1)
  have hev : ∀ x : Fin 2 → IsLocalRing.ResidueField R,
      (T.map (IsLocalRing.residue R)).eval x = a * x 0 * x 0 + b * x 0 * x 1 + c * x 1 * x 1 := fun x => by
    rw [eval_two_ghy]; rfl
  have hs' : b * b - 4 * a * c = (2 * s) ^ 2 := by
    have h22 : (2 : ℕ) / 2 = 1 := rfl
    rw [h22, pow_one] at hs
    have h3 : 4 * a * c - b * b = -((2 : IsLocalRing.ResidueField R) ^ 2 * (s * s)) := by
      rw [← hs]; field_simp
    linear_combination (-1 : IsLocalRing.ResidueField R) * h3
  by_cases ha : a = 0
  · have := hA ![1, 0] (by rw [hev]; simp [ha])
    have h := congrFun this 0
    simp at h
  · have := hA ![(-b + 2 * s) / (2 * a), 1] (by
      rw [hev]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      linear_combination (-1 : IsLocalRing.ResidueField R) * hs')
    have h := congrFun this 1
    simp at h

/-- **$\beta_\pi(\langle\pi u\rangle\perp T, T) = 2(q+1)/q$ at $\pi\nmid2$** for $T$ unimodular with $\bar T$ anisotropic:
the count mod $\pi$ is $q^2|O(\bar T)| = q^2\cdot2(q+1)$, where $|O(\bar T)| = 2(q+1)$ follows from the unimodular
self-density $\beta(T,T) = 2(1 + q^{-1})$ (`localDensityForm_self_even`, $\chi_D = -1$). Non-dyadic analogue of
`localDensityForm_piU_T`. -/
theorem localDensityForm_piU_T_odd [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (h2π : ¬ π ∣ 2) (u : R) (T : QuadForm R 2)
    (hT : IsUnit T.hessian.det) (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    localDensityForm (splitForm (π * u) T) T π = 2 * ((q R : ℝ) + 1) / q R := by
  classical
  let _ := Fintype.ofFinite (IsLocalRing.ResidueField R)
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  have hχ := chiDisc_aniso_ghy hπ h2π T haniso
  have hself : localDensityForm T T π = 2 * (1 + ((q R : ℝ))⁻¹) := by
    have h := localDensityForm_self_even π 1 le_rfl T hπ h2π (dvr_not_dvd_of_isUnit hπ hT)
    simp only [hχ, Nat.sub_self, Finset.range_zero, Finset.prod_empty, mul_one, pow_one, Int.cast_neg,
      Int.cast_one, neg_mul, one_mul, sub_neg_eq_add] at h
    exact h
  have hrep : (repCountForm T T π 1 : ℝ) = 2 * ((q R : ℝ) + 1) := by
    have h := localDensityForm_eq_of_isUnit T T π hπ hT le_rfl
    rw [hself, show 2 * 2 - 2 * (2 + 1) / 2 = 1 by norm_num, pow_one, eq_div_iff hq.ne'] at h
    rw [← h]; field_simp
  rw [localDensityForm_eq_of_isUnit _ _ π hπ hT (by norm_num)]
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  have hfin := finite_quot_pow π hπ 1
  have hπu : Ideal.Quotient.mk (Ideal.span {π ^ 1}) (π * u) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]; exact dvd_mul_right _ _
  have hcard : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by rw [card_quot_pow π hπ, pow_one]
  have hsplit : repCountForm (splitForm (π * u) T) T π 1 = q R ^ 2 * repCountForm T T π 1 := by
    unfold repCountForm
    rw [map_splitForm, hπu, card_reps_splitForm_zero_ghy, hcard]
  rw [hsplit]
  push_cast
  rw [hrep]
  field_simp

/-- **$\beta_\pi(\langle\pi u\rangle\perp T, T) = 2(q+1)/q$ at every prime** (case split on $\pi\mid2$:
`localDensityForm_piU_T` or `localDensityForm_piU_T_odd`). -/
theorem localDensityForm_piU_T_any [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (u : R) (T : QuadForm R 2) (hT : IsUnit T.hessian.det)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    localDensityForm (splitForm (π * u) T) T π = 2 * ((q R : ℝ) + 1) / q R := by
  by_cases h2π : π ∣ 2
  · exact localDensityForm_piU_T hπ h2π u T hT haniso
  · exact localDensityForm_piU_T_odd hπ h2π u T hT haniso

end OddDensity

/-! ### Level 0, the main formula and the closed forms -/

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- **The kernel's self-density** (Gan–Hanke–Yu Table 4, $\delta\notin A^\times$, $w=-1$, level $0$):
$\beta(\langle\pi c\rangle\perp T,\ \langle\pi c\rangle\perp T) = 4q^{e+1}(1 + q^{-1})$, $\pi^e\,\|\,2$.
From the frame lemma, `localDensityForm_piU_T_any`, and $\beta(\langle\pi c\rangle) = q\cdot2q^e$. -/
theorem localDensityForm_splitForm_piUnit {π : R} (hπ : Irreducible π) {e : ℕ}
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {c : R} (hc : IsUnit c) (T : QuadForm R 2)
    (hT : IsUnit T.hessian.det) (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    localDensityForm (splitForm (π * c) T) (splitForm (π * c) T) π =
      4 * (q R : ℝ) ^ (e + 1) * (1 + (q R : ℝ)⁻¹) := by
  have h20 : (2 : R) ≠ 0 := fun h => he.2 (h ▸ dvd_zero _)
  have hπc : π * c ≠ 0 := mul_ne_zero hπ.ne_zero hc.ne_zero
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  rw [localDensityForm_frame hπ h20 hπc T hT, localDensityForm_piU_T_any hπ c T hT haniso]
  have hU : (DVR.unary c).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_unary_det]; exact mul_ne_zero h20 hc.ne_zero
  rw [unary_mul_eq_smul, localDensityForm_smul (DVR.unary c) hU hπ (o := 1) (by simp)
    (fun h => hπ.not_isUnit (isUnit_of_dvd_one (by
      rw [pow_two] at h; exact (mul_dvd_mul_iff_left hπ.ne_zero).mp (by simpa using h)))),
    localDensityForm_self_unary π hπ e he hc]
  field_simp
  ring

/-- **The density of $\mathbb H^k\perp(\langle\pi c\rangle\perp T)$ at every prime** (Gan–Hanke–Yu Table 4, $\delta\notin A^\times$,
$w = -1$): $4q^{e+1}(1 + q^{-1})\prod_{j<k}\rho_j(q)$, $\pi^e\,\|\,2$ ($e = 0$ allowed), $c$ a unit, $T$ unimodular
binary with $\bar T$ anisotropic. -/
@[kb "ganhankeyu2001" "(6.6), (6.11), Table 4 (odd rank, δ ∉ A×, w = −1)"]
theorem localDensityForm_hypSum_piUnitT {π : R} (hπ : Irreducible π) {e : ℕ}
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {c : R} (hc : IsUnit c) (T : QuadForm R 2)
    (hT : IsUnit T.hessian.det) (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) (k : ℕ) :
    localDensityForm (hypSum (splitForm (π * c) T) k) (hypSum (splitForm (π * c) T) k) π =
      4 * (q R : ℝ) ^ (e + 1) * (1 + (q R : ℝ)⁻¹) * ∏ j ∈ Finset.range k, rho (q R) 3 (q R) j := by
  have h20 : (2 : R) ≠ 0 := fun h => he.2 (h ▸ dvd_zero _)
  have hπc : π * c ≠ 0 := mul_ne_zero hπ.ne_zero hc.ne_zero
  have hN : (splitForm (π * c) T).Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]
    exact mul_ne_zero (mul_ne_zero h20 hπc) hT.ne_zero
  have han := splitForm_piUnit_aniso hπ hc T haniso
  have hZ := resZero_splitForm_piUnit hπ c T haniso
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, mul_one]
    exact localDensityForm_splitForm_piUnit hπ he hc T hT haniso
  | succ k ih =>
    rw [localDensityForm_hypSum_succ hπ _ hN han k, ih, hZ, Finset.prod_range_succ]
    ring

/-- **Closed form, $w = 1$ row** (Gan–Hanke–Yu Table 4, $\delta\notin A^\times$): for $k\ge1$ and $q>1$ real, with $q = q_R$,
$\beta(\mathbb H^k\perp\langle\pi u\rangle) = 2q^{e+1}\cdot2(1 - q^{-k})\,\mathrm{ppow}_{k-1}(q)$. -/
theorem localDensityForm_hypSum_piUnit_closed {π : R} (hπ : Irreducible π) {e : ℕ}
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {u : R} (hu : IsUnit u) {k : ℕ} (hk : 1 ≤ k) :
    localDensityForm (hypSum (DVR.unary (π * u)) k) (hypSum (DVR.unary (π * u)) k) π =
      2 * (q R : ℝ) ^ (e + 1) * (2 * (1 - (q R : ℝ) ^ (-(k : ℝ))) * ppow (q R : ℝ) (k - 1)) := by
  have hq : (1 : ℝ) < q R := by exact_mod_cast one_lt_q (R := R)
  rw [localDensityForm_hypSum_piUnit hπ he hu k, prod_rho_one_eq hq hk]

/-- **Closed form, $w = -1$ row** (Gan–Hanke–Yu Table 4, $\delta\notin A^\times$): for every $k$, with $q = q_R$,
$\beta(\mathbb H^k\perp N) = 4q^{e+1}(1 + q^{-(k+1)})\,\mathrm{ppow}_k(q)$, $N = \langle\pi c\rangle\perp T$. -/
theorem localDensityForm_hypSum_piUnitT_closed {π : R} (hπ : Irreducible π) {e : ℕ}
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {c : R} (hc : IsUnit c) (T : QuadForm R 2)
    (hT : IsUnit T.hessian.det) (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) (k : ℕ) :
    localDensityForm (hypSum (splitForm (π * c) T) k) (hypSum (splitForm (π * c) T) k) π =
      4 * (q R : ℝ) ^ (e + 1) * ((1 + (q R : ℝ) ^ (-((k : ℝ) + 1))) * ppow (q R : ℝ) k) := by
  have hq : (1 : ℝ) < q R := by exact_mod_cast one_lt_q (R := R)
  rw [localDensityForm_hypSum_piUnitT hπ he hc T hT haniso k, mul_assoc, prod_rho_three_eq hq k]

end Main

end QuadFormsKB.Hanke2005
