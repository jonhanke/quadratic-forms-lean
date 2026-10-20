/-
# The window estimates for $\varphi_y$, $y = r(1+\eta)$

**Layer:** a number field $F$, a finite place $v$ (dyadic and ramified places included), $a, b, d\in\mathcal O_F$, $E = F_v[\delta]$,
$D_E = (a,b)_E$ over $F_v$ (`DEr Fv a b d`), $|2|_v = q^{-s}$.

* `QL k x`: all eight $F_v$-coordinates of $x\in D_E$ have valuation $\le q^{-k}$; **`QL.mul`**: $QL_k\cdot QL_{k'}\subseteq QL_{k+k'}$.
* **`valued_coords_Qmap_le`**: the quadratic part $Q_\eta(e_j)$ of $W_\eta$ has coordinates of valuation $\le q^{-2k}$ when the
  coordinates of $\eta$ have valuation $\le q^{-k}$.
* **`Lwin v N`** $=\{\eta = \eta' + \delta\eta'' : \eta'\in\Lambda'_N\ (\text{`latP`}),\ 2\eta''\in\mathfrak p^N\}$ and
  **`dco_le_iff`**: all entries of the linear part $D_\eta$ (`Dco`) lie in $\mathfrak p^N$ iff $\eta\in$ `Lwin v N`.
* **`rho_cases`**: $\rho\in F_v$ with $\rho^2N(1+z) = 1$, $|z|\le q^{-2k}$ ($2k > N + s$) has $\rho\equiv\pm1\bmod\mathfrak p^N$.
* **`ballOne_of_win`** / **`mem_win_of_ballOne`**: for $y = r(1+\operatorname{pureE}\eta)\in G^\natural(F_v)$ with small $\eta$:
  $\varphi_y\in K_N$ iff $\eta\in$ `Lwin v N` and $\rho\equiv1\bmod\mathfrak p^N$.

Source: Weil 1982, §2.2-2.3, §3.7 [unverified page] (the window: linearization of $\varphi$ at $1$).
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinVal
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinAlg

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic

section Window

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b d : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))
local notation "D" => DEr (v.adicCompletion F) a b d
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)

theorem CL.const_mul {k : ℤ} {c z : E} (hc : CL v 0 c) (h : CL v k z) : CL v k (c * z) := by
  have := hc.mul h; rwa [zero_add] at this

theorem CL.mul_const {k : ℤ} {c z : E} (hc : CL v 0 c) (h : CL v k z) : CL v k (z * c) := by
  rw [mul_comm]; exact hc.const_mul h

theorem CL_algebraMap_int (x : 𝓞 F) : CL v 0 (algebraMap Fv E (algebraMap F Fv (x : F))) :=
  CL.algebraMap (by rw [neg_zero, exp_zero]; exact valued_algebraMap_le_one x v)

variable (v) in
/-- **Quaternion level**: all eight $F_v$-coordinates of $x$ have valuation $\le q^{-k}$. -/
def QL (k : ℤ) (x : D) : Prop := CL v k x.re ∧ CL v k x.imI ∧ CL v k x.imJ ∧ CL v k x.imK

theorem QL.mono {k k' : ℤ} {x : D} (h : QL v k x) (hk : k' ≤ k) : QL v k' x :=
  ⟨h.1.mono hk, h.2.1.mono hk, h.2.2.1.mono hk, h.2.2.2.mono hk⟩

theorem QL.add {k : ℤ} {x y : D} (h : QL v k x) (h' : QL v k y) : QL v k (x + y) :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, h.2.2.1.add h'.2.2.1, h.2.2.2.add h'.2.2.2⟩

theorem QL.neg {k : ℤ} {x : D} (h : QL v k x) : QL v k (-x) :=
  ⟨h.1.neg, h.2.1.neg, h.2.2.1.neg, h.2.2.2.neg⟩

theorem QL.sub {k : ℤ} {x y : D} (h : QL v k x) (h' : QL v k y) : QL v k (x - y) := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

/-- **Products**: $QL_k\cdot QL_{k'}\subseteq QL_{k+k'}$ ($a, b$ integral). -/
theorem QL.mul {k k' : ℤ} {x y : D} (h : QL v k x) (h' : QL v k' y) : QL v (k + k') (x * y) := by
  obtain ⟨x0, x1, x2, x3⟩ := h
  obtain ⟨y0, y1, y2, y3⟩ := h'
  have hA := CL_algebraMap_int (v := v) (d := d) a
  have hB := CL_algebraMap_int (v := v) (d := d) b
  have hAB : CL v 0 (algebraMap Fv E Av * algebraMap Fv E Bv) := by simpa using hA.mul hB
  have cm : ∀ {c x' y' : E} {j j' : ℤ}, CL v 0 c → CL v j x' → CL v j' y' → CL v (j + j') (c * x' * y') :=
    fun hc hx hy => (hc.const_mul hx).mul hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
      QuaternionAlgebra.imK_mul, zero_mul, add_zero]
  · exact (((x0.mul y0).add (cm hA x1 y1)).add (cm hB x2 y2)).sub (cm hAB x3 y3)
  · exact (((x0.mul y1).add (x1.mul y0)).sub (cm hB x2 y3)).add (cm hB x3 y2)
  · exact (((x0.mul y2).add (cm hA x1 y3)).add (x2.mul y0)).sub (cm hA x3 y1)
  · exact (((x0.mul y3).add (x1.mul y2)).sub (x2.mul y1)).add (x3.mul y0)

theorem QL_zero (k : ℤ) : QL v k (0 : D) := ⟨CL.zero k, CL.zero k, CL.zero k, CL.zero k⟩

theorem QL_pureE {k : ℤ} {η : Fin 3 → E} (h : ∀ l, CL v k (η l)) : QL v k (pureE η : D) :=
  ⟨CL.zero k, h 0, h 1, h 2⟩

theorem QL_pureE_starV {k : ℤ} {η : Fin 3 → E} (h : ∀ l, CL v k (η l)) : QL v k (pureE (starV η) : D) :=
  ⟨CL.zero k, (h 0).star, (h 1).star, (h 2).star⟩

theorem QL_emb_single (j : Fin 4) : QL v 0 (emb (Pi.single j 1) : D) := by
  have h1 : Valued.v (1 : Fv) ≤ exp (-(0 : ℤ)) := by rw [neg_zero, exp_zero, map_one]
  have h0 : Valued.v (0 : Fv) ≤ exp (-(0 : ℤ)) := by rw [map_zero]; exact zero_le
  have hs : ∀ i, Valued.v ((Pi.single j (1 : Fv) : Fin 4 → Fv) i) ≤ exp (-(0 : ℤ)) := by
    intro i; by_cases hij : i = j
    · subst hij; rw [Pi.single_eq_same]; exact h1
    · rw [Pi.single_eq_of_ne hij]; exact h0
  exact ⟨⟨hs 0, h0⟩, ⟨h0, hs 1⟩, ⟨h0, hs 2⟩, ⟨h0, hs 3⟩⟩

theorem QL.valued_coords {k : ℤ} {x : D} (h : QL v k x) (i : Fin 4) : Valued.v (coords x i) ≤ exp (-k) := by
  fin_cases i
  · exact h.1.1
  · exact h.2.1.2
  · exact h.2.2.1.2
  · exact h.2.2.2.2

/-- **The quadratic part is small**: $|Q_\eta(e_j)_i|\le q^{-2k}$. -/
theorem valued_coords_Qmap_le {k : ℤ} {η : Fin 3 → E} (h : ∀ l, CL v k (η l)) (i j : Fin 4) :
    Valued.v (coords (Qmap η (emb (Pi.single j 1) : D)) i) ≤ exp (-(2 * k)) := by
  have := (((QL_pureE (v := v) (a := a) (b := b) h).mul (QL_emb_single j)).mul (QL_pureE_starV h)).neg
  rw [show k + 0 + k = 2 * k by ring] at this
  exact this.valued_coords i

theorem valued_mul_le_of_le' {x y : Fv} {m : ℤ} (hx : Valued.v x ≤ exp (-m)) (hy : Valued.v y ≤ 1) :
    Valued.v (x * y) ≤ exp (-m) := by
  rw [map_mul]
  calc Valued.v x * Valued.v y ≤ exp (-m) * 1 := mul_le_mul' hx hy
    _ = _ := mul_one _

/-! ### The window lattice -/

variable (v a b d) in
/-- **The window lattice** $\{\eta' + \delta\eta'' : \eta'\in\Lambda'_N,\ 2\eta''\in\mathfrak p^N\}$. -/
def Lwin (N : ℕ) : Set (Fin 3 → E) :=
  {η | (fun l => (η l).re) ∈ latP v N Av Bv ∧ ∀ l, Valued.v (2 * (η l).im) ≤ exp (-(N : ℤ))}

theorem valued_mul_le_of_le {x y : Fv} {m : ℤ} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ exp (-m)) :
    Valued.v (x * y) ≤ exp (-m) := by
  rw [map_mul]
  calc Valued.v x * Valued.v y ≤ 1 * exp (-m) := mul_le_mul' hx hy
    _ = _ := one_mul _

/-- **The linear part detects `Lwin`**: all entries of $D_\eta$ lie in $\mathfrak p^N$ iff $\eta\in$ `Lwin v N`. -/
theorem dco_le_iff (N : ℕ) (η : Fin 3 → E) :
    (∀ i j, Valued.v (Dco (a := Av) (b := Bv) (d := algebraMap F Fv (d : F)) η i j) ≤ exp (-(N : ℤ))) ↔
      η ∈ Lwin v a b d N := by
  have hA := valued_algebraMap_le_one a v
  have hB := valued_algebraMap_le_one b v
  have hD := valued_algebraMap_le_one d v
  have hAD : Valued.v (Av * algebraMap F Fv (d : F)) ≤ 1 := by
    rw [map_mul]; exact mul_le_one' hA hD
  have hBD : Valued.v (Bv * algebraMap F Fv (d : F)) ≤ 1 := by
    rw [map_mul]; exact mul_le_one' hB hD
  have hABD : Valued.v (Av * Bv * algebraMap F Fv (d : F)) ≤ 1 := by
    rw [map_mul, map_mul]; exact mul_le_one' (mul_le_one' hA hB) hD
  constructor
  · intro h
    refine ⟨(adMat_le_iff hA hB N _).1 fun i l => ?_, fun l => ?_⟩
    · have := h i.succ l.succ
      rw [adMat_eq]
      fin_cases i <;> fin_cases l <;> simpa [Dco] using this
    · have := h l.succ 0
      fin_cases l <;> simpa [Dco] using this
  · rintro ⟨⟨p0, p1, p2, p3⟩, h2⟩ i j
    have h0 : Valued.v (0 : Fv) ≤ exp (-(N : ℤ)) := by rw [map_zero]; exact zero_le
    have q0 := h2 0
    have q1 := h2 1
    have q2 := h2 2
    have e1 : ∀ x y : Fv, x * (2 * y) = 2 * x * y := fun x y => by ring
    fin_cases i <;> fin_cases j
    · simpa [Dco] using h0
    · simpa [Dco, mul_assoc, mul_left_comm] using valued_mul_le_of_le hAD q0
    · simpa [Dco, mul_assoc, mul_left_comm] using valued_mul_le_of_le hBD q1
    · simpa [Dco, mul_assoc, mul_left_comm] using valued_mul_le_of_le hABD q2
    · simpa [Dco] using q0
    · simpa [Dco] using h0
    · simpa [Dco] using p3
    · simpa [Dco, mul_assoc, mul_left_comm] using valued_mul_le_of_le hB p1
    · simpa [Dco] using q1
    · simpa [Dco] using p2
    · simpa [Dco] using h0
    · simpa [Dco, mul_assoc, mul_left_comm] using valued_mul_le_of_le hA p0
    · simpa [Dco] using q2
    · simpa [Dco] using p1
    · simpa [Dco] using p0
    · simpa [Dco] using h0

/-! ### The scalar $\rho$ -/

/-- **$\rho\equiv\pm1$**: $\rho^2c = 1$ with $|c - 1|_v\le q^{-m}$ gives $|\rho\mp1|_v\le q^{-(m-s)}$ for one sign. -/
theorem rho_cases {s : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) {m : ℤ} {ρ c : Fv} (hc : Valued.v (c - 1) ≤ exp (-m))
    (hm : 0 < m) (hρ : ρ ^ 2 * c = 1) :
    Valued.v (ρ - 1) ≤ exp (-(m - s)) ∨ Valued.v (ρ + 1) ≤ exp (-(m - s)) := by
  have hc1 : Valued.v c = 1 := by
    have h1 : Valued.v (c - 1) < 1 := hc.trans_lt (by rw [← exp_zero, exp_lt_exp]; omega)
    have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := 1) (y := c - 1) (by rwa [map_one])
    rwa [add_sub_cancel, map_one] at this
  have hρρ : (ρ - 1) * (ρ + 1) = -(c - 1) * ρ ^ 2 := by
    linear_combination (1 : Fv) * hρ
  have hv : Valued.v (ρ - 1) * Valued.v (ρ + 1) ≤ exp (-m) := by
    have hρ2 : Valued.v ρ ^ 2 = 1 := by
      have := congrArg Valued.v hρ
      rw [map_mul, map_pow, hc1, mul_one, map_one] at this; exact this
    rw [← map_mul, hρρ, map_mul, Valuation.map_neg, map_pow, hρ2, mul_one]; exact hc
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hn1 : ρ - 1 ≠ 0 := by intro h0; rw [h0, map_zero] at h1; exact not_lt.2 zero_le h1
  have hn2 : ρ + 1 ≠ 0 := by intro h0; rw [h0, map_zero] at h2; exact not_lt.2 zero_le h2
  obtain ⟨k1, hk1⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v hn1
  obtain ⟨k2, hk2⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v hn2
  rw [hk1, exp_lt_exp] at h1
  rw [hk2, exp_lt_exp] at h2
  rw [hk1, hk2, ← exp_add, exp_le_exp] at hv
  have h12 : exp (-(s : ℤ)) ≤ max (Valued.v (ρ - 1)) (Valued.v (ρ + 1)) := by
    rw [← hs, show (2 : Fv) = (ρ + 1) - (ρ - 1) by ring]
    exact (Valuation.map_sub _ _ _).trans (by rw [max_comm])
  rw [hk1, hk2] at h12
  rcases le_max_iff.1 h12 with h | h
  · rw [exp_le_exp] at h; omega
  · rw [exp_le_exp] at h; omega

theorem valued_norm_one_add_sub_one {k : ℤ} (hk : 0 ≤ k) {z : E} (hz : CL v k z) :
    Valued.v (QuadraticAlgebra.norm (1 + z) - 1) ≤ exp (-k) := by
  have hd := valued_algebraMap_le_one d v
  have h2 : Valued.v (2 : Fv) ≤ 1 := by rw [valued_two_eq v, ← exp_zero, exp_le_exp]; omega
  have e : QuadraticAlgebra.norm (1 + z) - 1 =
      2 * z.re + (z.re * z.re - algebraMap F Fv (d : F) * z.im * z.im) := by
    rw [QuadraticAlgebra.norm_def]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    ring
  rw [e]
  have hkk : exp (-(k + k)) ≤ exp (-k) := exp_le_exp.2 (by omega)
  have e2 : exp (-(k + k)) = exp (-k) * exp (-k) := by rw [← exp_add]; congr 1; ring
  refine (Valuation.map_add _ _ _).trans (max_le (valued_mul_le_of_le h2 hz.1) ?_)
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact (mul_le_mul' hz.1 hz.1).trans (e2 ▸ hkk)
  · rw [map_mul, map_mul]
    calc Valued.v (algebraMap F Fv (d : F)) * Valued.v z.im * Valued.v z.im ≤ 1 * exp (-k) * exp (-k) :=
          mul_le_mul' (mul_le_mul' hd hz.2) hz.2
      _ ≤ exp (-k) := by rw [one_mul, ← e2]; exact hkk

/-! ### The window in matrix form -/

theorem valued_one_apply_le (i j : Fin 4) : Valued.v ((1 : Matrix (Fin 4) (Fin 4) Fv) i j) ≤ 1 := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- **From $K_N$ to the window**: if $\rho(1 + D + Q)\in 1 + \mathfrak p^NM_4$ with $D_{00} = 0$, $|Q|\le q^{-2k}$, $2k > N$ and
$|\rho| = 1$, then $\rho\equiv1$ and $D\equiv0\bmod\mathfrak p^N$. -/
theorem win_K1 {N : ℕ} {k : ℤ} (hk : (N : ℤ) ≤ 2 * k) {ρ : Fv} (hρ : Valued.v ρ = 1)
    {Dm Qm : Matrix (Fin 4) (Fin 4) Fv} (hQ : ∀ i j, Valued.v (Qm i j) ≤ exp (-(2 * k))) (hD00 : Dm 0 0 = 0)
    (hM : ∀ i j, Valued.v (ρ * ((1 : Matrix (Fin 4) (Fin 4) Fv) i j + Dm i j + Qm i j) -
      (1 : Matrix (Fin 4) (Fin 4) Fv) i j) ≤ exp (-(N : ℤ))) :
    Valued.v (ρ - 1) ≤ exp (-(N : ℤ)) ∧ ∀ i j, Valued.v (Dm i j) ≤ exp (-(N : ℤ)) := by
  have hQN : ∀ i j, Valued.v (ρ * Qm i j) ≤ exp (-(N : ℤ)) := fun i j => by
    rw [map_mul, hρ, one_mul]; exact (hQ i j).trans (exp_le_exp.2 (by omega))
  have hρ1 : Valued.v (ρ - 1) ≤ exp (-(N : ℤ)) := by
    have e : ρ - 1 = (ρ * ((1 : Matrix (Fin 4) (Fin 4) Fv) 0 0 + Dm 0 0 + Qm 0 0) -
        (1 : Matrix (Fin 4) (Fin 4) Fv) 0 0) - ρ * Qm 0 0 := by
      rw [hD00, Matrix.one_apply_eq]; ring
    rw [e]; exact (Valuation.map_sub _ _ _).trans (max_le (hM 0 0) (hQN 0 0))
  refine ⟨hρ1, fun i j => ?_⟩
  have e : ρ * Dm i j = (ρ * ((1 : Matrix (Fin 4) (Fin 4) Fv) i j + Dm i j + Qm i j) -
      (1 : Matrix (Fin 4) (Fin 4) Fv) i j) - (ρ - 1) * (1 : Matrix (Fin 4) (Fin 4) Fv) i j - ρ * Qm i j := by ring
  have h := congrArg Valued.v e
  rw [map_mul, hρ, one_mul] at h
  rw [h]
  refine (Valuation.map_sub _ _ _).trans (max_le ((Valuation.map_sub _ _ _).trans (max_le (hM i j) ?_)) (hQN i j))
  exact valued_mul_le_of_le' hρ1 (valued_one_apply_le i j)

/-- **From the window to $K_N$**: $\rho\equiv1$, $D\equiv0\bmod\mathfrak p^N$, $|Q|\le q^{-2k}$ ($2k\ge N$), $|\rho|\le1$ give
$\rho(1 + D + Q)\in1 + \mathfrak p^NM_4$. -/
theorem win_K2 {N : ℕ} {k : ℤ} (hk : (N : ℤ) ≤ 2 * k) {ρ : Fv} (hρ : Valued.v ρ ≤ 1)
    {Dm Qm : Matrix (Fin 4) (Fin 4) Fv} (hQ : ∀ i j, Valued.v (Qm i j) ≤ exp (-(2 * k)))
    (hρ1 : Valued.v (ρ - 1) ≤ exp (-(N : ℤ))) (hD : ∀ i j, Valued.v (Dm i j) ≤ exp (-(N : ℤ))) (i j : Fin 4) :
    Valued.v (ρ * ((1 : Matrix (Fin 4) (Fin 4) Fv) i j + Dm i j + Qm i j) -
      (1 : Matrix (Fin 4) (Fin 4) Fv) i j) ≤ exp (-(N : ℤ)) := by
  have e : ρ * ((1 : Matrix (Fin 4) (Fin 4) Fv) i j + Dm i j + Qm i j) - (1 : Matrix (Fin 4) (Fin 4) Fv) i j =
      (ρ - 1) * (1 : Matrix (Fin 4) (Fin 4) Fv) i j + ρ * Dm i j + ρ * Qm i j := by ring
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans (max_le ?_ ?_)) ?_)
  · exact valued_mul_le_of_le' hρ1 (valued_one_apply_le i j)
  · exact valued_mul_le_of_le hρ (hD i j)
  · exact valued_mul_le_of_le hρ ((hQ i j).trans (exp_le_exp.2 (by omega)))

end Window

end QuadFormsKB.Tamagawa.Measure.Weil
