/-
# The $q$-expansion of $E_2^{\psi,\varphi,t}$
For $\varphi$ primitive modulo $v$ and $\psi(-1)\varphi(-1) = 1$ (`dsEisMF_eq_qExpansion`):
$$E_2^{\psi,\varphi,t}(z) = \psi(0)\sum_{d \in \mathbb{Z}}\frac{\bar\varphi(d)}{d^2}
  + 2\,\frac{(-2\pi i)^2\,g(\bar\varphi)}{v^2}\sum_{n \ge 1}\sigma_1^{\psi,\varphi}(n)\,q^{tn}, \qquad
  \sigma_1^{\psi,\varphi}(n) = \sum_{d \mid n}\psi(n/d)\,\varphi(d)\,d,$$
$q = e^{2\pi iz}$, $g(\bar\varphi) = \sum_{a \bmod v}\bar\varphi(a)e^{2\pi ia/v}$ (Mathlib's `gaussSum φ⁻¹ ZMod.stdAddChar`).
Here $\psi(0) = 1$ if $u = 1$ and $0$ otherwise, i.e. $\psi(0) = \delta(\psi)$ in Diamond–Shurman's notation.
Diamond–Shurman, Thm 4.5.1 (weight $k \ge 3$) and §4.6 (weight 2) [unverified locators] state
$G_k^{\psi,\varphi} = \frac{C_kg(\bar\varphi)}{v^k}\bigl(\delta(\psi)L(1-k,\varphi) + 2\sum_n\sigma_{k-1}^{\psi,\varphi}(n)q^n\bigr)$ with
$C_k = (-2\pi i)^k/(k-1)!$; the formula above is this for $k = 2$, with the constant term left as the value
$\frac{v^2}{C_2g(\bar\varphi)}\sum_d\bar\varphi(d)d^{-2}$ (which equals $L(-1,\varphi)$ by the functional equation; not
formalized here).
-/
import QuadFormsKB.Siegel.EisensteinWt2.Forms
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Complex Filter Topology ModularForm
open scoped Real UpperHalfPlane MatrixGroups

namespace QuadFormsKB.Siegel.EisensteinWt2

/-- **The twisted divisor sum** $\sigma_1^{\psi,\varphi}(n) = \sum_{d \mid n}\psi(n/d)\varphi(d)d$. -/
@[kb "diamondshurman2005" "§4.5, σ_{k-1}^{ψ,φ} (k = 2) [unverified]"]
def sigmaTw (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ d ∈ n.divisors, a (n / d) * b d * d

/-- **Twisted Lambert-series rearrangement:** for $|x| < 1$, $|a| \le A$ and $|b| \le 1$,
$\sum_{m \ge 1}a(m)\sum_{n \ge 1}b(n)\,n\,x^{mn} = \sum_{e \ge 1}\sigma^{a,b}(e)\,x^e$. -/
theorem tsum_tsum_twisted_eq {a b : ℕ → ℂ} {A : ℝ} (ha : ∀ n, ‖a n‖ ≤ A) (hb : ∀ n, ‖b n‖ ≤ 1) {x : ℂ}
    (hx : ‖x‖ < 1) :
    ∑' m : ℕ+, a m * ∑' n : ℕ+, b n * n * x ^ ((m : ℕ) * n) = ∑' e : ℕ+, sigmaTw a b e * x ^ (e : ℕ) := by
  have hxr : ‖‖x‖‖ < 1 := by rwa [norm_norm]
  have hsumR := summable_prod_mul_pow (𝕜 := ℝ) 1 hxr
  set f : ℕ+ × ℕ+ → ℂ := fun c => a c.1 * (b c.2 * c.2 * x ^ ((c.1 : ℕ) * c.2)) with hf
  have hfs : Summable f := by
    refine Summable.of_norm_bounded (hsumR.mul_left A) fun c => ?_
    simp only [hf, norm_mul, norm_pow, Complex.norm_natCast, pow_one]
    have h1 := ha c.1
    have h2 := hb c.2
    have : 0 ≤ ‖x‖ ^ ((c.1 : ℕ) * c.2) := by positivity
    have : (0 : ℝ) ≤ (c.2 : ℕ) := by positivity
    have hA : 0 ≤ A := (norm_nonneg _).trans (ha 0)
    calc ‖a c.1‖ * (‖b c.2‖ * ((c.2 : ℕ) : ℝ) * ‖x‖ ^ ((c.1 : ℕ) * c.2))
        ≤ A * (1 * ((c.2 : ℕ) : ℝ) * ‖x‖ ^ ((c.1 : ℕ) * c.2)) := by gcongr
      _ = _ := by simp
  have hlhs : ∑' m : ℕ+, a m * ∑' n : ℕ+, b n * n * x ^ ((m : ℕ) * n) = ∑' c, f c := by
    rw [hfs.tsum_prod]
    exact tsum_congr fun m => by rw [← tsum_mul_left]
  rw [hlhs, ← sigmaAntidiagonalEquivProd.tsum_eq]
  have hsig : Summable (f ∘ sigmaAntidiagonalEquivProd) := sigmaAntidiagonalEquivProd.summable_iff.mpr hfs
  rw [show (∑' c, f (sigmaAntidiagonalEquivProd c)) = ∑' c, (f ∘ sigmaAntidiagonalEquivProd) c from rfl,
    hsig.tsum_sigma]
  refine tsum_congr fun e => ?_
  rw [tsum_fintype, sigmaTw, Finset.sum_mul]
  have := (e : ℕ).divisorsAntidiagonal.sum_attach
    (fun p : ℕ × ℕ => a p.1 * (b p.2 * p.2 * x ^ (p.1 * p.2)))
  simp only [Function.comp_apply, hf, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors,
    Equiv.coe_fn_mk, PNat.mk_coe]
  rw [Finset.univ_eq_attach, this, Nat.sum_divisorsAntidiagonal' (f := fun i j => a i * (b j * j * x ^ (i * j)))]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
  ring

section DS

variable {N : ℕ} [NeZero N] {u v : ℕ} {ψ : DirichletCharacter ℂ u} {φ : DirichletCharacter ℂ v}

omit [NeZero N] in
lemma dsF_mul (M m : ℕ) (hM : M ≠ 0) (d : ℤ) :
    dsF ψ φ M ((M * m : ℕ) : ℤ) d = ψ (m : ZMod u) * φ⁻¹ (d : ZMod v) := by
  simp only [dsF, Nat.cast_mul, dvd_mul_right, ↓reduceIte]
  rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hM)]; simp

omit [NeZero N] in
lemma dsF_zero_left (M : ℕ) (d : ℤ) : dsF ψ φ M 0 d = ψ 0 * φ⁻¹ (d : ZMod v) := by
  simp [dsF]

omit [NeZero N] in
lemma dsF_of_not_dvd {M : ℕ} {c : ℤ} (hc : ¬ (M : ℤ) ∣ c) (d : ℤ) : dsF ψ φ M c d = 0 := by
  simp [dsF, hc]

omit [NeZero N] in
lemma char_neg_one_inv (χ : DirichletCharacter ℂ v) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply_eq_inv']
  have h : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  exact inv_eq_of_mul_eq_one_right h

omit [NeZero N] in
lemma dsF_neg (heven : ψ (-1) * φ (-1) = 1) (M : ℕ) (c d : ℤ) :
    dsF ψ φ M (-c) (-d) = dsF ψ φ M c d := by
  simp only [dsF, Int.cast_neg]
  by_cases hc : (M : ℤ) ∣ c
  · have hc' : (M : ℤ) ∣ -c := (dvd_neg).mpr hc
    simp only [hc, hc', ↓reduceIte]
    rw [Int.neg_ediv_of_dvd hc, Int.cast_neg, neg_eq_neg_one_mul (((c / M : ℤ)) : ZMod u),
      neg_eq_neg_one_mul (d : ZMod v), map_mul, map_mul, char_neg_one_inv]
    linear_combination (ψ ((c / M : ℤ) : ZMod u) * φ⁻¹ (d : ZMod v)) * heven
  · have hc' : ¬ (M : ℤ) ∣ -c := fun h => hc ((dvd_neg).mp h)
    simp [hc, hc']

omit [NeZero N] in
/-- The Gauss sum twisted by $e^{2\pi i nr/v}$: $\sum_{r}\bar\varphi(r)e^{2\pi inr/v} = \varphi(n)\,g(\bar\varphi)$ for
$\varphi$ primitive. -/
lemma sum_fin_inv_mul_exp [NeZero v] (hφ : φ.IsPrimitive) (n : ℕ) :
    ∑ r : Fin v, φ⁻¹ (((r : ℕ) : ℤ) : ZMod v) * cexp (2 * π * I * n * (r : ℕ) / v) =
      φ (n : ZMod v) * gaussSum φ⁻¹ ZMod.stdAddChar := by
  have hprim : (φ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hφ
  have h := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hprim (n : ZMod v)
  rw [inv_inv] at h
  rw [← h, gaussSum]
  rw [Fin.sum_univ_eq_sum_range (fun r => φ⁻¹ ((r : ℤ) : ZMod v) * cexp (2 * π * I * n * r / v)) v]
  rw [← sum_range_zmod (N := v) (fun a => φ⁻¹ a * (ZMod.stdAddChar.mulShift (n : ZMod v)) a)]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  rw [AddChar.mulShift_apply, show (n : ZMod v) * ((r : ℤ) : ZMod v) = ((n * r : ℤ) : ZMod v) by
    push_cast; ring, ZMod.stdAddChar_coe]
  push_cast; ring_nf

omit [NeZero N] in
/-- **The row $c = vtm$:** $\sum_d\psi(m)\bar\varphi(d)(vtmz + d)^{-2}
= \psi(m)\,\frac{(-2\pi i)^2g(\bar\varphi)}{v^2}\sum_{n \ge 0}n\varphi(n)\,q^{tmn}$. -/
lemma dsRow [NeZero v] (hφ : φ.IsPrimitive) {t m : ℕ} (ht : t ≠ 0) (hm : 0 < m) (z : ℍ) :
    ∑' d : ℤ, dsF ψ φ (v * t) ((v * t * m : ℕ) : ℤ) d * ((((v * t * m : ℕ) : ℂ) * z + d) ^ 2)⁻¹ =
      ψ (m : ZMod u) * ((-2 * π * I) ^ 2 / (v : ℂ) ^ 2 * gaussSum φ⁻¹ ZMod.stdAddChar) *
        ∑' n : ℕ, ((n : ℂ) * φ (n : ZMod v)) * cexp (2 * π * I * z) ^ (t * m * n) := by
  have hv0 : (v : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne v
  have hM0 : v * t ≠ 0 := mul_ne_zero (NeZero.ne v) ht
  have hterm : ∀ d : ℤ, dsF ψ φ (v * t) ((v * t * m : ℕ) : ℤ) d * ((((v * t * m : ℕ) : ℂ) * z + d) ^ 2)⁻¹ =
      ψ (m : ZMod u) * (φ⁻¹ (d : ZMod v) * ((((v * t * m : ℕ) : ℂ) * z + d) ^ 2)⁻¹) := by
    intro d; rw [dsF_mul (v * t) m hM0]; ring
  rw [tsum_congr hterm, tsum_mul_left, mul_assoc (ψ (m : ZMod u))]
  congr 1
  have hC : 0 < v * t * m := Nat.mul_pos (Nat.pos_of_ne_zero hM0) hm
  rw [row_expansion (M := v) (β := fun d : ℤ => φ⁻¹ (d : ZMod v)) (fun d => by push_cast; simp)
    (fun d => DirichletCharacter.norm_le_one _ _) hC z]
  set q := cexp (2 * π * I * z)
  have hq : ‖q‖ < 1 := by
    rw [norm_cexp_two_pi_I]; exact Real.exp_lt_one_iff.mpr (by
      have := z.im_pos; have := Real.pi_pos; simp only [UpperHalfPlane.coe_im]; nlinarith)
  have hexp : ∀ (r : Fin v) (n : ℕ),
      cexp (2 * π * I * ((((v * t * m : ℕ) : ℂ) * z + (r : ℕ)) / v)) ^ n =
        q ^ (t * m * n) * cexp (2 * π * I * n * (r : ℕ) / v) := by
    intro r n
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  have hsum : ∀ r : Fin v, Summable fun n : ℕ =>
      φ⁻¹ (((r : ℕ) : ℤ) : ZMod v) * ((n : ℂ) * (q ^ (t * m * n) * cexp (2 * π * I * n * (r : ℕ) / v))) := by
    intro r
    have hqt : ‖q ^ (t * m)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.mul_ne_zero ht hm.ne')
    refine Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := ‖q ^ (t * m)‖) (by rwa [norm_norm])) fun n => ?_
    rw [norm_mul, norm_mul, norm_mul, pow_mul, Complex.norm_natCast]
    have h1 := DirichletCharacter.norm_le_one φ⁻¹ (((r : ℕ) : ℤ) : ZMod v)
    have h2 : ‖cexp (2 * π * I * n * (r : ℕ) / v)‖ = 1 := by
      rw [Complex.norm_exp]; simp [Complex.div_re, mul_re, mul_im]
    rw [h2, pow_one, mul_one, norm_pow]
    calc ‖φ⁻¹ (((r : ℕ) : ℤ) : ZMod v)‖ * ((n : ℝ) * ‖q ^ (t * m)‖ ^ n) ≤ 1 * ((n : ℝ) * ‖q ^ (t * m)‖ ^ n) := by
          gcongr
      _ = _ := by simp
  simp_rw [hexp, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => hsum r)]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hg := sum_fin_inv_mul_exp hφ n
  calc (-2 * π * I) ^ 2 / (v : ℂ) ^ 2 * ∑ r : Fin v, φ⁻¹ (((r : ℕ) : ℤ) : ZMod v) *
        ((n : ℂ) * (q ^ (t * m * n) * cexp (2 * π * I * n * (r : ℕ) / v)))
      = (-2 * π * I) ^ 2 / (v : ℂ) ^ 2 * ((n : ℂ) * q ^ (t * m * n)) *
          ∑ r : Fin v, φ⁻¹ (((r : ℕ) : ℤ) : ZMod v) * cexp (2 * π * I * n * (r : ℕ) / v) := by
        rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => by ring
    _ = _ := by rw [hg]; ring

end DS

section General

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
lemma rowW_neg {W : ZMod N → ZMod N → ℂ} (hW : ∀ c d, wt W (-c) (-d) = wt W c d) (c : ℤ) (w : ℂ) :
    rowW W (-c) w = rowW W c w := by
  rw [rowW, rowW, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun d => ?_
  simp only [Equiv.neg_apply, hW, Int.cast_neg]
  congr 1
  ring

lemma summable_rowW (W : ZMod N → ZMod N → ℂ) (z : ℍ) : Summable fun c => rowW W c z := by
  refine Summable.of_norm_bounded_eventually (summable_rowBound (N := N) (B := wtBound W) z.im_pos) ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ℤ)).subset fun c hc => ?_
  by_contra h
  exact hc (norm_rowW_le W h z)

/-- For an even weight ($W(-c,-d) = W(c,d)$): $E_W = (\text{row } 0) + 2\sum_{c \ge 1}(\text{row } c)$. -/
lemma eis2_eq_row0_add {W : ZMod N → ZMod N → ℂ} (hW : ∀ c d, wt W (-c) (-d) = wt W c d) (z : ℍ) :
    eis2 W z = rowW W 0 z + 2 * ∑' c : ℕ+, rowW W ((c : ℕ) : ℤ) z := by
  have hs := summable_rowW W z
  set f : ℤ → ℂ := fun c => rowW W c z with hf
  have h1 : Summable fun n : ℕ => f (n : ℤ) := hs.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ => f (-((n : ℤ) + 1)) :=
    hs.comp_injective fun a b h => by simpa using h
  have h3 : ∀ n : ℕ, f (-((n : ℤ) + 1)) = f ((n + 1 : ℕ) : ℤ) := fun n => by
    simp only [hf]; rw [rowW_neg hW]; push_cast; rfl
  have e1 : eis2 W z = ∑' n : ℕ, f (n : ℤ) + ∑' n : ℕ, f (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one h1 h2
  have e2 : ∑' n : ℕ, f (-((n : ℤ) + 1)) = ∑' n : ℕ, f ((n + 1 : ℕ) : ℤ) := tsum_congr h3
  have e3 : ∑' n : ℕ, f (n : ℤ) = f ((0 : ℕ) : ℤ) + ∑' n : ℕ, f ((n + 1 : ℕ) : ℤ) :=
    h1.tsum_eq_zero_add
  have e4 : ∑' c : ℕ+, f ((c : ℕ) : ℤ) = ∑' n : ℕ, f ((n + 1 : ℕ) : ℤ) :=
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => f (n : ℤ))
  change eis2 W z = f 0 + 2 * ∑' c : ℕ+, f ((c : ℕ) : ℤ)
  rw [e1, e2, e3, e4, Nat.cast_zero]
  ring

end General

section DSq

variable {N : ℕ} [NeZero N] {u v : ℕ} {ψ : DirichletCharacter ℂ u} {φ : DirichletCharacter ℂ v}

/-- **The $q$-expansion of $E_2^{\psi,\varphi,t}$** ($\varphi$ primitive, $\psi\varphi$ even, $t \ge 1$):
$$E_2^{\psi,\varphi,t}(z) = \psi(0)\sum_{d}\frac{\bar\varphi(d)}{d^2} + 2\,\frac{(-2\pi i)^2g(\bar\varphi)}{v^2}
  \sum_{e \ge 1}\sigma_1^{\psi,\varphi}(e)\,q^{te}, \qquad q = e^{2\pi iz}.$$ -/
@[kb "diamondshurman2005" "Thm 4.5.1 / §4.6 (q-expansion of G_2^{ψ,φ}) [unverified]"]
theorem dsEisMF_eq_qExpansion [NeZero v] (hφ : φ.IsPrimitive) (heven : ψ (-1) * φ (-1) = 1)
    {t : ℕ} (ht : t ≠ 0) (hN : u * (v * t) ∣ N) (hne : ψ ≠ 1 ∨ φ ≠ 1) (z : ℍ) :
    dsEisMF ψ φ t hN hne z =
      ψ 0 * ∑' d : ℤ, φ⁻¹ (d : ZMod v) * ((d : ℂ) ^ 2)⁻¹ +
        2 * ((-2 * π * I) ^ 2 / (v : ℂ) ^ 2 * gaussSum φ⁻¹ ZMod.stdAddChar) *
          ∑' e : ℕ+, sigmaTw (fun n => ψ (n : ZMod u)) (fun n => φ (n : ZMod v)) e *
            (cexp (2 * π * I * z) ^ t) ^ (e : ℕ) := by
  have hper := dsF_periodic (ψ := ψ) (φ := φ) hN
  have hM0 : v * t ≠ 0 := mul_ne_zero (NeZero.ne v) ht
  have hwt : ∀ c d, wt (dsW (N := N) ψ φ t) c d = dsF ψ φ (v * t) c d := wt_ofPer hper.1 hper.2
  have heven' : ∀ c d, wt (dsW (N := N) ψ φ t) (-c) (-d) = wt (dsW (N := N) ψ φ t) c d := by
    intro c d; rw [hwt, hwt, dsF_neg heven]
  change eis2 (dsW ψ φ t) z = _
  rw [eis2_eq_row0_add heven' z]
  congr 1
  · -- the constant term
    simp only [rowW, hwt, dsF_zero_left, Int.cast_zero, zero_mul, zero_add]
    rw [← tsum_mul_left]
    exact tsum_congr fun d => by ring
  · -- only rows c = vtm contribute
    set K := (-2 * π * I) ^ 2 / (v : ℂ) ^ 2 * gaussSum φ⁻¹ ZMod.stdAddChar
    let g : ℕ+ → ℕ+ := fun m => ⟨v * t * m, Nat.mul_pos (Nat.pos_of_ne_zero hM0) m.pos⟩
    have hsupp : Function.support (fun c : ℕ+ => rowW (dsW (N := N) ψ φ t) ((c : ℕ) : ℤ) z) ⊆
        Set.range g := by
      intro c hc
      by_contra hcr
      apply hc
      have hnd : ¬ ((v * t : ℕ) : ℤ) ∣ ((c : ℕ) : ℤ) := by
        rintro ⟨k, hk⟩
        have hk0 : 0 < k := by
          have : (0 : ℤ) < (c : ℕ) := by exact_mod_cast c.pos
          rw [hk] at this
          exact pos_of_mul_pos_right this (by positivity)
        apply hcr
        have : ((c : ℕ) : ℤ) = ((v * t * k.toNat : ℕ) : ℤ) := by
          rw [hk]; push_cast; rw [Int.toNat_of_nonneg hk0.le]
        have h' : v * t * k.toNat = (c : ℕ) := by exact_mod_cast this.symm
        exact ⟨⟨k.toNat, by omega⟩, PNat.eq (by simp only [g, PNat.mk_coe]; exact h')⟩
      simp only [rowW, hwt, dsF_of_not_dvd hnd, zero_mul, tsum_zero]
    have hginj : Function.Injective g := fun a b h => by
      have h' := congr_arg (fun x : ℕ+ => (x : ℕ)) h
      simp only [g, PNat.mk_coe] at h'
      exact PNat.eq (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hM0) h')
    rw [← hginj.tsum_eq hsupp]
    have hrow : ∀ m : ℕ+, rowW (dsW (N := N) ψ φ t) (((g m : ℕ+) : ℕ) : ℤ) z =
        ψ ((m : ℕ) : ZMod u) * K * ∑' n : ℕ, ((n : ℂ) * φ (n : ZMod v)) *
          cexp (2 * π * I * z) ^ (t * m * n) := by
      intro m
      have := dsRow (ψ := ψ) hφ ht m.pos z
      simp only [rowW, hwt]
      exact this
    simp_rw [hrow]
    set q := cexp (2 * π * I * z)
    have hq : ‖q‖ < 1 := by
      rw [norm_cexp_two_pi_I]; exact Real.exp_lt_one_iff.mpr (by
        have := z.im_pos; have := Real.pi_pos; simp only [UpperHalfPlane.coe_im]; nlinarith)
    have hqt : ‖q ^ t‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq ht
    have hinner : ∀ m : ℕ+, ∑' n : ℕ, ((n : ℂ) * φ (n : ZMod v)) * q ^ (t * m * n) =
        ∑' n : ℕ+, φ ((n : ℕ) : ZMod v) * (n : ℕ) * (q ^ t) ^ ((m : ℕ) * n) := by
      intro m
      have hs : Summable fun n : ℕ => ((n : ℂ) * φ (n : ZMod v)) * q ^ (t * m * n) := by
        have hqm : ‖q ^ (t * m)‖ < 1 := by
          rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.mul_ne_zero ht m.ne_zero)
        refine Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (r := ‖q ^ (t * m)‖) (by rwa [norm_norm])) fun n => ?_
        rw [norm_mul, norm_mul, Complex.norm_natCast, pow_mul, norm_pow, pow_one]
        have := DirichletCharacter.norm_le_one φ (n : ZMod v)
        calc (n : ℝ) * ‖φ (n : ZMod v)‖ * ‖q ^ (t * m)‖ ^ n ≤ (n : ℝ) * 1 * ‖q ^ (t * m)‖ ^ n := by
              gcongr
          _ = _ := by ring
      rw [← tsum_zero_pnat_eq_tsum_nat hs]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      refine tsum_congr fun n => ?_
      rw [← pow_mul]; ring_nf
    simp_rw [hinner]
    have htw := tsum_tsum_twisted_eq (a := fun n => ψ (n : ZMod u)) (b := fun n => φ (n : ZMod v))
      (fun n => DirichletCharacter.norm_le_one _ _) (fun n => DirichletCharacter.norm_le_one _ _) hqt
    rw [← htw, mul_assoc 2 K, ← tsum_mul_left (a := K)]
    congr 1
    exact tsum_congr fun m => by ring

end DSq

end QuadFormsKB.Siegel.EisensteinWt2
