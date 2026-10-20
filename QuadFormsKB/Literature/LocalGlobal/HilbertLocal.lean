/-
# The local Hilbert symbol over $\mathbb{Q}_p$ (Serre, *A Course in Arithmetic*, II–III)

The steps toward Hilbert reciprocity $\prod_v (a,b)_v = 1$ (`hilbert_product_formula`). Every element of $\mathbb{Q}_p^\times$ is $p^k u$ with $k \in \mathbb{Z}$ and $u$ a
$p$-adic unit, so everything is stated for such products.

* squares in $\mathbb{Q}_p$: for $p$ odd via the residue of $u$ in $\mathbb{F}_p$; for
  $p = 2$ via $u \bmod 8$;
* $(u, v)_p = 1$ for units, $p$ odd;
* the explicit formulas for $(a,b)_p$: $p$ odd and $p = 2$;
* $(a,b)_p = 1$ for almost all $p$.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Defs.Hilbert

namespace QuadFormsKB.HilbertLocal

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The residue character of a $p$-adic unit:** for $u \in \mathbb{Z}_p^\times$,
$\left(\frac{u}{p}\right) \in \{1, -1\}$, the quadratic character of the residue
$\bar u \in \mathbb{F}_p^\times$ ($1$ iff $\bar u$ is a square in $\mathbb{F}_p$). -/
noncomputable def unitChar (u : ℤ_[p]ˣ) : ℤ :=
  quadraticChar (ZMod p) (PadicInt.toZMod (u : ℤ_[p]))

/-! ### Squares in $\mathbb{Q}_p$, $p$ odd -/

/-- **A $p$-adic unit is a square in $\mathbb{Q}_p$ iff its residue is a square in
$\mathbb{F}_p$** ($p$ odd; Hensel's lemma). -/
@[kb "serre1973" "Ch. II §3.3, Thm. 3 [unverified]"]
theorem isSquare_unit_iff (hp2 : p ≠ 2) (u : ℤ_[p]ˣ) :
    IsSquare ((u : ℤ_[p]) : ℚ_[p]) ↔ IsSquare (PadicInt.toZMod (u : ℤ_[p])) := by
  constructor
  · rintro ⟨x, hx⟩
    have hu : ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1 := by
      rw [PadicInt.norm_coe]; exact (PadicInt.isUnit_iff).mp u.isUnit
    have hx1 : ‖x‖ = 1 := by
      rw [hx, norm_mul] at hu
      nlinarith [norm_nonneg x]
    obtain ⟨w, hwx⟩ : ∃ w : ℤ_[p], (w : ℚ_[p]) = x := ⟨⟨x, hx1.le⟩, rfl⟩
    have this : (u : ℤ_[p]) = w * w := by
      apply PadicInt.ext
      rw [PadicInt.coe_mul, hwx]
      exact hx
    refine ⟨PadicInt.toZMod w, ?_⟩
    rw [this, map_mul]
  · rintro ⟨y, hy⟩
    set a : ℤ_[p] := (y.val : ℤ_[p])
    have ha : PadicInt.toZMod a = y := by simp [a]
    let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[p])
    have h1 : ‖F.aeval a‖ < 1 := by
      have : F.aeval a ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
        rw [RingHom.mem_ker]; simp [F, ha, hy, sq]
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
      exact this
    have h2 : ‖F.derivative.aeval a‖ = 1 := by
      rw [← PadicInt.isUnit_iff, ← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod,
        RingHom.mem_ker]
      have hy0 : y ≠ 0 := by
        rintro rfl
        have := (Units.map (PadicInt.toZMod (p := p)).toMonoidHom u).isUnit
        simp [hy] at this
      have h20 : (2 : ZMod p) ≠ 0 := by
        intro h
        have h' := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
        have := Nat.le_of_dvd (by norm_num) h'
        have := (Fact.out : p.Prime).two_le; omega
      simp [F, ha, hy0]
      rw [one_add_one_eq_two]; exact h20
    obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [h2]; simpa using h1)
    refine ⟨(z : ℚ_[p]), ?_⟩
    have : z * z = (u : ℤ_[p]) := by
      simp [F, sub_eq_zero, sq] at hz; exact hz
    rw [← this]; push_cast; rfl

/-- **Squares in $\mathbb{Q}_p^\times$, $p$ odd:** $p^k u$ (with $u$ a unit, $k \in \mathbb{Z}$) is a
square in $\mathbb{Q}_p$ iff $k$ is even and the residue of $u$ is a square in $\mathbb{F}_p$. -/
@[kb "serre1973" "Ch. II §3.3, Thm. 3 [unverified]"]
theorem isSquare_zpow_mul_unit_iff (hp2 : p ≠ 2) (k : ℤ) (u : ℤ_[p]ˣ) :
    IsSquare ((p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p])) ↔
      Even k ∧ IsSquare (PadicInt.toZMod (u : ℤ_[p])) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpos : (0 : ℝ) < p := by linarith
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hu1 : ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp u.isUnit
  have key : ∀ z : ℤ_[p], ‖z‖ < 1 ↔ PadicInt.toZMod z = 0 := by
    intro z
    rw [← PadicInt.mem_nonunits, ← RingHom.mem_ker, PadicInt.ker_toZMod]
    rfl
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hx
      rcases mul_eq_zero.mp hx with h | h
      · exact zpow_ne_zero k hpne h
      · rw [h, norm_zero] at hu1; exact zero_ne_one hu1
    have hn := congrArg norm hx
    rw [norm_mul, norm_mul, hu1, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx0,
      mul_one, ← zpow_add₀ hpos.ne'] at hn
    have hk : -x.valuation + -x.valuation = -k :=
      zpow_right_injective₀ hpos hp1.ne' (show (p:ℝ) ^ (-x.valuation + -x.valuation) = (p:ℝ) ^ (-k) from hn.symm)
    have hk' : k = x.valuation + x.valuation := by linarith
    refine ⟨⟨x.valuation, hk'⟩, ?_⟩
    set y : ℚ_[p] := x * (p : ℚ_[p]) ^ (-x.valuation) with hy
    have hyn : ‖y‖ = 1 := by
      rw [hy, norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx0,
        ← zpow_add₀ hpos.ne']
      simp
    let y' : ℤ_[p] := ⟨y, hyn.le⟩
    have hyy : y' * y' = (u : ℤ_[p]) := by
      apply Subtype.ext
      show y * y = ((u : ℤ_[p]) : ℚ_[p])
      rw [hy]
      have : x * (p : ℚ_[p]) ^ (-x.valuation) * (x * (p : ℚ_[p]) ^ (-x.valuation))
          = (x * x) * ((p : ℚ_[p]) ^ k)⁻¹ := by
        rw [hk', zpow_add₀ hpne, zpow_neg]; ring
      rw [this, ← hx]
      field_simp
    exact ⟨PadicInt.toZMod y', by rw [← map_mul, hyy]⟩
  · rintro ⟨⟨m, rfl⟩, ⟨a, ha⟩⟩
    set b : ℤ_[p] := ((a.val : ℕ) : ℤ_[p]) with hb
    have hba : PadicInt.toZMod b = a := by simp [hb]
    have ha0 : a ≠ 0 := by
      rintro rfl
      have := key (u : ℤ_[p])
      rw [PadicInt.norm_def, hu1] at this
      simp at this; rw [mul_zero] at ha; exact this ha
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
    obtain ⟨z, hz, -⟩ := hensels_lemma (F := Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[p])) (a := b) (by
      have e1 : ‖Polynomial.aeval b (Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[p]))‖ < 1 := by
        rw [key]; simp [hba, ha]; ring
      have e2 : ‖Polynomial.aeval b (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[p])))‖ = 1 := by
        have := key (Polynomial.aeval b (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[p]))))
        have hle := PadicInt.norm_le_one (Polynomial.aeval b (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[p]))))
        by_contra hne
        have : PadicInt.toZMod (Polynomial.aeval b (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[p])))) = 0 := this.mp (lt_of_le_of_ne hle hne)
        simp [hba] at this
        rcases this with h | h
        · exact h2 (by rw [← h]; norm_num)
        · exact ha0 h
      rw [e2]; simpa using e1)
    simp at hz
    refine ⟨(p : ℚ_[p]) ^ m * (z : ℚ_[p]), ?_⟩
    have : (z : ℚ_[p]) ^ 2 = ((u : ℤ_[p]) : ℚ_[p]) := by
      rw [← PadicInt.coe_pow, sub_eq_zero.mp hz]
    rw [zpow_add₀ hpne, ← this]; ring

/-! ### Squares in $\mathbb{Q}_2$ -/

/-- **A $2$-adic unit is a square in $\mathbb{Q}_2$ iff it is $\equiv 1 \pmod 8$.** -/
@[kb "serre1973" "Ch. II §3.3, Thm. 4 [unverified]"]
theorem isSquare_two_adic_unit_iff (u : ℤ_[2]ˣ) :
    IsSquare ((u : ℤ_[2]) : ℚ_[2]) ↔ PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 := by
  have key : ∀ y : ZMod (2^3), IsUnit y → y^2 = 1 := by decide
  constructor
  · rintro ⟨x, hx⟩
    have hu : ‖((u : ℤ_[2]) : ℚ_[2])‖ = 1 := by
      rw [PadicInt.norm_coe]; exact (PadicInt.isUnit_iff).1 u.isUnit
    have hx1 : ‖x‖ = 1 := by
      rw [hx, norm_mul] at hu
      nlinarith [norm_nonneg x]
    set y : ℤ_[2] := ⟨x, hx1.le⟩
    have hy : IsUnit y := PadicInt.isUnit_iff.2 hx1
    have huy : (u : ℤ_[2]) = y ^ 2 := by
      apply Subtype.ext
      show ((u:ℤ_[2]):ℚ_[2]) = ((y^2 : ℤ_[2]) : ℚ_[2])
      rw [PadicInt.coe_pow, hx, sq]
    rw [huy, map_pow]
    exact key _ (hy.map _)
  · intro h
    have hmem : (u : ℤ_[2]) - 1 ∈ Ideal.span {((2:ℕ) : ℤ_[2]) ^ 3} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, map_one, sub_self]
    have hn := (PadicInt.norm_le_pow_iff_mem_span_pow _ 3).2 hmem
    have h2 : ‖(2 : ℤ_[2])‖ = 1/2 := by
      have := PadicInt.norm_p (p := 2)
      simpa using this
    obtain ⟨z, hz, -⟩ := hensels_lemma (p := 2) (R := ℤ_[2])
      (F := Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[2])) (a := 1) (by
        simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
          Polynomial.derivative_X_pow, Polynomial.derivative_C]
        simp
        rw [norm_sub_rev, h2]
        refine lt_of_le_of_lt hn ?_
        norm_num)
    refine ⟨(z : ℚ_[2]), ?_⟩
    simp at hz
    rw [← PadicInt.coe_mul, ← sq, sub_eq_zero.1 hz]

/-- **Squares in $\mathbb{Q}_2^\times$:** $2^k u$ is a square iff $k$ is even and $u \equiv 1 \pmod 8$. -/
@[kb "serre1973" "Ch. II §3.3, Thm. 4 [unverified]"]
theorem isSquare_two_zpow_mul_unit_iff (k : ℤ) (u : ℤ_[2]ˣ) :
    IsSquare ((2 : ℚ_[2]) ^ k * ((u : ℤ_[2]) : ℚ_[2])) ↔
      Even k ∧ PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 := by
  have hu1 : ‖((u : ℤ_[2]) : ℚ_[2])‖ = 1 := by
    rw [PadicInt.norm_coe]
    exact PadicInt.isUnit_iff.mp u.isUnit
  have h2n : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
    have := Padic.norm_p (p := 2)
    simpa using this
  have h20 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : ((u : ℤ_[2]) : ℚ_[2]) ≠ 0 := by
        intro h0; rw [h0] at hu1; simp at hu1
      simp only [mul_zero, mul_eq_zero, zpow_ne_zero _ h20, false_or] at hy
      exact this hy
    set v := y.valuation with hv
    have hyn : ‖y‖ = 2 ^ (-v) := by
      have := Padic.norm_eq_zpow_neg_valuation hy0
      exact_mod_cast this
    have hnorm := congrArg norm hy
    rw [norm_mul, norm_mul, norm_zpow, hu1, h2n, hyn, mul_one, inv_zpow', ← zpow_add₀ (by norm_num)] at hnorm
    have hk : -k = -v + -v := zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) hnorm
    have hk' : k = v + v := by omega
    refine ⟨⟨v, hk'⟩, ?_⟩
    set z := y * 2 ^ (-v) with hz
    have hzn : ‖z‖ = 1 := by
      rw [hz, norm_mul, norm_zpow, h2n, hyn, inv_zpow', neg_neg, ← zpow_add₀ (by norm_num)]
      simp
    have hyz : y = z * 2 ^ v := by
      rw [hz, mul_assoc, ← zpow_add₀ h20]; simp
    have huz : ((u : ℤ_[2]) : ℚ_[2]) = z * z := by
      rw [hyz, hk', zpow_add₀ h20] at hy
      have h2v : (2 : ℚ_[2]) ^ v ≠ 0 := zpow_ne_zero _ h20
      apply mul_left_cancel₀ (mul_ne_zero h2v h2v)
      linear_combination hy
    set z' : ℤ_[2] := ⟨z, hzn.le⟩
    have huz' : (u : ℤ_[2]) = z' * z' := by
      apply Subtype.ext
      simpa using huz
    have key : ∀ a b : ZMod (2^3), a * b = 1 → a^2 = 1 := by decide
    have hinv : PadicInt.toZModPow 3 (u : ℤ_[2]) * PadicInt.toZModPow 3 ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [huz', map_mul] at hinv ⊢
    rw [← sq]
    exact key _ (PadicInt.toZModPow 3 z' * PadicInt.toZModPow 3 ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) (by rw [← hinv]; ring)
  · rintro ⟨⟨m, rfl⟩, h⟩
    have hk : (u : ℤ_[2]) - 1 ∈ RingHom.ker (PadicInt.toZModPow 3) := by
      rw [RingHom.mem_ker, map_sub, h, map_one, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
    obtain ⟨c, hc⟩ := hk
    have hn : ‖(u : ℤ_[2]) - 1‖ < 2⁻¹ ^ 2 := by
      rw [hc, norm_mul, PadicInt.norm_p_pow]
      have := PadicInt.norm_le_one c
      have h0 : (0:ℝ) ≤ 2 ^ (-(3:ℤ)) := by positivity
      have : (2:ℝ) ^ (-(3:ℤ)) < (2⁻¹)^2 := by norm_num
      push_cast
      nlinarith
    obtain ⟨z, hz, -⟩ := hensels_lemma (p := 2) (F := (Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[2]))) (a := 1) (by
      simp
      have h2 : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
        have := PadicInt.norm_p (p := 2)
        simpa using this
      rw [one_add_one_eq_two, h2, norm_sub_rev]
      convert hn using 2)
    have hzu : z * z = (u : ℤ_[2]) := by
      simp at hz
      linear_combination hz
    refine ⟨2 ^ m * (z : ℚ_[2]), ?_⟩
    rw [← hzu, PadicInt.coe_mul, zpow_add₀ h20]
    ring

/-! ### Units, $p$ odd -/

/-- **$(u, v)_p = 1$ for $p$-adic units, $p$ odd:** the conic $z^2 = u x^2 + v y^2$ has an
$\mathbb{F}_p$-point (Chevalley–Warning) that lifts to $\mathbb{Q}_p$ (Hensel). -/
@[kb "serre1973" "Ch. III §1.2 [unverified]"]
theorem hilbertSymbol_units (hp2 : p ≠ 2) (u v : ℤ_[p]ˣ) :
    hilbertSymbol ℚ_[p] ((u : ℤ_[p]) : ℚ_[p]) ((v : ℤ_[p]) : ℚ_[p]) = 1 := by
  classical
  open Polynomial in
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact (hp.out.eq_one_or_self_of_dvd 2 |>.mt (by omega) |> fun h => by
      rcases hp.out.eq_two_or_odd with h' | h' <;> omega)
  have hu : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := by
    intro h; exact (Units.isUnit u).map PadicInt.toZMod |>.ne_zero h
  have hv : PadicInt.toZMod (v : ℤ_[p]) ≠ 0 := by
    intro h; exact (Units.isUnit v).map PadicInt.toZMod |>.ne_zero h
  obtain ⟨x0, y0, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C (PadicInt.toZMod (u : ℤ_[p])) * Polynomial.X^2)
    (g := Polynomial.C (PadicInt.toZMod (v : ℤ_[p])) * Polynomial.X^2 - 1)
    (by compute_degree!) (by compute_degree!) hodd
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one] at hxy
  set x : ℤ_[p] := (x0.val : ℤ_[p])
  set y : ℤ_[p] := (y0.val : ℤ_[p])
  set c : ℤ_[p] := (u : ℤ_[p]) * x^2 + (v : ℤ_[p]) * y^2 with hc
  have hc1 : PadicInt.toZMod c = 1 := by
    simp only [c, x, y, map_add, map_mul, map_pow, map_natCast, ZMod.natCast_zmod_val]
    linear_combination hxy
  have hcn : ‖c - 1‖ < 1 := by
    have : c - 1 ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [RingHom.mem_ker, map_sub, hc1, map_one, sub_self]
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
    exact this
  have h2 : ‖(2 : ℤ_[p])‖ = 1 := by
    have := (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).2
      ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
    exact_mod_cast this
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := p)
    (F := (Polynomial.X^2 - Polynomial.C c : Polynomial ℤ_[p])) (a := 1) (by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Polynomial.derivative_X_pow, Polynomial.derivative_C]
    simp
    rw [norm_sub_rev, h2]; simpa using hcn)
  have hz2 : z ^ 2 = c := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at hz
    exact sub_eq_zero.mp (by simpa using hz)
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0] at hc1; simp at hc1
  unfold hilbertSymbol
  rw [if_pos]
  refine ⟨(x : ℚ_[p]), (y : ℚ_[p]), (z : ℚ_[p]), ?_, ?_⟩
  · intro h
    simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h
    have hz0 : z = 0 := by simpa using h.2.2
    apply hc0; rw [← hz2, hz0]; ring
  · have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz2
    simp only [c] at this
    push_cast at this
    exact this

/-! ### The explicit formula, $p$ odd -/

/-- **The Hilbert symbol over $\mathbb{Q}_p$, $p$ odd:** for $a = p^\alpha u$, $b = p^\beta v$
with $u, v \in \mathbb{Z}_p^\times$ and $\alpha, \beta \ge 0$,
$$(a, b)_p = (-1)^{\alpha \beta \varepsilon(p)} \left(\frac{u}{p}\right)^{\beta}
\left(\frac{v}{p}\right)^{\alpha}, \qquad \varepsilon(p) = \tfrac{p-1}{2}.$$
(Negative exponents reduce to these, since the symbol depends only on square classes.) -/
@[kb "serre1973" "Ch. III §1.2, Thm. 1 [unverified]"]
theorem hilbertSymbol_odd_formula (hp2 : p ≠ 2) (α β : ℕ) (u v : ℤ_[p]ˣ) :
    hilbertSymbol ℚ_[p] ((p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p]))
        ((p : ℚ_[p]) ^ β * ((v : ℤ_[p]) : ℚ_[p])) =
      (-1) ^ (α * β * ((p - 1) / 2)) * unitChar u ^ β * unitChar v ^ α := by
  have hilbertSymbol_comm : ∀ (K : Type) [Field K] (a b : K), hilbertSymbol K a b = hilbertSymbol K b a := by
    intro K _ a b; unfold hilbertSymbol; congr 1; apply propext; constructor <;>
    · rintro ⟨x, y, z, hne, heq⟩
      refine ⟨y, x, z, ?_, by rw [heq]; ring⟩
      intro h; apply hne; simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h ⊢; tauto
  have key : ∀ x : ℤ_[p], PadicInt.toZMod x = 0 → ‖x‖ < 1 := by
    intro x hx
    have : x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := hx
    rw [PadicInt.ker_toZMod] at this
    have := (IsLocalRing.mem_maximalIdeal x).mp this
    rw [mem_nonunits_iff, PadicInt.isUnit_iff] at this
    exact lt_of_le_of_ne (PadicInt.norm_le_one x) this
  have hdvd : ∀ x : ℤ_[p], PadicInt.toZMod x = 0 → ∃ y, x = (p : ℤ_[p]) * y := by
    intro x hx
    exact (PadicInt.norm_lt_one_iff_dvd x).mp (key x hx)
  have hsq : ∀ (w : ℤ_[p]) (t : ZMod p), t ≠ 0 → PadicInt.toZMod w = t ^ 2 → ∃ s : ℤ_[p], s ^ 2 = w := by
    intro w t ht hw
    obtain ⟨a, ha⟩ : ∃ a : ℤ_[p], PadicInt.toZMod a = t := ⟨(t.val : ℤ_[p]), by simp⟩
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have := Nat.le_of_dvd (by norm_num) h'
      have := (Fact.out : p.Prime).two_le
      omega
    have hunit : ‖(2 * a : ℤ_[p])‖ = 1 := by
      rw [← PadicInt.isUnit_iff]
      by_contra hc
      have hm : (2 * a) ∈ IsLocalRing.maximalIdeal ℤ_[p] := hc
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_mul, ha, map_ofNat] at hm
      rcases mul_eq_zero.mp hm with h | h
      · exact h2 h
      · exact ht h
    obtain ⟨z, hz, -⟩ := hensels_lemma (R := ℤ_[p]) (F := Polynomial.X ^ 2 - Polynomial.C w) (a := a) (by
      have : ‖(a ^ 2 - w : ℤ_[p])‖ < 1 := key _ (by simp [ha, hw])
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        Polynomial.derivative_X_pow, Polynomial.derivative_C]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_zero, sub_zero, Polynomial.aeval_C]
      norm_num [hunit]
      exact this)
    exact ⟨z, by simpa [sub_eq_zero] using hz⟩
  have hred : ∀ (a b c : ℚ_[p]), c ≠ 0 → hilbertSymbol ℚ_[p] (c ^ 2 * a) b = hilbertSymbol ℚ_[p] a b := by
    intro a b c hc
    unfold hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨x, y, z, hne, heq⟩
      refine ⟨c * x, y, z, ?_, by rw [heq]; ring⟩
      intro h
      apply hne
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, mul_eq_zero, hc, false_or] at h ⊢
      exact h
    · rintro ⟨x, y, z, hne, heq⟩
      refine ⟨x / c, y, z, ?_, by rw [heq]; field_simp⟩
      intro h
      apply hne
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, div_eq_zero_iff, hc, or_false] at h ⊢
      exact h
  have hprim : ∀ A B : ℤ_[p], (∃ x y z : ℚ_[p], (x, y, z) ≠ 0 ∧ z ^ 2 = (A : ℚ_[p]) * x ^ 2 + (B : ℚ_[p]) * y ^ 2) →
      ∃ x y z : ℤ_[p], (PadicInt.toZMod x ≠ 0 ∨ PadicInt.toZMod y ≠ 0 ∨ PadicInt.toZMod z ≠ 0) ∧
        z ^ 2 = A * x ^ 2 + B * y ^ 2 := by
    rintro A B ⟨x, y, z, hne, heq⟩
    have gen : ∀ c : ℚ_[p], ‖x‖ ≤ ‖c‖ → ‖y‖ ≤ ‖c‖ → ‖z‖ ≤ ‖c‖ → (c = x ∨ c = y ∨ c = z) →
        ∃ x y z : ℤ_[p], (PadicInt.toZMod x ≠ 0 ∨ PadicInt.toZMod y ≠ 0 ∨ PadicInt.toZMod z ≠ 0) ∧
          z ^ 2 = A * x ^ 2 + B * y ^ 2 := by
      intro c hx hy hz hcs
      have hc : c ≠ 0 := by
        rintro rfl
        apply hne
        simp only [norm_zero, norm_le_zero_iff] at hx hy hz
        simp [hx, hy, hz]
      have hx' : ‖x / c‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hx (norm_nonneg _)
      have hy' : ‖y / c‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hy (norm_nonneg _)
      have hz' : ‖z / c‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hz (norm_nonneg _)
      refine ⟨⟨x / c, hx'⟩, ⟨y / c, hy'⟩, ⟨z / c, hz'⟩, ?_, ?_⟩
      · rcases hcs with h | h | h
        · left
          have e : (⟨x / c, hx'⟩ : ℤ_[p]) = (1 : ℤ_[p]) := PadicInt.ext (by
            show x / c = 1
            subst h; exact div_self hc)
          rw [e, map_one]
          exact one_ne_zero
        · right; left
          have e : (⟨y / c, hy'⟩ : ℤ_[p]) = (1 : ℤ_[p]) := PadicInt.ext (by
            show y / c = 1
            subst h; exact div_self hc)
          rw [e, map_one]
          exact one_ne_zero
        · right; right
          have e : (⟨z / c, hz'⟩ : ℤ_[p]) = (1 : ℤ_[p]) := PadicInt.ext (by
            show z / c = 1
            subst h; exact div_self hc)
          rw [e, map_one]
          exact one_ne_zero
      · apply PadicInt.ext
        simp only [PadicInt.coe_add, PadicInt.coe_mul]
        show (z / c) ^ 2 = (A : ℚ_[p]) * (x / c) ^ 2 + (B : ℚ_[p]) * (y / c) ^ 2
        rw [div_pow, heq]
        field_simp
    rcases le_total ‖x‖ ‖y‖ with h1 | h1 <;> rcases le_total ‖y‖ ‖z‖ with h2 | h2 <;>
      rcases le_total ‖x‖ ‖z‖ with h3 | h3 <;>
      first
      | exact gen x (by linarith) (by linarith) (by linarith) (Or.inl rfl)
      | exact gen y (by linarith) (by linarith) (by linarith) (Or.inr (Or.inl rfl))
      | exact gen z (by linarith) (by linarith) (by linarith) (Or.inr (Or.inr rfl))
  have hune : ∀ u : ℤ_[p]ˣ, PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := fun u => (u.isUnit.map _).ne_zero
  have hTp : PadicInt.toZMod (p : ℤ_[p]) = 0 := by simp
  have hpne : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h <;> omega
  have h00 : ∀ u v : ℤ_[p]ˣ, hilbertSymbol ℚ_[p] ((u : ℤ_[p]) : ℚ_[p]) ((v : ℤ_[p]) : ℚ_[p]) = 1 := by
    intro u v
    unfold hilbertSymbol
    rw [if_pos]
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := ZMod p)
      (f := Polynomial.C (PadicInt.toZMod (u : ℤ_[p])) * Polynomial.X ^ 2)
      (g := Polynomial.C (PadicInt.toZMod (v : ℤ_[p])) * Polynomial.X ^ 2 - 1)
      (Polynomial.degree_C_mul_X_pow 2 (hune u)) (by
        rw [Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_C_mul_X_pow 2 (hune v)]
        · rfl
        · rw [Polynomial.degree_C_mul_X_pow 2 (hune v), Polynomial.degree_one]
          norm_num)
      (by rw [ZMod.card]; exact hodd)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one] at hab
    set x0 : ℤ_[p] := (a.val : ℤ_[p])
    set y0 : ℤ_[p] := (b.val : ℤ_[p])
    have hw : PadicInt.toZMod ((u : ℤ_[p]) * x0 ^ 2 + (v : ℤ_[p]) * y0 ^ 2) = 1 ^ 2 := by
      simp only [x0, y0, map_add, map_mul, map_pow, map_natCast, ZMod.natCast_zmod_val]
      linear_combination hab
    obtain ⟨s, hs⟩ := hsq _ 1 one_ne_zero hw
    refine ⟨(x0 : ℚ_[p]), (y0 : ℚ_[p]), (s : ℚ_[p]), ?_, ?_⟩
    · intro h
      have hs0 : (s : ℚ_[p]) = 0 := by simp only [Prod.ext_iff] at h; exact h.2.2
      have : s = 0 := PadicInt.ext hs0
      rw [← hs, this] at hw
      simp at hw
    · have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hs
      simp only [PadicInt.coe_pow, PadicInt.coe_add, PadicInt.coe_mul] at this
      rw [this]
  have h10 : ∀ u v : ℤ_[p]ˣ, hilbertSymbol ℚ_[p] ((p : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]))
      ((v : ℤ_[p]) : ℚ_[p]) = unitChar v := by
    intro u v
    show _ = quadraticChar (ZMod p) (PadicInt.toZMod (v : ℤ_[p]))
    by_cases hsv : IsSquare (PadicInt.toZMod (v : ℤ_[p]))
    · rw [(quadraticChar_one_iff_isSquare (hune v)).mpr hsv]
      obtain ⟨t, ht⟩ := hsv
      have ht0 : t ≠ 0 := by rintro rfl; exact hune v (by simpa using ht)
      obtain ⟨s, hs⟩ := hsq _ t ht0 (by rw [ht]; ring)
      unfold hilbertSymbol; rw [if_pos]
      refine ⟨0, 1, (s : ℚ_[p]), by simp [Prod.ext_iff], ?_⟩
      rw [← hs]; push_cast; ring
    · have : quadraticChar (ZMod p) (PadicInt.toZMod (v : ℤ_[p])) = -1 := by
        rcases quadraticChar_dichotomy (hune v) with h | h
        · exact absurd ((quadraticChar_one_iff_isSquare (hune v)).mp h) hsv
        · exact h
      rw [this]
      unfold hilbertSymbol; rw [if_neg]
      intro hex
      obtain ⟨x, y, z, hnz, heq⟩ := hprim ((p : ℤ_[p]) * u) v (by
        obtain ⟨x, y, z, h1, h2⟩ := hex
        exact ⟨x, y, z, h1, by push_cast; exact h2⟩)
      have hT := congrArg PadicInt.toZMod heq
      simp only [map_add, map_mul, map_pow, hTp, zero_mul, zero_add] at hT
      by_cases hy : PadicInt.toZMod y = 0
      · rw [hy] at hT
        simp at hT
        obtain ⟨y1, rfl⟩ := hdvd y hy
        obtain ⟨z1, rfl⟩ := hdvd z hT
        have h2 : (p : ℤ_[p]) * z1 ^ 2 = u * x ^ 2 + p * v * y1 ^ 2 := by
          apply mul_left_cancel₀ hpne; linear_combination heq
        have hT2 := congrArg PadicInt.toZMod h2
        simp only [map_add, map_mul, map_pow, hTp, zero_mul, add_zero] at hT2
        have hx : PadicInt.toZMod x = 0 := by
          rcases mul_eq_zero.mp hT2.symm with h | h
          · exact absurd h (hune u)
          · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
        rcases hnz with h | h | h
        · exact h hx
        · simp [hTp] at h
        · simp [hTp] at h
      · apply hsv
        refine ⟨PadicInt.toZMod z / PadicInt.toZMod y, ?_⟩
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]
        linear_combination -hT
  have h11 : ∀ u v : ℤ_[p]ˣ, hilbertSymbol ℚ_[p] ((p : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]))
      ((p : ℚ_[p]) * ((v : ℤ_[p]) : ℚ_[p])) =
        quadraticChar (ZMod p) (-(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p]))) := by
    intro u v
    have hne : -(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p])) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero (hune u) (hune v))
    by_cases hs : IsSquare (-(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p])))
    · rw [(quadraticChar_one_iff_isSquare hne).mpr hs]
      obtain ⟨t, ht⟩ := hs
      have ht0 : t ≠ 0 := by rintro rfl; apply hne; simpa using ht
      obtain ⟨s, hs'⟩ := hsq (-((u : ℤ_[p]) * v)) t ht0 (by
        simp only [map_neg, map_mul]; rw [ht]; ring)
      unfold hilbertSymbol; rw [if_pos]
      refine ⟨(s : ℚ_[p]), ((u : ℤ_[p]) : ℚ_[p]), 0, ?_, ?_⟩
      · intro h
        simp only [Prod.ext_iff] at h
        exact u.ne_zero (PadicInt.coe_eq_zero.mp h.2.1)
      · have hQ := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hs'
        push_cast at hQ
        linear_combination (-(p : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p])) * hQ
    · have : quadraticChar (ZMod p) (-(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p]))) = -1 := by
        rcases quadraticChar_dichotomy hne with h | h
        · exact absurd ((quadraticChar_one_iff_isSquare hne).mp h) hs
        · exact h
      rw [this]
      unfold hilbertSymbol; rw [if_neg]
      intro hex
      obtain ⟨x, y, z, hnz, heq⟩ := hprim ((p : ℤ_[p]) * u) ((p : ℤ_[p]) * v) (by
        obtain ⟨x, y, z, h1, h2⟩ := hex
        exact ⟨x, y, z, h1, by push_cast; exact h2⟩)
      have hT := congrArg PadicInt.toZMod heq
      simp only [map_add, map_mul, map_pow, hTp, zero_mul, zero_add] at hT
      have hz : PadicInt.toZMod z = 0 := pow_eq_zero_iff two_ne_zero |>.mp hT
      obtain ⟨z1, rfl⟩ := hdvd z hz
      have h2 : (p : ℤ_[p]) * z1 ^ 2 = u * x ^ 2 + v * y ^ 2 := by
        apply mul_left_cancel₀ hpne; linear_combination heq
      have hT2 := congrArg PadicInt.toZMod h2
      simp only [map_add, map_mul, map_pow, hTp, zero_mul] at hT2
      by_cases hy : PadicInt.toZMod y = 0
      · rw [hy] at hT2
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at hT2
        have hx : PadicInt.toZMod x = 0 := by
          rcases mul_eq_zero.mp hT2.symm with h | h
          · exact absurd h (hune u)
          · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
        rcases hnz with h | h | h
        · exact h hx
        · exact h hy
        · simp [hTp] at h
      · apply hs
        refine ⟨PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod x / PadicInt.toZMod y, ?_⟩
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]
        linear_combination (PadicInt.toZMod (u : ℤ_[p])) * hT2
  have hneg : ∀ a b : ZMod p, quadraticChar (ZMod p) (-(a * b)) =
      (-1) ^ ((p - 1) / 2) * quadraticChar (ZMod p) a * quadraticChar (ZMod p) b := by
    intro a b
    rw [neg_eq_neg_one_mul, map_mul, map_mul,
      quadraticChar_neg_one (by rw [ZMod.ringChar_zmod_n]; exact hp2), ZMod.card,
      ZMod.χ₄_nat_eq_if_mod_four, if_neg (by omega)]
    split_ifs with h4
    · rw [show (p - 1) / 2 = 2 * (p / 4) by omega, pow_mul]; norm_num
    · rw [show (p - 1) / 2 = 2 * (p / 4) + 1 by omega, pow_succ, pow_mul]; norm_num
  have hχsq : ∀ u : ℤ_[p]ˣ, unitChar u ^ 2 = 1 := fun u => quadraticChar_sq_one (hune u)
  have hev : ∀ n : ℕ, (-1 : ℤ) ^ (2 * n) = 1 := by intro n; rw [pow_mul]; norm_num
  have hpQ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨a, rfl | rfl⟩ : ∃ a, α = 2 * a ∨ α = 2 * a + 1 := ⟨α / 2, by omega⟩ <;>
  obtain ⟨b, rfl | rfl⟩ : ∃ b, β = 2 * b ∨ β = 2 * b + 1 := ⟨β / 2, by omega⟩
  · rw [show (p : ℚ_[p]) ^ (2 * a) * ((u : ℤ_[p]) : ℚ_[p]) = ((p : ℚ_[p]) ^ a) ^ 2 * ((u : ℤ_[p]) : ℚ_[p]) by ring,
      hred _ _ _ (pow_ne_zero _ hpQ), hilbertSymbol_comm,
      show (p : ℚ_[p]) ^ (2 * b) * ((v : ℤ_[p]) : ℚ_[p]) = ((p : ℚ_[p]) ^ b) ^ 2 * ((v : ℤ_[p]) : ℚ_[p]) by ring,
      hred _ _ _ (pow_ne_zero _ hpQ), hilbertSymbol_comm, h00,
      show 2 * a * (2 * b) * ((p - 1) / 2) = 2 * (a * (2 * b) * ((p - 1) / 2)) by ring, hev,
      pow_mul, pow_mul, hχsq, hχsq]
    simp
  · rw [show (p : ℚ_[p]) ^ (2 * a) * ((u : ℤ_[p]) : ℚ_[p]) = ((p : ℚ_[p]) ^ a) ^ 2 * ((u : ℤ_[p]) : ℚ_[p]) by ring,
      hred _ _ _ (pow_ne_zero _ hpQ), hilbertSymbol_comm,
      show (p : ℚ_[p]) ^ (2 * b + 1) * ((v : ℤ_[p]) : ℚ_[p]) = ((p : ℚ_[p]) ^ b) ^ 2 * ((p : ℚ_[p]) * ((v : ℤ_[p]) : ℚ_[p])) by ring,
      hred _ _ _ (pow_ne_zero _ hpQ), h10,
      show 2 * a * (2 * b + 1) * ((p - 1) / 2) = 2 * (a * (2 * b + 1) * ((p - 1) / 2)) by ring, hev,
      pow_succ, pow_mul, pow_mul, hχsq, hχsq]
    simp
  · rw [show (p : ℚ_[p]) ^ (2 * a + 1) * ((u : ℤ_[p]) : ℚ_[p]) = ((p : ℚ_[p]) ^ a) ^ 2 * ((p : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p])) by ring,
      hred _ _ _ (pow_ne_zero _ hpQ), hilbertSymbol_comm,
      show (p : ℚ_[p]) ^ (2 * b) * ((v : ℤ_[p]) : ℚ_[p]) = ((p : ℚ_[p]) ^ b) ^ 2 * ((v : ℤ_[p]) : ℚ_[p]) by ring,
      hred _ _ _ (pow_ne_zero _ hpQ), hilbertSymbol_comm, h10,
      show (2 * a + 1) * (2 * b) * ((p - 1) / 2) = 2 * ((2 * a + 1) * b * ((p - 1) / 2)) by ring, hev,
      pow_succ (unitChar v), pow_mul, pow_mul, hχsq, hχsq]
    simp
  · rw [show (p : ℚ_[p]) ^ (2 * a + 1) * ((u : ℤ_[p]) : ℚ_[p]) = ((p : ℚ_[p]) ^ a) ^ 2 * ((p : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p])) by ring,
      hred _ _ _ (pow_ne_zero _ hpQ), hilbertSymbol_comm,
      show (p : ℚ_[p]) ^ (2 * b + 1) * ((v : ℤ_[p]) : ℚ_[p]) = ((p : ℚ_[p]) ^ b) ^ 2 * ((p : ℚ_[p]) * ((v : ℤ_[p]) : ℚ_[p])) by ring,
      hred _ _ _ (pow_ne_zero _ hpQ), hilbertSymbol_comm, h11, hneg,
      show (2 * a + 1) * (2 * b + 1) * ((p - 1) / 2) = 2 * ((2 * a * b + a + b) * ((p - 1) / 2)) + (p - 1) / 2 by ring,
      pow_add, hev, pow_succ (unitChar u), pow_succ (unitChar v), pow_mul, pow_mul, hχsq, hχsq]
    simp only [one_pow, one_mul]
    rfl

/-! ### The explicit formula, $p = 2$ -/

/-- **$\varepsilon(u) = \frac{u - 1}{2} \bmod 2$** for a $2$-adic unit, read off $u \bmod 8$:
$0$ if $u \equiv 1 \pmod 4$, $1$ if $u \equiv 3 \pmod 4$. -/
def twoEps (r : ZMod (2 ^ 3)) : ℕ := if r = 1 ∨ r = 5 then 0 else 1

/-- **$\omega(u) = \frac{u^2 - 1}{8} \bmod 2$** for a $2$-adic unit, read off $u \bmod 8$:
$0$ if $u \equiv \pm 1 \pmod 8$, $1$ if $u \equiv \pm 3 \pmod 8$. -/
def twoOmega (r : ZMod (2 ^ 3)) : ℕ := if r = 1 ∨ r = 7 then 0 else 1

/-- **The Hilbert symbol over $\mathbb{Q}_2$:** for $a = 2^\alpha u$, $b = 2^\beta v$ with
$u, v \in \mathbb{Z}_2^\times$ and $\alpha, \beta \ge 0$,
$$(a, b)_2 = (-1)^{\varepsilon(u)\varepsilon(v) + \alpha\, \omega(v) + \beta\, \omega(u)}.$$ -/
@[kb "serre1973" "Ch. III §1.2, Thm. 1 [unverified]"]
theorem hilbertSymbol_two_formula (α β : ℕ) (u v : ℤ_[2]ˣ) :
    hilbertSymbol ℚ_[2] ((2 : ℚ_[2]) ^ α * ((u : ℤ_[2]) : ℚ_[2]))
        ((2 : ℚ_[2]) ^ β * ((v : ℤ_[2]) : ℚ_[2])) =
      (-1) ^ (twoEps (PadicInt.toZModPow 3 (u : ℤ_[2])) * twoEps (PadicInt.toZModPow 3 (v : ℤ_[2]))
        + α * twoOmega (PadicInt.toZModPow 3 (v : ℤ_[2]))
        + β * twoOmega (PadicInt.toZModPow 3 (u : ℤ_[2]))) := by
  have hsq : ∀ w : ℤ_[2], PadicInt.toZModPow 3 w = 1 → ∃ s : ℤ_[2], s ^ 2 = w := by
    intro w hw
    have h1 : w - 1 ∈ Ideal.span {((2:ℕ):ℤ_[2])^3} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hw, map_one, sub_self]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    have h2 : ‖((2:ℕ):ℤ_[2])‖ = 1/2 := by rw [PadicInt.norm_p]; norm_num
    have h2' : ‖(2:ℤ_[2])‖ = 1/2 := by exact_mod_cast h2
    obtain ⟨z, hz, -⟩ := hensels_lemma (p := 2) (F := (Polynomial.X ^ 2 - Polynomial.C w : Polynomial ℤ_[2])) (a := 1) (by
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        Polynomial.derivative_X_pow, Polynomial.derivative_C, one_pow, sub_zero, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
      have e1 : (1:ℤ_[2]) - w = -(c * ((2:ℕ):ℤ_[2])^3) := by rw [hc]; ring
      rw [e1, norm_neg, norm_mul, norm_pow, h2]
      norm_num
      rw [h2']
      nlinarith [norm_nonneg c, c.norm_le_one])
    refine ⟨z, ?_⟩
    simp at hz
    linear_combination hz
  have hmulsq : ∀ a b c : ℚ_[2], c ≠ 0 → hilbertSymbol ℚ_[2] (a * c^2) b = hilbertSymbol ℚ_[2] a b := by
    intro a b c hc
    unfold hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨c * x, y, z, ?_, by rw [h]; ring⟩
      intro h0; apply hne
      simp only [Prod.mk_eq_zero, mul_eq_zero] at h0 ⊢
      tauto
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨x / c, y, z, ?_, by rw [h]; field_simp⟩
      intro h0; apply hne
      simp only [Prod.mk_eq_zero, div_eq_zero_iff] at h0 ⊢
      tauto
  have hmulsq2 : ∀ a b c : ℚ_[2], c ≠ 0 → hilbertSymbol ℚ_[2] a (b * c^2) = hilbertSymbol ℚ_[2] a b := by
    intro a b c hc
    unfold hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨x, c * y, z, ?_, by rw [h]; ring⟩
      intro h0; apply hne
      simp only [Prod.mk_eq_zero, mul_eq_zero] at h0 ⊢
      tauto
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨x, y / c, z, ?_, by rw [h]; field_simp⟩
      intro h0; apply hne
      simp only [Prod.mk_eq_zero, div_eq_zero_iff] at h0 ⊢
      tauto
  have hpos : ∀ (a b x y : ℤ) (k : ℕ), (x ≠ 0 ∨ y ≠ 0) → (a*x^2+b*y^2) % (4^k*8) = 4^k →
      hilbertSymbol ℚ_[2] (a:ℚ_[2]) (b:ℚ_[2]) = 1 := by
    intro a b x y k hxy hmod
    have hdiv := Int.mul_ediv_add_emod (a*x^2+b*y^2) (4^k*8)
    rw [hmod] at hdiv
    set q := (a*x^2+b*y^2) / (4^k*8)
    obtain ⟨s, hs⟩ := hsq ((8*q+1 : ℤ) : ℤ_[2]) (by
      rw [map_intCast]; push_cast
      rw [show ((8:ZMod (2^3))) = 0 by decide]; ring)
    unfold hilbertSymbol
    rw [if_pos]
    refine ⟨x, y, 2^k * (s:ℚ_[2]), ?_, ?_⟩
    · intro h0; simp only [Prod.mk_eq_zero, Int.cast_eq_zero] at h0; tauto
    · have hs' : ((s:ℚ_[2]))^2 = ((8*q+1 : ℤ):ℚ_[2]) := by
        rw [← PadicInt.coe_pow, hs]; norm_cast
      have heq : ((a*x^2+b*y^2 : ℤ) : ℚ_[2]) = ((4^k*8*q + 4^k : ℤ) : ℚ_[2]) := by rw [hdiv]
      push_cast at heq hs'
      rw [mul_pow, hs', heq, ← pow_mul, mul_comm k 2, pow_mul]; ring
  have hneg : ∀ a b : ℤ, (∀ y z : ZMod (2^4), z^2 ≠ (a : ZMod (2^4)) + (b : ZMod (2^4))*y^2) →
      (∀ x z : ZMod (2^4), z^2 ≠ (a : ZMod (2^4))*x^2+(b : ZMod (2^4))) →
      (∀ x y : ZMod (2^4), 1 ≠ (a : ZMod (2^4))*x^2+(b : ZMod (2^4))*y^2) →
      hilbertSymbol ℚ_[2] (a:ℚ_[2]) (b:ℚ_[2]) = -1 := by
    intro a b h1 h2 h3
    have key : ∀ X Y Z : ℤ_[2], Z^2 = a*X^2 + b*Y^2 → X = 1 ∨ Y = 1 ∨ Z = 1 → False := by
      intro X Y Z hXYZ hone
      have hm := congrArg (PadicInt.toZModPow 4) hXYZ
      simp only [map_add, map_mul, map_pow, map_intCast] at hm
      rcases hone with rfl | rfl | rfl
      · rw [map_one, one_pow, mul_one] at hm
        exact h1 _ _ hm
      · rw [map_one, one_pow, mul_one] at hm
        exact h2 _ _ hm
      · rw [map_one, one_pow] at hm
        exact h3 _ _ hm
    unfold hilbertSymbol
    rw [if_neg]
    rintro ⟨x, y, z, hne, h⟩
    obtain ⟨t, hx, hy, hz, ht⟩ : ∃ t : ℚ_[2], ‖x‖ ≤ ‖t‖ ∧ ‖y‖ ≤ ‖t‖ ∧ ‖z‖ ≤ ‖t‖ ∧ (t = x ∨ t = y ∨ t = z) := by
      rcases le_total ‖x‖ ‖y‖ with hxy | hxy <;> rcases le_total ‖y‖ ‖z‖ with hyz | hyz <;>
        rcases le_total ‖x‖ ‖z‖ with hxz | hxz
      all_goals first
        | exact ⟨x, le_rfl, by linarith, by linarith, Or.inl rfl⟩
        | exact ⟨y, by linarith, le_rfl, by linarith, Or.inr (Or.inl rfl)⟩
        | exact ⟨z, by linarith, by linarith, le_rfl, Or.inr (Or.inr rfl)⟩
    have ht0 : t ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hx hy hz
      apply hne
      simp [norm_le_zero_iff.mp hx, norm_le_zero_iff.mp hy, norm_le_zero_iff.mp hz]
    have hX : ‖x / t‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hx (norm_nonneg _)
    have hY : ‖y / t‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hy (norm_nonneg _)
    have hZ : ‖z / t‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hz (norm_nonneg _)
    apply key ⟨x/t, hX⟩ ⟨y/t, hY⟩ ⟨z/t, hZ⟩
    · apply PadicInt.ext
      simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_intCast]
      show (z/t)^2 = (a:ℚ_[2]) * (x/t)^2 + b * (y/t)^2
      rw [div_pow, div_pow, div_pow, h]; field_simp
    · rcases ht with rfl | rfl | rfl
      · left; apply PadicInt.ext; show t / t = ((1:ℤ_[2]):ℚ_[2]); simp [div_self ht0]
      · right; left; apply PadicInt.ext; show t / t = ((1:ℤ_[2]):ℚ_[2]); simp [div_self ht0]
      · right; right; apply PadicInt.ext; show t / t = ((1:ℤ_[2]):ℚ_[2]); simp [div_self ht0]
  have hred : ∀ u : ℤ_[2]ˣ, ∃ r : ℤ, (r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) ∧
      PadicInt.toZModPow 3 (u:ℤ_[2]) = r ∧ ∃ c : ℚ_[2], c ≠ 0 ∧ ((u:ℤ_[2]):ℚ_[2]) = r * c^2 := by
    intro u
    have hu : PadicInt.toZModPow 3 (u:ℤ_[2]) * PadicInt.toZModPow 3 ((u⁻¹ : ℤ_[2]ˣ):ℤ_[2]) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    obtain ⟨r, hr, hur⟩ : ∃ r : ℤ, (r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) ∧ PadicInt.toZModPow 3 (u:ℤ_[2]) = r := by
      generalize PadicInt.toZModPow 3 (u:ℤ_[2]) = e at hu
      generalize PadicInt.toZModPow 3 ((u⁻¹ : ℤ_[2]ˣ):ℤ_[2]) = f at hu
      have : ∀ e f : ZMod (2^3), e * f = 1 → e = ((1:ℤ):ZMod (2^3)) ∨ e = ((3:ℤ):ZMod (2^3)) ∨ e = ((5:ℤ):ZMod (2^3)) ∨ e = ((7:ℤ):ZMod (2^3)) := by decide
      rcases this e f hu with h | h | h | h
      · exact ⟨1, by norm_num, h⟩
      · exact ⟨3, by norm_num, h⟩
      · exact ⟨5, by norm_num, h⟩
      · exact ⟨7, by norm_num, h⟩
    refine ⟨r, hr, hur, ?_⟩
    obtain ⟨s, hs⟩ := hsq ((u:ℤ_[2]) * r) (by
      rw [map_mul, hur, map_intCast]; rcases hr with rfl|rfl|rfl|rfl <;> decide)
    have hr0 : (r:ℚ_[2]) ≠ 0 := by rcases hr with rfl|rfl|rfl|rfl <;> norm_num
    have hu0 : ((u:ℤ_[2]):ℚ_[2]) ≠ 0 := by
      intro h0
      exact u.ne_zero (PadicInt.ext (by simpa using h0))
    have hs' : ((s:ℚ_[2]))^2 = ((u:ℤ_[2]):ℚ_[2]) * r := by
      rw [← PadicInt.coe_pow, hs]; norm_cast
    refine ⟨s / r, ?_, ?_⟩
    · intro h0
      rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · rw [h0] at hs'
        have : ((u:ℤ_[2]):ℚ_[2]) * r = 0 := by rw [← hs']; ring
        exact mul_ne_zero hu0 hr0 this
      · exact hr0 h0
    · rw [div_pow, hs']; field_simp
  have key : ∀ (α' β' : ℕ), α' < 2 → β' < 2 → ∀ (r r' : ℤ), (r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) →
      (r' = 1 ∨ r' = 3 ∨ r' = 5 ∨ r' = 7) →
      hilbertSymbol ℚ_[2] ((2^α' * r : ℤ) : ℚ_[2]) ((2^β' * r' : ℤ) : ℚ_[2]) =
        (-1) ^ (twoEps (r : ZMod (2^3)) * twoEps (r' : ZMod (2^3)) + α' * twoOmega (r' : ZMod (2^3))
          + β' * twoOmega (r : ZMod (2^3))) := by
    intro α' β' hα hβ r r' hr hr'
    interval_cases α' <;> interval_cases β' <;> rcases hr with rfl|rfl|rfl|rfl <;>
      rcases hr' with rfl|rfl|rfl|rfl
    all_goals first
      | (rw [show (-1 : ℤ) ^ (twoEps _ * twoEps _ + _ + _) = -1 from by decide]
         exact hneg _ _ (by decide) (by decide) (by decide))
      | (rw [show (-1 : ℤ) ^ (twoEps _ * twoEps _ + _ + _) = 1 from by decide]
         first
          | exact hpos _ _ 1 0 0 (by decide) (by decide)
          | exact hpos _ _ 0 1 0 (by decide) (by decide)
          | exact hpos _ _ 1 1 0 (by decide) (by decide)
          | exact hpos _ _ 1 2 0 (by decide) (by decide)
          | exact hpos _ _ 2 1 0 (by decide) (by decide)
          | exact hpos _ _ 1 1 1 (by decide) (by decide)
          | exact hpos _ _ 1 3 1 (by decide) (by decide)
          | exact hpos _ _ 3 1 1 (by decide) (by decide)
          | exact hpos _ _ 1 1 2 (by decide) (by decide))
  obtain ⟨r, hr, hur, c, hc0, hc⟩ := hred u
  obtain ⟨r', hr', hvr, c', hc0', hc'⟩ := hred v
  rw [hur, hvr, hc, hc']
  have hα := (Nat.div_add_mod α 2).symm
  have hβ := (Nat.div_add_mod β 2).symm
  have e1 : (2 : ℚ_[2]) ^ α * (r * c^2) = ((2^(α%2) * r : ℤ) : ℚ_[2]) * (2^(α/2) * c)^2 := by
    conv_lhs => rw [hα]
    push_cast; ring
  have e2 : (2 : ℚ_[2]) ^ β * (r' * c'^2) = ((2^(β%2) * r' : ℤ) : ℚ_[2]) * (2^(β/2) * c')^2 := by
    conv_lhs => rw [hβ]
    push_cast; ring
  rw [e1, e2, hmulsq _ _ _ (mul_ne_zero (pow_ne_zero _ two_ne_zero) hc0),
    hmulsq2 _ _ _ (mul_ne_zero (pow_ne_zero _ two_ne_zero) hc0'),
    key _ _ (Nat.mod_lt _ two_pos) (Nat.mod_lt _ two_pos) r r' hr hr']
  generalize twoEps (r : ZMod (2^3)) = e1
  generalize twoEps (r' : ZMod (2^3)) = e2
  generalize twoOmega (r : ZMod (2^3)) = w1
  generalize twoOmega (r' : ZMod (2^3)) = w2
  have : e1 * e2 + α * w2 + β * w1 = (e1 * e2 + α % 2 * w2 + β % 2 * w1) + 2 * (α / 2 * w2 + β / 2 * w1) := by
    conv_lhs => rw [hα, hβ]
    ring
  conv_rhs => rw [this, pow_add, pow_mul]
  norm_num

/-! ### Almost all places -/

/-- **$(a, b)_p = 1$ at odd primes not dividing $a$ or $b$:** for $a, b \in \mathbb{Q}^\times$ and an
odd prime $p$ with $v_p(a) = v_p(b) = 0$, the local symbol at $p$ is $1$ (both are $p$-adic
units). -/
@[kb "serre1973" "Ch. III §2.1 [unverified]"]
theorem hilbert_eq_one_of_padicValRat (hp2 : p ≠ 2) (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpa : padicValRat p a = 0) (hpb : padicValRat p b = 0) :
    RatPlace.hilbert (.finite ⟨p, hp.out⟩) a b = 1 := by
  open Polynomial in
  have hA : ‖(a:ℚ_[p])‖ = 1 := by
    rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero ha, hpa]; simp
  have hB : ‖(b:ℚ_[p])‖ = 1 := by
    rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hb, hpb]; simp
  set A : ℤ_[p] := ⟨a, hA.le⟩ with hAdef
  set B : ℤ_[p] := ⟨b, hB.le⟩ with hBdef
  have key : ∀ w : ℤ_[p], ‖w‖ < 1 ↔ PadicInt.toZMod w = 0 := by
    intro w
    rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod,
      RingHom.mem_ker]
  have hA0 : PadicInt.toZMod A ≠ 0 := by
    intro h; have := (key A).2 h; rw [PadicInt.norm_def] at this; simp [A, hA] at this
  have hB0 : PadicInt.toZMod B ≠ 0 := by
    intro h; have := (key B).2 h; rw [PadicInt.norm_def] at this; simp [B, hB] at this
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2:ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    rcases (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this with h'
    exact hp2 h'
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  obtain ⟨x0, y0, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := C (PadicInt.toZMod A) * X ^ 2) (g := C (PadicInt.toZMod B) * X ^ 2 - C 1)
    (by rw [degree_C_mul_X_pow 2 hA0]; rfl)
    (by rw [degree_sub_C] <;> rw [degree_C_mul_X_pow 2 hB0] <;> decide) hodd
  simp at hxy
  obtain ⟨x, rfl⟩ := ZMod.ringHom_surjective PadicInt.toZMod x0
  obtain ⟨y, rfl⟩ := ZMod.ringHom_surjective PadicInt.toZMod y0
  set c := A * x ^ 2 + B * y ^ 2 with hc
  have hc1 : PadicInt.toZMod c = 1 := by
    simp only [c, map_add, map_mul, map_pow]; linear_combination hxy
  have h1 : ‖(2 : ℤ_[p])‖ = 1 := by
    have := (key 2).not.2 (by rw [map_ofNat]; exact h2)
    have := PadicInt.norm_le_one (2 : ℤ_[p])
    push Not at *; linarith
  have h3 : ‖1 - c‖ < 1 := by rw [key]; simp [hc1]
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := p) (R := ℤ_[p]) (F := (X ^ 2 - C c : ℤ_[p][X])) (a := 1) (by
    simpa [h1, one_add_one_eq_two, Algebra.algebraMap_self] using h3)
  simp at hz
  have hz0 : PadicInt.toZMod z ^ 2 = 1 := by
    rw [← map_pow, sub_eq_zero.1 hz, hc1]
  simp only [RatPlace.hilbert, hilbertSymbol]
  rw [if_pos]
  refine ⟨(x : ℚ_[p]), (y : ℚ_[p]), (z : ℚ_[p]), ?_, ?_⟩
  · intro h
    simp [Prod.ext_iff] at h
    rw [h.2.2] at hz0
    simp at hz0
  · have := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) (sub_eq_zero.1 hz)
    simp only [c, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow] at this
    exact this

/-- **Finite support:** for $a, b \in \mathbb{Q}^\times$, $(a, b)_v = -1$ at only finitely many places. -/
@[kb "serre1973" "Ch. III §2.1 [unverified]"]
theorem hilbert_support_finite (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : RatPlace | v.hilbert a b = -1}.Finite := by
  have key : ∀ (p : ℕ) [hp : Fact p.Prime], p ≠ 2 → ∀ (A B : ℤ), ¬ (p:ℤ) ∣ A → ¬ (p:ℤ) ∣ B →
      ∃ X Y Z : ℤ_[p], Z ≠ 0 ∧ Z ^ 2 = A * X ^ 2 + B * Y ^ 2 := by
    intro p hp hp2 A B hA hB
    have hA' : (A : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hB' : (B : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hodd : Fintype.card (ZMod p) % 2 = 1 := by
      rw [ZMod.card]; exact Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
    have hf : (Polynomial.C (A : ZMod p) * Polynomial.X ^ 2).degree = 2 := by
      rw [Polynomial.degree_C_mul_X_pow 2 hA']; rfl
    have hg : (Polynomial.C (B : ZMod p) * Polynomial.X ^ 2 - 1).degree = 2 := by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> rw [Polynomial.degree_C_mul_X_pow 2 hB'] <;> simp
    obtain ⟨x0, y0, h0⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one] at h0
    set c : ℤ_[p] := A * (x0.val : ℤ_[p]) ^ 2 + B * (y0.val : ℤ_[p]) ^ 2 with hc
    have hc1 : PadicInt.toZMod c = 1 := by
      simp only [hc, map_add, map_mul, map_pow, map_intCast, map_natCast, ZMod.natCast_zmod_val]
      linear_combination h0
    have hlt : ‖1 - c‖ < 1 := by
      have : 1 - c ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
        rw [RingHom.mem_ker, map_sub, hc1, map_one, sub_self]
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at this
      exact PadicInt.mem_nonunits.mp this
    have h2 : ‖(2 : ℤ_[p])‖ = 1 := by
      have h1 := PadicInt.norm_le_one (p := p) 2
      have h3 : ¬ ‖((2:ℤ) : ℤ_[p])‖ < 1 := by
        rw [PadicInt.norm_int_lt_one_iff_dvd]
        intro h
        have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (by exact_mod_cast h)
        exact hp2 this
      push_cast at h1 h3
      linarith
    obtain ⟨z, hz, -⟩ := hensels_lemma (p := p) (R := ℤ_[p])
      (F := Polynomial.X ^ 2 - Polynomial.C c) (a := 1) (by
        simp
        rw [one_add_one_eq_two, h2]
        simpa using hlt)
    refine ⟨x0.val, y0.val, z, ?_, ?_⟩
    · rintro rfl
      simp at hz
      rw [hz] at hc1
      simp at hc1
    · simp at hz
      linear_combination hz
  set N : ℕ := 2 * a.num.natAbs * a.den * b.num.natAbs * b.den with hN
  have hN0 : N ≠ 0 := by
    have := Rat.num_ne_zero.mpr ha
    have := Rat.num_ne_zero.mpr hb
    have := a.den_nz
    have := b.den_nz
    positivity
  have hsub : {v : RatPlace | v.hilbert a b = -1} ⊆
      insert RatPlace.infinite
        (RatPlace.finite '' ((↑) ⁻¹' (N.primeFactors : Set ℕ))) := by
    intro v hv
    cases v with
    | infinite => exact Set.mem_insert _ _
    | finite q =>
      right
      refine ⟨q, ?_, rfl⟩
      show (q:ℕ) ∈ N.primeFactors
      rw [Nat.mem_primeFactors]
      refine ⟨q.2, ?_, hN0⟩
      by_contra hdvd
      obtain ⟨p, hpp⟩ := q
      have : Fact p.Prime := ⟨hpp⟩
      simp only at hdvd
      have h2 : ¬ p ∣ 2 := fun h => hdvd (dvd_trans h ⟨a.num.natAbs * a.den * b.num.natAbs * b.den, by rw [hN]; ring⟩)
      have h3 : ¬ p ∣ a.num.natAbs := fun h => hdvd (dvd_trans h ⟨2 * a.den * b.num.natAbs * b.den, by rw [hN]; ring⟩)
      have h4 : ¬ p ∣ a.den := fun h => hdvd (dvd_trans h ⟨2 * a.num.natAbs * b.num.natAbs * b.den, by rw [hN]; ring⟩)
      have h5 : ¬ p ∣ b.num.natAbs := fun h => hdvd (dvd_trans h ⟨2 * a.num.natAbs * a.den * b.den, by rw [hN]; ring⟩)
      have h6 : ¬ p ∣ b.den := fun h => hdvd (dvd_trans h ⟨2 * a.num.natAbs * a.den * b.num.natAbs, by rw [hN]; ring⟩)
      have hp2 : p ≠ 2 := by
        rintro rfl; exact h2 dvd_rfl
      have hA : ¬ (p:ℤ) ∣ a.num * a.den * (b.den : ℤ)^2 := by
        intro h
        have h' := Int.natCast_dvd.mp h
        simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h'
        rcases (Nat.Prime.dvd_mul hpp).mp h' with h' | h'
        · rcases (Nat.Prime.dvd_mul hpp).mp h' with h' | h'
          · exact h3 h'
          · exact h4 h'
        · exact h6 (hpp.dvd_of_dvd_pow h')
      have hB : ¬ (p:ℤ) ∣ b.num * b.den * (a.den : ℤ)^2 := by
        intro h
        have h' := Int.natCast_dvd.mp h
        simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h'
        rcases (Nat.Prime.dvd_mul hpp).mp h' with h' | h'
        · rcases (Nat.Prime.dvd_mul hpp).mp h' with h' | h'
          · exact h5 h'
          · exact h6 h'
        · exact h4 (hpp.dvd_of_dvd_pow h')
      obtain ⟨X, Y, Z, hZ, hXYZ⟩ := key p hp2 _ _ hA hB
      have hZ' : (Z : ℚ_[p]) ≠ 0 := by simpa using hZ
      have had : (a.den : ℚ_[p]) ≠ 0 := by exact_mod_cast a.den_nz
      have hbd : (b.den : ℚ_[p]) ≠ 0 := by exact_mod_cast b.den_nz
      have ha' : ((a : ℚ) : ℚ_[p]) = (a.num : ℚ_[p]) / (a.den : ℚ_[p]) := by
        conv_lhs => rw [← Rat.num_div_den a]
        push_cast; rfl
      have hb' : ((b : ℚ) : ℚ_[p]) = (b.num : ℚ_[p]) / (b.den : ℚ_[p]) := by
        conv_lhs => rw [← Rat.num_div_den b]
        push_cast; rfl
      have hXYZ' := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hXYZ
      simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_intCast] at hXYZ'
      push_cast at hXYZ'
      have hex : ∃ x y z : ℚ_[p], (x, y, z) ≠ 0 ∧ z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 := by
        refine ⟨X, Y, (Z : ℚ_[p]) / ((a.den : ℚ_[p]) * b.den), ?_, ?_⟩
        · intro h
          have := congrArg (fun t => t.2.2) h
          simp only [Prod.snd_zero] at this
          exact div_ne_zero hZ' (mul_ne_zero had hbd) this
        · rw [div_pow, ha', hb', hXYZ']
          field_simp
      have hv' : hilbertSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) = -1 := hv
      unfold hilbertSymbol at hv'
      rw [if_pos hex] at hv'
      norm_num at hv'
  refine (Set.Finite.insert _ (Set.Finite.image _ ?_)).subset hsub
  exact Set.Finite.preimage (fun x _ y _ h => Subtype.ext h) (Finset.finite_toSet _)

/-! ### Bimultiplicativity -/

/-- **Bimultiplicativity over $\mathbb{Q}_p$** (every prime $p$, including $p = 2$): for nonzero
$a, a', b \in \mathbb{Q}_p$,
$$(a a', b)_p = (a, b)_p\, (a', b)_p.$$
Follows from the explicit formulas (`hilbertSymbol_odd_formula`, `hilbertSymbol_two_formula`)
after writing each element as $p^k u$ and reducing exponents mod $2$. -/
@[kb "serre1973" "Ch. III §1.2, Thm. 2 [unverified]"]
theorem hilbertSymbol_padic_mul_left (a a' b : ℚ_[p]) (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol ℚ_[p] (a * a') b = hilbertSymbol ℚ_[p] a b * hilbertSymbol ℚ_[p] a' b := by
  have hsqL : ∀ (a b c : ℚ_[p]), c ≠ 0 → hilbertSymbol ℚ_[p] (c ^ 2 * a) b = hilbertSymbol ℚ_[p] a b := by
    intro a b c hc
    unfold hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨x, y, z, hne, heq⟩
      refine ⟨c * x, y, z, ?_, by rw [heq]; ring⟩
      intro h
      apply hne
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, mul_eq_zero, hc, false_or] at h ⊢
      exact h
    · rintro ⟨x, y, z, hne, heq⟩
      refine ⟨x / c, y, z, ?_, by rw [heq]; field_simp⟩
      intro h
      apply hne
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, div_eq_zero_iff, hc, or_false] at h ⊢
      exact h
  have hsqR : ∀ (a b c : ℚ_[p]), c ≠ 0 → hilbertSymbol ℚ_[p] a (c ^ 2 * b) = hilbertSymbol ℚ_[p] a b := by
    intro a b c hc
    unfold hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨x, y, z, hne, heq⟩
      refine ⟨x, c * y, z, ?_, by rw [heq]; ring⟩
      intro h
      apply hne
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, mul_eq_zero, hc, false_or] at h ⊢
      exact h
    · rintro ⟨x, y, z, hne, heq⟩
      refine ⟨x, y / c, z, ?_, by rw [heq]; field_simp⟩
      intro h
      apply hne
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, div_eq_zero_iff, hc, or_false] at h ⊢
      exact h
  have hdec : ∀ x : ℚ_[p], x ≠ 0 → ∃ (n : ℕ) (u : ℤ_[p]ˣ) (c : ℚ_[p]), c ≠ 0 ∧
      x = c ^ 2 * ((p : ℚ_[p]) ^ n * ((u : ℤ_[p]) : ℚ_[p])) := by
    intro x hx
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    have hpos : (0 : ℝ) < p := by linarith
    have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    set k := x.valuation
    have hyn : ‖x * (p : ℚ_[p]) ^ (-k)‖ = 1 := by
      rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx,
        ← zpow_add₀ hpos.ne']
      simp [k]
    refine ⟨(k + 2 * k.natAbs).toNat, PadicInt.mkUnits hyn, (p : ℚ_[p]) ^ (-(k.natAbs : ℤ)),
      zpow_ne_zero _ hpne, ?_⟩
    rw [PadicInt.mkUnits_eq]
    have h0 : (0:ℤ) ≤ k + 2 * k.natAbs := by omega
    have : ((p : ℚ_[p]) ^ (k + 2 * k.natAbs).toNat) = (p : ℚ_[p]) ^ (k + 2 * k.natAbs) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg h0]
    rw [this, ← zpow_natCast, ← zpow_mul]
    have e : (p : ℚ_[p]) ^ (-(k.natAbs : ℤ) * ((2:ℕ):ℤ)) * ((p : ℚ_[p]) ^ (k + 2 * k.natAbs) * (x * (p : ℚ_[p]) ^ (-k)))
        = x * ((p : ℚ_[p]) ^ (-(k.natAbs : ℤ) * ((2:ℕ):ℤ)) * (p : ℚ_[p]) ^ (k + 2 * k.natAbs) * (p : ℚ_[p]) ^ (-k)) := by ring
    rw [e, ← zpow_add₀ hpne, ← zpow_add₀ hpne]
    push_cast
    ring_nf
    simp
  obtain ⟨n, u, c, hc, rfl⟩ := hdec a ha
  obtain ⟨n', u', c', hc', rfl⟩ := hdec a' ha'
  obtain ⟨m, v, d, hd, rfl⟩ := hdec b hb
  have e : c ^ 2 * ((p : ℚ_[p]) ^ n * ((u : ℤ_[p]) : ℚ_[p])) * (c' ^ 2 * ((p : ℚ_[p]) ^ n' * ((u' : ℤ_[p]) : ℚ_[p])))
      = (c * c') ^ 2 * ((p : ℚ_[p]) ^ (n + n') * (((u * u' : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) := by
    push_cast; ring
  rw [e, hsqL _ _ _ (mul_ne_zero hc hc'), hsqR _ _ _ hd, hsqL _ _ _ hc, hsqR _ _ _ hd,
    hsqL _ _ _ hc', hsqR _ _ _ hd]
  by_cases hp2 : p ≠ 2
  · rw [hilbertSymbol_odd_formula hp2, hilbertSymbol_odd_formula hp2, hilbertSymbol_odd_formula hp2]
    have hχ : unitChar (u * u') = unitChar u * unitChar u' := by
      unfold unitChar; push_cast; rw [map_mul, map_mul]
    rw [hχ, add_mul, add_mul, pow_add, mul_pow, pow_add]; ring
  · push Not at hp2
    subst hp2
    simp only [Nat.cast_ofNat]
    rw [hilbertSymbol_two_formula, hilbertSymbol_two_formula, hilbertSymbol_two_formula]
    have hres : ∀ w : ℤ_[2]ˣ, ∃ w' : ZMod (2^3), PadicInt.toZModPow 3 (w : ℤ_[2]) * w' = 1 :=
      fun w => ⟨PadicInt.toZModPow 3 ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), by rw [← map_mul, Units.mul_inv, map_one]⟩
    have hmul : PadicInt.toZModPow 3 ((u * u' : ℤ_[2]ˣ) : ℤ_[2]) =
        PadicInt.toZModPow 3 (u : ℤ_[2]) * PadicInt.toZModPow 3 (u' : ℤ_[2]) := by
      push_cast; rw [map_mul]
    rw [hmul]
    have h4 : ∀ r : ZMod (2^3), (∃ r', r * r' = 1) → r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by decide
    have hkey : ∀ r s : ZMod (2^3), (r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) → (s = 1 ∨ s = 3 ∨ s = 5 ∨ s = 7) →
        twoEps (r * s) + 2 * (twoEps r * twoEps s) = twoEps r + twoEps s ∧
        twoOmega (r * s) + 2 * (twoOmega r * twoOmega s) = twoOmega r + twoOmega s := by decide
    obtain ⟨he, hw⟩ := hkey _ _ (h4 _ (hres u)) (h4 _ (hres u'))
    generalize PadicInt.toZModPow 3 (u : ℤ_[2]) = r at he hw ⊢
    generalize PadicInt.toZModPow 3 (u' : ℤ_[2]) = s at he hw ⊢
    generalize PadicInt.toZModPow 3 (v : ℤ_[2]) = t
    rw [← pow_add]
    have : twoEps r * twoEps t + n * twoOmega t + m * twoOmega r +
        (twoEps s * twoEps t + n' * twoOmega t + m * twoOmega s) =
        (twoEps (r * s) * twoEps t + (n + n') * twoOmega t + m * twoOmega (r * s)) +
          2 * (twoEps r * twoEps s * twoEps t + m * (twoOmega r * twoOmega s)) := by
      have e1 : twoEps r * twoEps t + n * twoOmega t + m * twoOmega r +
        (twoEps s * twoEps t + n' * twoOmega t + m * twoOmega s) =
          (twoEps r + twoEps s) * twoEps t + (n + n') * twoOmega t + m * (twoOmega r + twoOmega s) := by ring
      rw [e1, ← he, ← hw]; ring
    rw [this, pow_add (-1 : ℤ) _ (2 * _), pow_mul, neg_one_sq, one_pow, mul_one]

/-- **Bimultiplicativity over $\mathbb{R}$:** for nonzero $a, a', b \in \mathbb{R}$,
$(a a', b)_{\mathbb{R}} = (a, b)_{\mathbb{R}}\, (a', b)_{\mathbb{R}}$ (from `hilbertSymbol_real`). -/
@[kb "serre1973" "Ch. III §1.2, Thm. 2 [unverified]"]
theorem hilbertSymbol_real_mul_left (a a' b : ℝ) (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol ℝ (a * a') b = hilbertSymbol ℝ a b * hilbertSymbol ℝ a' b := by
  have hpos : ∀ x y : ℝ, (0 < x ∨ 0 < y) → hilbertSymbol ℝ x y = 1 := by
    intro x y h
    unfold hilbertSymbol
    rw [if_pos]
    rcases h with h | h
    · refine ⟨1, 0, Real.sqrt x, by simp [Prod.ext_iff], ?_⟩
      rw [Real.sq_sqrt h.le]; ring
    · refine ⟨0, 1, Real.sqrt y, by simp [Prod.ext_iff], ?_⟩
      rw [Real.sq_sqrt h.le]; ring
  have hneg : ∀ x y : ℝ, x < 0 → y < 0 → hilbertSymbol ℝ x y = -1 := by
    intro x y hx hy
    unfold hilbertSymbol
    rw [if_neg]
    rintro ⟨X, Y, Z, hne, h⟩
    apply hne
    have hX : X = 0 := by
      by_contra hX
      have : 0 < X ^ 2 := by positivity
      nlinarith [sq_nonneg Y, sq_nonneg Z]
    have hY : Y = 0 := by
      by_contra hY
      have : 0 < Y ^ 2 := by positivity
      nlinarith [sq_nonneg X, sq_nonneg Z]
    have hZ : Z = 0 := by
      subst hX hY
      simpa using h
    simp [hX, hY, hZ]
  have e : ∀ x : ℝ, x ≠ 0 → hilbertSymbol ℝ x b = if x < 0 ∧ b < 0 then -1 else 1 := by
    intro x hx
    split_ifs with hc
    · exact hneg x b hc.1 hc.2
    · apply hpos
      rcases lt_or_gt_of_ne hx with h1 | h1
      · rcases lt_or_gt_of_ne hb with h2 | h2
        · exact absurd ⟨h1, h2⟩ hc
        · exact Or.inr h2
      · exact Or.inl h1
  rw [e _ (mul_ne_zero ha ha'), e _ ha, e _ ha']
  rcases lt_or_gt_of_ne ha with h1 | h1 <;> rcases lt_or_gt_of_ne ha' with h2 | h2 <;>
    rcases lt_or_gt_of_ne hb with h3 | h3
  all_goals
    first
    | (have : 0 < a * a' := by nlinarith
       simp [h1, h2, h3, not_lt.mpr this.le, not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr h3.le])
    | (have : a * a' < 0 := by nlinarith
       simp [h1, h2, h3, this, not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr h3.le])

/-- **Bimultiplicativity at every place of $\mathbb{Q}$:** for nonzero rationals $a, a', b$ and
any place $v$, $(a a', b)_v = (a, b)_v\, (a', b)_v$. -/
@[kb "serre1973" "Ch. III §1.2, Thm. 2 [unverified]"]
theorem RatPlace.hilbert_mul_left (v : RatPlace) (a a' b : ℚ) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hb : b ≠ 0) : v.hilbert (a * a') b = v.hilbert a b * v.hilbert a' b := by
  have hsq : ∀ (K : Type) [Field K] (a b c : K), c ≠ 0 → hilbertSymbol K (c ^ 2 * a) b = hilbertSymbol K a b := by
    intro K _ a b c hc
    unfold hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨x, y, z, hne, heq⟩
      refine ⟨c * x, y, z, ?_, by rw [heq]; ring⟩
      intro h
      apply hne
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, mul_eq_zero, hc, false_or] at h ⊢
      exact h
    · rintro ⟨x, y, z, hne, heq⟩
      refine ⟨x / c, y, z, ?_, by rw [heq]; field_simp⟩
      intro h
      apply hne
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, div_eq_zero_iff, hc, or_false] at h ⊢
      exact h
  have hcomm : ∀ (K : Type) [Field K] (a b : K), hilbertSymbol K a b = hilbertSymbol K b a := by
    intro K _ a b; unfold hilbertSymbol; congr 1; apply propext; constructor <;>
    · rintro ⟨x, y, z, hne, heq⟩
      refine ⟨y, x, z, ?_, by rw [heq]; ring⟩
      intro h; apply hne; simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h ⊢; tauto
  have hsq' : ∀ (K : Type) [Field K] (a b c : K), c ≠ 0 → hilbertSymbol K a (c ^ 2 * b) = hilbertSymbol K a b := by
    intro K _ a b c hc
    rw [hcomm, hsq K b a c hc, hcomm]
  have decomp : ∀ (p : ℕ) [Fact p.Prime] (x : ℚ_[p]), x ≠ 0 → ∃ (α : ℕ) (u : ℤ_[p]ˣ) (c : ℚ_[p]), c ≠ 0 ∧ x = c ^ 2 * ((p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p])) := by
    intro p _ x hx
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hpos : (0 : ℝ) < p := by linarith
    have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    set k := x.valuation with hk
    have hy : ‖x * (p : ℚ_[p]) ^ (-k)‖ = 1 := by
      rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx, ← zpow_add₀ hpos.ne']
      simp [k]
    refine ⟨(k + 2 * k.natAbs).toNat, PadicInt.mkUnits hy, (p : ℚ_[p]) ^ (-(k.natAbs : ℤ)), zpow_ne_zero _ hpne, ?_⟩
    rw [PadicInt.mkUnits_eq, show ((p:ℚ_[p]) ^ (k + 2 * k.natAbs).toNat) = (p:ℚ_[p]) ^ (k + 2*k.natAbs) by rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)], show ((p:ℚ_[p]) ^ (-(k.natAbs:ℤ)))^2 = (p:ℚ_[p])^(-(k.natAbs:ℤ) * 2) by rw [← zpow_natCast, ← zpow_mul]; rfl]
    have : (p : ℚ_[p]) ^ (-(k.natAbs : ℤ) * 2) * ((p : ℚ_[p]) ^ (k + 2 * k.natAbs) * (x * (p : ℚ_[p]) ^ (-k))) = x * ((p : ℚ_[p]) ^ (-(k.natAbs : ℤ) * 2) * (p : ℚ_[p]) ^ (k + 2 * k.natAbs) * (p : ℚ_[p]) ^ (-k)) := by ring
    rw [this, ← zpow_add₀ hpne, ← zpow_add₀ hpne]
    rw [show (-(k.natAbs : ℤ) * 2 + (k + 2 * k.natAbs) + -k) = 0 by ring, zpow_zero, mul_one]
  have padic : ∀ (p : ℕ) [hp : Fact p.Prime] (a a' b : ℚ_[p]), a ≠ 0 → a' ≠ 0 → b ≠ 0 →
      hilbertSymbol ℚ_[p] (a * a') b = hilbertSymbol ℚ_[p] a b * hilbertSymbol ℚ_[p] a' b := by
    intro p hp a a' b ha ha' hb
    obtain ⟨α, u, c, hc, rfl⟩ := decomp p a ha
    obtain ⟨α', u', c', hc', rfl⟩ := decomp p a' ha'
    obtain ⟨β, v, d, hd, rfl⟩ := decomp p b hb
    have e : c ^ 2 * ((p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p])) * (c' ^ 2 * ((p : ℚ_[p]) ^ α' * ((u' : ℤ_[p]) : ℚ_[p]))) = (c * c') ^ 2 * ((p : ℚ_[p]) ^ (α + α') * (((u * u' : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) := by
      push_cast; ring
    rw [e, hsq _ _ _ _ (mul_ne_zero hc hc'), hsq _ _ _ _ hc, hsq _ _ _ _ hc', hsq' _ _ _ _ hd,
      hsq' _ _ _ _ hd, hsq' _ _ _ _ hd]
    by_cases hp2 : p = 2
    · subst hp2
      have h2 : ((2:ℕ) : ℚ_[2]) = 2 := by norm_num
      rw [h2, hilbertSymbol_two_formula, hilbertSymbol_two_formula, hilbertSymbol_two_formula]
      have key : ∀ r s r' s' : ZMod (2^3), r * r' = 1 → s * s' = 1 → 
          twoEps (r*s) % 2 = (twoEps r + twoEps s) % 2 ∧ twoOmega (r*s) % 2 = (twoOmega r + twoOmega s) % 2 := by
        unfold twoEps twoOmega
        decide
      have hinv : ∀ w : ℤ_[2]ˣ, PadicInt.toZModPow 3 (w : ℤ_[2]) * PadicInt.toZModPow 3 ((w⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
        intro w; rw [← map_mul, Units.mul_inv, map_one]
      obtain ⟨k1, k2⟩ := key _ _ _ _ (hinv u) (hinv u')
      rw [Units.val_mul, map_mul, ← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := _ + _)]
      congr 1
      have m1 : Nat.ModEq 2 (twoEps (PadicInt.toZModPow 3 (u:ℤ_[2]) * PadicInt.toZModPow 3 (u':ℤ_[2]))) (twoEps (PadicInt.toZModPow 3 (u:ℤ_[2])) + twoEps (PadicInt.toZModPow 3 (u':ℤ_[2]))) := k1
      have m2 : Nat.ModEq 2 (twoOmega (PadicInt.toZModPow 3 (u:ℤ_[2]) * PadicInt.toZModPow 3 (u':ℤ_[2]))) (twoOmega (PadicInt.toZModPow 3 (u:ℤ_[2])) + twoOmega (PadicInt.toZModPow 3 (u':ℤ_[2]))) := k2
      have := ((m1.mul_right (twoEps (PadicInt.toZModPow 3 (v:ℤ_[2])))).add_right ((α + α') * twoOmega (PadicInt.toZModPow 3 (v:ℤ_[2])))).add (m2.mul_left β)
      exact this.trans (congrArg (· % 2) (by ring))
    · rw [hilbertSymbol_odd_formula hp2, hilbertSymbol_odd_formula hp2, hilbertSymbol_odd_formula hp2]
      have hm : unitChar (u * u') = unitChar u * unitChar u' := by
        unfold unitChar; rw [Units.val_mul, map_mul, map_mul]
      rw [hm, add_mul, add_mul, pow_add, pow_add, mul_pow]
      ring
  have real : ∀ (a a' b : ℝ), a ≠ 0 → a' ≠ 0 → b ≠ 0 →
      hilbertSymbol ℝ (a * a') b = hilbertSymbol ℝ a b * hilbertSymbol ℝ a' b := by
    intro a a' b ha ha' hb
    have hR : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → hilbertSymbol ℝ x y = if x < 0 ∧ y < 0 then -1 else 1 := by
      intro x y hx hy
      unfold hilbertSymbol
      split_ifs with h1 h2 h2
      · exfalso
        obtain ⟨X, Y, Z, hne, heq⟩ := h1
        have hX2 : X ^ 2 = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y, sq_nonneg Z]
        have hY2 : Y ^ 2 = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y, sq_nonneg Z]
        have hZ2 : Z ^ 2 = 0 := by rw [heq, hX2, hY2]; ring
        apply hne
        simp [pow_eq_zero_iff, Prod.ext_iff] at hX2 hY2 hZ2 ⊢
        exact ⟨hX2, hY2, hZ2⟩
      · rfl
      · rfl
      · exfalso
        apply h1
        by_cases hx0 : 0 < x
        · refine ⟨1, 0, Real.sqrt x, by simp [Prod.ext_iff], ?_⟩
          rw [Real.sq_sqrt hx0.le]; ring
        · have hy0 : 0 < y := by
            rcases lt_or_gt_of_ne hy with h | h
            · exact absurd ⟨lt_of_le_of_ne (not_lt.1 hx0) hx, h⟩ h2
            · exact h
          refine ⟨0, 1, Real.sqrt y, by simp [Prod.ext_iff], ?_⟩
          rw [Real.sq_sqrt hy0.le]; ring
    rw [hR _ _ (mul_ne_zero ha ha') hb, hR _ _ ha hb, hR _ _ ha' hb]
    rcases lt_or_gt_of_ne ha with h1 | h1 <;> rcases lt_or_gt_of_ne ha' with h2 | h2 <;>
      rcases lt_or_gt_of_ne hb with h3 | h3 <;>
      simp [h1, h2, h3, h1.le, h2.le, h3.le, not_lt.2, mul_neg_of_pos_of_neg, mul_neg_of_neg_of_pos] <;> nlinarith
  cases v with
  | infinite =>
    show hilbertSymbol ℝ ((a * a' : ℚ) : ℝ) (b : ℝ) = hilbertSymbol ℝ (a : ℝ) (b : ℝ) * hilbertSymbol ℝ (a' : ℝ) (b : ℝ)
    rw [Rat.cast_mul]
    exact real _ _ _ (by exact_mod_cast ha) (by exact_mod_cast ha') (by exact_mod_cast hb)
  | finite q =>
    obtain ⟨p, hpp⟩ := q
    haveI : Fact p.Prime := ⟨hpp⟩
    show hilbertSymbol ℚ_[p] ((a * a' : ℚ) : ℚ_[p]) (b : ℚ_[p]) = hilbertSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) * hilbertSymbol ℚ_[p] (a' : ℚ_[p]) (b : ℚ_[p])
    rw [Rat.cast_mul]
    exact padic p _ _ _ (by exact_mod_cast ha) (by exact_mod_cast ha') (by exact_mod_cast hb)

end QuadFormsKB.HilbertLocal
