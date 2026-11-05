/-
# Cassels, Chapter 4, §3: the Witt group of $\mathbb Q_2$ (Lemma 3.2)

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 4, §3, *The Witt group*, Lemma 3.2 (p. 65).

**Setting.** As in `Ch4/Witt.lean`: $W(k)$ = `W k` is the Witt group of Chapter 2, §5, and
$\langle a\rangle$ = `gW a` for $a \in k^{\times}$ (`Ch2/WittRing.lean`). For $x \in \mathbb Q_2^{\times}$ write
$x = 2^{v}u$ with $u \in \mathbb Z_2^{\times}$ (`val 2 x`, `uc 2 x`). Its *square-class coordinates* are
$\mathrm{cd}(x) = (v \bmod 2, \varepsilon(u), \omega(u)) \in (\mathbb Z/2)^{3}$, where $\varepsilon(u) = \frac{u-1}{2}$ and
$\omega(u) = \frac{u^{2}-1}{8}$ modulo $2$ (`HilbertLocal.twoEps`, `HilbertLocal.twoOmega`, read off $u \bmod 8$).

**Proves.** Lemma 3.2: $W(\mathbb Q_2) \cong \mathbb Z/8 \oplus \mathbb Z/2 \oplus \mathbb Z/2$ (`witt_padic_two`).

**Proof notes.** The book's proof on p. 65 is illegible in the machine-read text; the proof here is reconstructed.
Generators: $\xi = \langle 1\rangle$ (order $8$), $\eta = \langle 2\rangle - \langle 1\rangle$ and $\theta = \langle 5\rangle - \langle 1\rangle$
(order $2$); the relations $8\xi = 2\eta = 2\theta = 0$ and the expressions of the eight classes
$\langle 1\rangle, \langle 3\rangle, \langle 5\rangle, \langle 7\rangle, \langle 2\rangle, \langle 6\rangle, \langle 10\rangle, \langle 14\rangle$
come from Cassels' relation (ii) for the pairs $(1,1), (1,2), (1,4), (1,5), (1,6), (1,7), (3,7)$, relation (iii), and the
squares $-7, 105 \in (\mathbb Q_2^{\times})^{2}$. The inverse map is defined on generators by
$\langle x\rangle \mapsto G(\mathrm{cd}(x))$ for an explicit $G\colon (\mathbb Z/2)^{3} \to \mathbb Z/8 \oplus \mathbb Z/2 \oplus \mathbb Z/2$;
relation (ii) for it reduces, by the Hilbert symbol identity $(a, b) = (a + b, ab(a+b))$ and the explicit formula for
$(\cdot,\cdot)_2$ (`HilbertLocal.hilbertSymbol_two_formula`), to a finite check.
-/
import QuadFormsKB.Literature.Cassels.Ch4.Witt
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiThree

open QuadraticMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.WittTwo

open QuadFormsKB.Cassels QuadFormsKB.HilbertLocal

/-! ### Square-class coordinates on $\mathbb Q_2^{\times}$ -/

/-- The coordinate group $(\mathbb Z/2)^{3}$ of $\mathbb Q_2^{\times}/(\mathbb Q_2^{\times})^{2}$. -/
abbrev C2 := ZMod 2 × ZMod 2 × ZMod 2

/-- The residue modulo $8$ of a $2$-adic unit. -/
def res8 (u : ℤ_[2]ˣ) : ZMod (2 ^ 3) := PadicInt.toZModPow 3 (u : ℤ_[2])

/-- $\varepsilon$ with values in $\mathbb Z/2$. -/
def epsC (r : ZMod (2 ^ 3)) : ZMod 2 := (twoEps r : ZMod 2)

/-- $\omega$ with values in $\mathbb Z/2$. -/
def omgC (r : ZMod (2 ^ 3)) : ZMod 2 := (twoOmega r : ZMod 2)

/-- The square-class coordinates $(v \bmod 2, \varepsilon(u), \omega(u))$ of $x = 2^{v}u$. -/
def cd (x : ℚ_[2]ˣ) : C2 := ((val 2 x : ZMod 2), epsC (res8 (uc 2 x)), omgC (res8 (uc 2 x)))

theorem epsC_mul : ∀ r s : ZMod (2 ^ 3), (∃ t, r * t = 1) → (∃ t, s * t = 1) →
    epsC (r * s) = epsC r + epsC s := by
  unfold epsC twoEps; decide

theorem omgC_mul : ∀ r s : ZMod (2 ^ 3), (∃ t, r * t = 1) → (∃ t, s * t = 1) →
    omgC (r * s) = omgC r + omgC s := by
  unfold omgC twoOmega; decide

theorem eq_one_of_cd : ∀ r : ZMod (2 ^ 3), (∃ t, r * t = 1) → epsC r = 0 → omgC r = 0 → r = 1 := by
  unfold epsC omgC twoEps twoOmega; decide

theorem res8_mul (u v : ℤ_[2]ˣ) : res8 (u * v) = res8 u * res8 v := by
  simp [res8]

theorem res8_unit (u : ℤ_[2]ˣ) : ∃ t, res8 u * t = 1 :=
  ⟨res8 u⁻¹, by rw [← res8_mul, mul_inv_cancel]; simp [res8]⟩

theorem cd_mul (x y : ℚ_[2]ˣ) : cd (x * y) = cd x + cd y := by
  obtain ⟨h1, h2⟩ := val_mul 2 x y
  simp only [cd, h1, h2, res8_mul, epsC_mul _ _ (res8_unit _) (res8_unit _),
    omgC_mul _ _ (res8_unit _) (res8_unit _), Int.cast_add, Prod.mk_add_mk]

theorem cd_of {x : ℚ_[2]ˣ} {l : ℤ} {u : ℤ_[2]ˣ} (h : (x : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) ^ l * ((u : ℤ_[2]) : ℚ_[2])) :
    cd x = ((l : ZMod 2), epsC (res8 u), omgC (res8 u)) := by
  obtain ⟨h1, h2⟩ := decomp_unique 2 h
  simp only [cd, h1, h2]

theorem C2_add_self : ∀ k : C2, k + k = 0 := by decide

theorem cd_one : cd 1 = 0 := by
  rw [cd_of (l := 0) (u := 1) (by simp)]
  simp only [res8, Units.val_one, map_one, epsC, omgC, twoEps, twoOmega]
  decide

theorem cd_neg_one : cd (-1) = (0, 1, 0) := by
  rw [cd_of (l := 0) (u := -1) (by simp)]
  simp only [res8, Units.val_neg, Units.val_one, map_neg, map_one, epsC, omgC, twoEps, twoOmega]
  decide

theorem cd_inv (x : ℚ_[2]ˣ) : cd x⁻¹ = cd x := by
  have h := cd_mul x x⁻¹
  rw [mul_inv_cancel, cd_one] at h
  calc cd x⁻¹ = cd x + (cd x + cd x⁻¹) := by rw [← add_assoc, C2_add_self, zero_add]
    _ = cd x := by rw [← h, add_zero]

/-! ### The Hilbert symbol in coordinates -/

/-- The bilinear form $B$ with $(x, y)_2 = (-1)^{B(\mathrm{cd}\,x, \mathrm{cd}\,y)}$. -/
def Bf (x y : C2) : ZMod 2 := x.2.1 * y.2.1 + x.1 * y.2.2 + y.1 * x.2.2

theorem neg_one_pow_eq_ite (N : ℕ) : (-1 : ℤ) ^ N = if (N : ZMod 2) = 0 then 1 else -1 := by
  rcases Nat.even_or_odd N with h | h
  · simp [h.neg_one_pow, (ZMod.natCast_eq_zero_iff_even).mpr h]
  · simp [h.neg_one_pow, ZMod.natCast_eq_zero_iff_even, Nat.not_even_iff_odd.mpr h]

/-- $x = (2^{m}u)\,(2^{-k})^{2}$ with $m = v + 2k \ge 0$. -/
theorem decomp_nat (x : ℚ_[2]ˣ) : ∃ (m : ℕ) (k : ℤ), (m : ℤ) = val 2 x + 2 * k ∧
    (x : ℚ_[2]) = ((2 : ℚ_[2]) ^ m * ((uc 2 x : ℤ_[2]) : ℚ_[2])) * ((2 : ℚ_[2]) ^ (-k)) ^ 2 := by
  have hv := abs_nonneg (val 2 x)
  have hle : 0 ≤ val 2 x + 2 * |val 2 x| := by cases abs_cases (val 2 x) <;> linarith
  refine ⟨(val 2 x + 2 * |val 2 x|).toNat, |val 2 x|, Int.toNat_of_nonneg hle, ?_⟩
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have e1 : (2 : ℚ_[2]) ^ (val 2 x + 2 * |val 2 x|).toNat = 2 ^ (val 2 x + 2 * |val 2 x|) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hle]
  have e2 : ((2 : ℚ_[2]) ^ (-|val 2 x|)) ^ 2 = 2 ^ (-|val 2 x| * 2) := by
    rw [zpow_mul]; norm_cast
  rw [e1, e2, mul_right_comm, ← zpow_add₀ h2, decomp 2 x]
  congr 2
  ring

theorem hilb_cd (x y : ℚ_[2]ˣ) :
    hilbertSymbol ℚ_[2] x y = if Bf (cd x) (cd y) = 0 then 1 else -1 := by
  obtain ⟨m, k, hm, hx⟩ := decomp_nat x
  obtain ⟨n, j, hn, hy⟩ := decomp_nat y
  have h2 : ∀ k : ℤ, (2 : ℚ_[2]) ^ (-k) ≠ 0 := fun k => zpow_ne_zero _ two_ne_zero
  rw [hx, HM3.hilbertSymbol_mul_sq_left _ _ _ _ (h2 k), hilbertSymbol_comm, hy,
    HM3.hilbertSymbol_mul_sq_left _ _ _ _ (h2 j), hilbertSymbol_comm, hilbertSymbol_two_formula,
    neg_one_pow_eq_ite]
  have hm2 : (val 2 x : ZMod 2) = (m : ZMod 2) := by
    have := congrArg (fun z : ℤ => (z : ZMod 2)) hm
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at this
    rw [this, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]
  have hn2 : (val 2 y : ZMod 2) = (n : ZMod 2) := by
    have := congrArg (fun z : ℤ => (z : ZMod 2)) hn
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at this
    rw [this, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]
  congr 1
  simp only [Bf, cd, hm2, hn2, epsC, omgC, res8]
  push_cast
  ring_nf

/-- The Hilbert symbol identity $(a, b) = (a + b, ab(a + b))$, from $\langle a, b\rangle \cong \langle a+b, ab(a+b)\rangle$. -/
theorem hilb_rel {K : Type*} [Field K] {a b : K} (hab : a + b ≠ 0) :
    hilbertSymbol K a b = hilbertSymbol K (a + b) (a * b * (a + b)) := by
  unfold QuadFormsKB.hilbertSymbol
  have key : (∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) ↔
      (∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = (a + b) * x ^ 2 + a * b * (a + b) * y ^ 2) := by
    constructor
    · rintro ⟨X, Y, z, hne, h⟩
      refine ⟨(a * X + b * Y) / (a + b), (X - Y) / (a + b), z, ?_, ?_⟩
      · intro h0
        simp only [Prod.mk_eq_zero, div_eq_zero_iff, hab, or_false] at h0
        apply hne
        have hXY : X = Y := sub_eq_zero.mp h0.2.1
        subst hXY
        have : (a + b) * X = 0 := by linear_combination h0.1
        have hX : X = 0 := (mul_eq_zero.mp this).resolve_left hab
        simp [hX, h0.2.2]
      · rw [h]; field_simp; ring
    · rintro ⟨x, y, z, hne, h⟩
      refine ⟨x + b * y, x - a * y, z, ?_, ?_⟩
      · intro h0
        simp only [Prod.mk_eq_zero] at h0
        apply hne
        have : (a + b) * y = 0 := by linear_combination h0.1 - h0.2.1
        have hy : y = 0 := (mul_eq_zero.mp this).resolve_left hab
        have hx : x = 0 := by linear_combination h0.1 - b * hy
        simp [hx, hy, h0.2.2]
      · rw [h]; ring
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.mp h1) h2
  · exact absurd (key.mpr h2) h1
  · rfl

theorem ite_pm_inj : ∀ s t : ZMod 2, ((if s = 0 then (1 : ℤ) else -1) = if t = 0 then 1 else -1) → s = t := by
  decide

theorem Bf_rel (a b : ℚ_[2]ˣ) (hab : (a : ℚ_[2]) + b ≠ 0) :
    Bf (cd a) (cd b) = Bf (cd (Units.mk0 _ hab)) (cd a + cd b + cd (Units.mk0 _ hab)) := by
  have h := hilb_rel hab
  rw [show (a : ℚ_[2]) + b = (Units.mk0 _ hab : ℚ_[2]) from rfl,
    show (a : ℚ_[2]) * b * (Units.mk0 _ hab : ℚ_[2]) = ((a * b * Units.mk0 _ hab : ℚ_[2]ˣ) : ℚ_[2]) by
      push_cast; rfl, hilb_cd, hilb_cd, cd_mul, cd_mul] at h
  exact ite_pm_inj _ _ h

/-! ### The map $\Psi\colon W(\mathbb Q_2) \to \mathbb Z/8 \oplus \mathbb Z/2 \oplus \mathbb Z/2$ -/

/-- The value of $\Psi$ on $\langle x\rangle$ in terms of $\mathrm{cd}(x) = (e, \alpha, \beta)$:
$(1 - 2\alpha + 4e\beta, e, \beta)$. -/
def G (k : C2) : ZMod 8 × ZMod 2 × ZMod 2 :=
  ((if k.2.1 = 0 then 1 else 7) + (if k.1 = 1 ∧ k.2.2 = 1 then 4 else 0), k.1, k.2.2)

theorem G_rel : ∀ x y z : C2, Bf x y = Bf z (x + y + z) → G x + G y = G z + G (x + y + z) := by
  unfold G Bf; decide

theorem G_rel3 : G 0 + G (0, 1, 0) = 0 := by decide

theorem gΨ_rel1 (a b : ℚ_[2]ˣ) : G (cd (a * b ^ 2)) = G (cd a) := by
  rw [cd_mul, _root_.sq, cd_mul, C2_add_self, add_zero]

theorem gΨ_rel2 (a b : ℚ_[2]ˣ) (hab : (a : ℚ_[2]) + b ≠ 0) :
    G (cd a) + G (cd b) = G (cd (Units.mk0 _ hab)) + G (cd (a * b * Units.mk0 _ hab)) := by
  rw [cd_mul, cd_mul]
  exact G_rel _ _ _ (Bf_rel a b hab)

theorem gΨ_rel3 : G (cd 1) + G (cd (-1)) = 0 := by
  rw [cd_one, cd_neg_one]; exact G_rel3

/-- The map $\Psi\colon W(\mathbb Q_2) \to \mathbb Z/8 \oplus \mathbb Z/2 \oplus \mathbb Z/2$, $\langle x\rangle \mapsto G(\mathrm{cd}\,x)$. -/
def Ψ2 : W ℚ_[2] →+ ZMod 8 × ZMod 2 × ZMod 2 :=
  (W_lift (fun x => G (cd x)) gΨ_rel1 gΨ_rel2 gΨ_rel3).choose

theorem Ψ2_gen (x : ℚ_[2]ˣ) : Ψ2 (gW x) = G (cd x) :=
  (W_lift (fun x => G (cd x)) gΨ_rel1 gΨ_rel2 gΨ_rel3).choose_spec.1 x

/-! ### Squares and representatives -/

/-- **Hensel.** A $2$-adic integer $\equiv 1 \pmod 8$ is a square. -/
theorem sq_of_res8 (w : ℤ_[2]) (hw : PadicInt.toZModPow 3 w = 1) : ∃ s : ℤ_[2], s ^ 2 = w := by
  have h1 : w - 1 ∈ Ideal.span {((2:ℕ):ℤ_[2])^3} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hw, map_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
  have h2 : ‖((2:ℕ):ℤ_[2])‖ = 1/2 := by rw [PadicInt.norm_p]; norm_num
  have h2' : ‖(2:ℤ_[2])‖ = 1/2 := by exact_mod_cast h2
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := 2) (F := (Polynomial.X ^ 2 - Polynomial.C w : Polynomial ℤ_[2]))
    (a := 1) (by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Polynomial.derivative_X_pow, Polynomial.derivative_C, one_pow, sub_zero, map_mul,
      Algebra.algebraMap_self, RingHom.id_apply]
    have e1 : (1:ℤ_[2]) - w = -(c * ((2:ℕ):ℤ_[2])^3) := by rw [hc]; ring
    rw [e1, norm_neg, norm_mul, norm_pow, h2]
    norm_num
    rw [h2']
    nlinarith [norm_nonneg c, c.norm_le_one])
  refine ⟨z, ?_⟩
  simp at hz
  linear_combination hz

theorem sq_of_cd {y : ℚ_[2]ˣ} (h : cd y = 0) : ∃ s : ℚ_[2]ˣ, y = s ^ 2 := by
  simp only [cd, Prod.mk_eq_zero] at h
  obtain ⟨hv, he, ho⟩ := h
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (val 2 y) 2).mp hv
  have hr := eq_one_of_cd _ (res8_unit _) he ho
  obtain ⟨z, hz⟩ := sq_of_res8 _ hr
  have hz0 : (z : ℚ_[2]) ≠ 0 := by
    intro h0
    have : z = 0 := PadicInt.coe_eq_zero.mp h0
    rw [this, zero_pow two_ne_zero] at hz
    exact (uc 2 y).ne_zero hz.symm
  refine ⟨Units.mk0 ((2 : ℚ_[2]) ^ k * (z : ℚ_[2])) (mul_ne_zero (zpow_ne_zero _ two_ne_zero) hz0), Units.ext ?_⟩
  rw [decomp 2 y, Units.val_pow_eq_pow_val, Units.val_mk0, mul_pow, ← PadicInt.coe_pow, hz, hk]
  push_cast
  rw [← zpow_natCast, ← zpow_mul, mul_comm k]
  rfl

/-- The representative $2^{e}u$ ($u \in \{1, 3, 5, 7\}$) of the square class with coordinates $(e, \alpha, \beta)$. -/
def repQ (k : C2) : ℚ_[2] :=
  (if k.1 = 1 then 2 else 1) * (if k.2.1 = 0 then (if k.2.2 = 0 then 1 else 5) else (if k.2.2 = 0 then 7 else 3))

theorem repQ_ne_zero (k : C2) : repQ k ≠ 0 := by
  unfold repQ
  split_ifs <;> norm_num

/-- The representative as a unit. -/
def rep (k : C2) : ℚ_[2]ˣ := Units.mk0 (repQ k) (repQ_ne_zero k)

/-- An odd integer as a $2$-adic unit. -/
def oddU (m : ℤ) (hm : (m : ZMod 2) ≠ 0) : ℤ_[2]ˣ :=
  (isUnit_of_toZMod_ne_zero 2 (z := (m : ℤ_[2])) (by rw [map_intCast]; exact hm)).unit

theorem coe_oddU (m : ℤ) (hm : (m : ZMod 2) ≠ 0) : ((oddU m hm : ℤ_[2]) : ℚ_[2]) = m := by
  simp [oddU]

theorem res8_oddU (m : ℤ) (hm : (m : ZMod 2) ≠ 0) : res8 (oddU m hm) = (m : ZMod (2 ^ 3)) := by
  simp [res8, oddU]

/-- $\mathrm{cd}(2^{l}m) = (l, \varepsilon(m), \omega(m))$ for an odd integer $m$. -/
theorem cd_int (x : ℚ_[2]ˣ) (l : ℕ) (m : ℤ) (hm : (m : ZMod 2) ≠ 0) (hx : (x : ℚ_[2]) = 2 ^ l * m) :
    cd x = ((l : ZMod 2), epsC (m : ZMod (2 ^ 3)), omgC (m : ZMod (2 ^ 3))) := by
  rw [cd_of (l := l) (u := oddU m hm) (by rw [hx, coe_oddU]; push_cast; rw [zpow_natCast]), res8_oddU]
  simp

theorem cd_rep : ∀ k : C2, cd (rep k) = k := by
  rintro ⟨e, α, β⟩
  fin_cases e <;> fin_cases α <;> fin_cases β
  · rw [cd_int _ 0 1 (by decide) (by simp +decide [rep, repQ])]; unfold epsC omgC twoEps twoOmega; decide
  · rw [cd_int _ 0 5 (by decide) (by simp +decide [rep, repQ])]; unfold epsC omgC twoEps twoOmega; decide
  · rw [cd_int _ 0 7 (by decide) (by simp +decide [rep, repQ])]; unfold epsC omgC twoEps twoOmega; decide
  · rw [cd_int _ 0 3 (by decide) (by simp +decide [rep, repQ])]; unfold epsC omgC twoEps twoOmega; decide
  · rw [cd_int _ 1 1 (by decide) (by simp +decide [rep, repQ])]; unfold epsC omgC twoEps twoOmega; decide
  · rw [cd_int _ 1 5 (by decide) (by simp +decide [rep, repQ])]; unfold epsC omgC twoEps twoOmega; decide
  · rw [cd_int _ 1 7 (by decide) (by simp +decide [rep, repQ])]; unfold epsC omgC twoEps twoOmega; decide
  · rw [cd_int _ 1 3 (by decide) (by simp +decide [rep, repQ])]; unfold epsC omgC twoEps twoOmega; decide

/-- Every $\langle x\rangle$ equals $\langle r\rangle$ for the representative $r$ of the square class of $x$. -/
theorem gW_rep (x : ℚ_[2]ˣ) : gW x = gW (rep (cd x)) := by
  have h0 : cd (x * (rep (cd x))⁻¹) = 0 := by rw [cd_mul, cd_inv, cd_rep, C2_add_self]
  obtain ⟨s, hs⟩ := sq_of_cd h0
  have : x = rep (cd x) * s ^ 2 := by rw [← hs, mul_comm x, mul_inv_cancel_left]
  conv_lhs => rw [this]
  rw [gW_sq]

/-! ### Relations among the representatives in $W(\mathbb Q_2)$ -/

/-- $\langle q\rangle$ for $q \in \mathbb Q_2$, with the convention $\langle 0\rangle = 0$ (bookkeeping only). -/
def w (q : ℚ_[2]) : W ℚ_[2] :=
  haveI := Classical.dec (q = 0)
  if h : q = 0 then 0 else gW (Units.mk0 q h)

theorem w_unit (x : ℚ_[2]ˣ) : w x = gW x := by
  unfold w; rw [dite_eq_right_of_eq_false (eq_false x.ne_zero), Units.mk0_val]

theorem w_eq {q q' : ℚ_[2]} (s : ℚ_[2]) (hq' : q' ≠ 0) (hs : s ≠ 0) (h : q = q' * s ^ 2) : w q = w q' := by
  have hqs : q' * s ^ 2 ≠ 0 := mul_ne_zero hq' (pow_ne_zero 2 hs)
  unfold w
  rw [h, dite_eq_right_of_eq_false (eq_false hqs), dite_eq_right_of_eq_false (eq_false hq'),
    show Units.mk0 (q' * s ^ 2) hqs = Units.mk0 q' hq' * (Units.mk0 s hs) ^ 2 from Units.ext (by simp), gW_sq]

theorem w_add {q r s t : ℚ_[2]} (hq : q ≠ 0) (hr : r ≠ 0) (hs0 : s ≠ 0) (hs : q + r = s)
    (ht : q * r * s = t) : w q + w r = w s + w t := by
  have hqr : ((Units.mk0 q hq : ℚ_[2]ˣ) : ℚ_[2]) + (Units.mk0 r hr : ℚ_[2]ˣ) ≠ 0 := by
    rw [Units.val_mk0, Units.val_mk0, hs]; exact hs0
  have h := gW_add (Units.mk0 q hq) (Units.mk0 r hr) hqr
  rw [← w_unit, ← w_unit, ← w_unit, ← w_unit] at h
  simp only [Units.val_mul, Units.val_mk0] at h
  rw [hs] at h
  rw [← ht, h]

theorem w_one_neg : w 1 + w (-1) = 0 := by
  have h := gW_add_neg (1 : ℚ_[2]ˣ)
  rw [← w_unit, ← w_unit] at h
  simpa using h

theorem exists_sq_int {c : ℤ} (hc : PadicInt.toZModPow 3 (c : ℤ_[2]) = 1) (hc0 : c ≠ 0) :
    ∃ t : ℚ_[2], t ≠ 0 ∧ t ^ 2 = c := by
  obtain ⟨z, hz⟩ := sq_of_res8 (c : ℤ_[2]) hc
  have e : (z : ℚ_[2]) ^ 2 = c := by rw [← PadicInt.coe_pow, hz]; push_cast; rfl
  refine ⟨z, ?_, e⟩
  rintro h0
  rw [h0, zero_pow two_ne_zero] at e
  exact hc0 (by exact_mod_cast e.symm)

theorem sq105 : ∃ t : ℚ_[2], t ≠ 0 ∧ t ^ 2 = 105 := by
  obtain ⟨t, h0, ht⟩ := exists_sq_int (c := 105) (by rw [map_intCast]; decide) (by norm_num)
  exact ⟨t, h0, by rw [ht]; norm_num⟩

theorem sqm7 : ∃ t : ℚ_[2], t ≠ 0 ∧ t ^ 2 = -7 := by
  obtain ⟨t, h0, ht⟩ := exists_sq_int (c := -7) (by rw [map_intCast]; decide) (by norm_num)
  exact ⟨t, h0, by rw [ht]; norm_num⟩

theorem w4 : w 4 = w 1 := w_eq 2 one_ne_zero two_ne_zero (by norm_num)
theorem w8 : w 8 = w 2 := w_eq 2 two_ne_zero two_ne_zero (by norm_num)
theorem w20 : w 20 = w 5 := w_eq 2 (by norm_num) two_ne_zero (by norm_num)
theorem w56 : w 56 = w 14 := w_eq 2 (by norm_num) two_ne_zero (by norm_num)

theorem w_neg1 : w (-1) = w 7 := by
  obtain ⟨t, h0, ht⟩ := sqm7
  exact w_eq (t / 7) (by norm_num) (div_ne_zero h0 (by norm_num)) (by rw [div_pow, ht]; norm_num)

theorem w30 : w 30 = w 14 := by
  obtain ⟨t, h0, ht⟩ := sq105
  exact w_eq (t / 7) (by norm_num) (div_ne_zero h0 (by norm_num)) (by rw [div_pow, ht]; norm_num)

theorem w210 : w 210 = w 2 := by
  obtain ⟨t, h0, ht⟩ := sq105
  exact w_eq t two_ne_zero h0 (by rw [ht]; norm_num)

theorem w42 : w 42 = w 10 := by
  obtain ⟨t, h0, ht⟩ := sq105
  exact w_eq (t / 5) (by norm_num) (div_ne_zero h0 (by norm_num)) (by rw [div_pow, ht]; norm_num)

theorem R0 : w 1 + w 7 = 0 := by rw [← w_neg1]; exact w_one_neg
theorem R11 : w 1 + w 1 = w 2 + w 2 := w_add (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem R14 : w 1 + w 1 = w 5 + w 5 := by
  have h := w_add (q := 1) (r := 4) (s := 5) (t := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  rwa [w4, w20] at h
theorem R17 : w 1 + w 7 = w 2 + w 14 := by
  rw [← w8, ← w56]; exact w_add (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem R15 : w 1 + w 5 = w 6 + w 14 := by
  rw [← w30]; exact w_add (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem R12 : w 1 + w 2 = w 3 + w 6 := w_add (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem R37 : w 3 + w 7 = w 10 + w 2 := by
  rw [← w210]; exact w_add (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem R16 : w 1 + w 6 = w 7 + w 10 := by
  rw [← w42]; exact w_add (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem s7 : w 7 = -w 1 := by linear_combination R0
theorem s14 : w 14 = -w 2 := by linear_combination -R17 + s7
theorem s6 : w 6 = w 1 + w 2 + w 5 := by linear_combination -R15 - s14
theorem s3 : w 3 = -w 5 := by linear_combination -R12 - s6
theorem s10 : w 10 = 3 * w 1 + w 2 + w 5 := by linear_combination -R16 + s6 - s7
theorem s10' : w 10 = -w 1 - w 2 - w 5 := by linear_combination -R37 + s3 + s7
theorem T2b : 2 * w 1 = 2 * w 2 := by linear_combination R11
theorem T2c : 2 * w 1 = 2 * w 5 := by linear_combination R14
theorem T8 : 8 * w 1 = 0 := by linear_combination -s10 + s10' + T2b + T2c

/-! ### The map $\Phi\colon \mathbb Z/8 \oplus \mathbb Z/2 \oplus \mathbb Z/2 \to W(\mathbb Q_2)$ -/

/-- $\Phi(i, j, l) = i\xi + j\eta + l\theta$ with $\xi = \langle 1\rangle$, $\eta = \langle 2\rangle - \langle 1\rangle$,
$\theta = \langle 5\rangle - \langle 1\rangle$. -/
def Φ2 : ZMod 8 × ZMod 2 × ZMod 2 →+ W ℚ_[2] :=
  (ZMod.lift 8 ⟨zmultiplesHom _ (w 1), by
      simp only [zmultiplesHom_apply, Nat.cast_ofNat, zsmul_eq_mul, Int.cast_ofNat]; exact T8⟩).coprod
    ((ZMod.lift 2 ⟨zmultiplesHom _ (w 2 - w 1), by
      simp only [zmultiplesHom_apply, Nat.cast_ofNat, zsmul_eq_mul, Int.cast_ofNat]
      linear_combination -T2b⟩).coprod
    (ZMod.lift 2 ⟨zmultiplesHom _ (w 5 - w 1), by
      simp only [zmultiplesHom_apply, Nat.cast_ofNat, zsmul_eq_mul, Int.cast_ofNat]
      linear_combination -T2c⟩))

theorem lift_val {n : ℕ} [NeZero n] {A : Type*} [AddCommGroup A] (f : {f : ℤ →+ A // f n = 0}) (i : ZMod n) :
    ZMod.lift n f i = f.1 (i.val : ℤ) := by
  have := ZMod.lift_coe n f (i.val : ℤ)
  rwa [Int.cast_natCast, ZMod.natCast_zmod_val] at this

theorem Φ2_apply (i : ZMod 8) (j l : ZMod 2) :
    Φ2 (i, j, l) = (i.val : W ℚ_[2]) * w 1 + (j.val : W ℚ_[2]) * (w 2 - w 1) + (l.val : W ℚ_[2]) * (w 5 - w 1) := by
  simp only [Φ2, AddMonoidHom.coprod_apply, lift_val, zmultiplesHom_apply, zsmul_eq_mul, Int.cast_natCast]
  ring

theorem key000 : Φ2 (G (0, 0, 0)) = w (repQ (0, 0, 0)) := by
  rw [show G (0, 0, 0) = (1, 0, 0) by decide, show repQ (0, 0, 0) = 1 by simp +decide [repQ], Φ2_apply]
  simp only [show (1 : ZMod 8).val = 1 from rfl, show (0 : ZMod 2).val = 0 from rfl]
  push_cast; ring
theorem key001 : Φ2 (G (0, 0, 1)) = w (repQ (0, 0, 1)) := by
  rw [show G (0, 0, 1) = (1, 0, 1) by decide, show repQ (0, 0, 1) = 5 by simp +decide [repQ], Φ2_apply]
  simp only [show (1 : ZMod 8).val = 1 from rfl, show (0 : ZMod 2).val = 0 from rfl,
    show (1 : ZMod 2).val = 1 from rfl]
  push_cast; ring
theorem key010 : Φ2 (G (0, 1, 0)) = w (repQ (0, 1, 0)) := by
  rw [show G (0, 1, 0) = (7, 0, 0) by decide, show repQ (0, 1, 0) = 7 by simp +decide [repQ], Φ2_apply]
  simp only [show (7 : ZMod 8).val = 7 from rfl, show (0 : ZMod 2).val = 0 from rfl]
  push_cast; linear_combination T8 - s7
theorem key011 : Φ2 (G (0, 1, 1)) = w (repQ (0, 1, 1)) := by
  rw [show G (0, 1, 1) = (7, 0, 1) by decide, show repQ (0, 1, 1) = 3 by simp +decide [repQ], Φ2_apply]
  simp only [show (7 : ZMod 8).val = 7 from rfl, show (0 : ZMod 2).val = 0 from rfl,
    show (1 : ZMod 2).val = 1 from rfl]
  push_cast; linear_combination T8 - s3 - T2c
theorem key100 : Φ2 (G (1, 0, 0)) = w (repQ (1, 0, 0)) := by
  rw [show G (1, 0, 0) = (1, 1, 0) by decide, show repQ (1, 0, 0) = 2 by simp +decide [repQ], Φ2_apply]
  simp only [show (1 : ZMod 8).val = 1 from rfl, show (0 : ZMod 2).val = 0 from rfl,
    show (1 : ZMod 2).val = 1 from rfl]
  push_cast; ring
theorem key101 : Φ2 (G (1, 0, 1)) = w (repQ (1, 0, 1)) := by
  rw [show G (1, 0, 1) = (5, 1, 1) by decide, show repQ (1, 0, 1) = 10 by simp +decide [repQ]; norm_num,
    Φ2_apply]
  simp only [show (5 : ZMod 8).val = 5 from rfl, show (1 : ZMod 2).val = 1 from rfl]
  push_cast; linear_combination -s10
theorem key110 : Φ2 (G (1, 1, 0)) = w (repQ (1, 1, 0)) := by
  rw [show G (1, 1, 0) = (7, 1, 0) by decide, show repQ (1, 1, 0) = 14 by simp +decide [repQ]; norm_num,
    Φ2_apply]
  simp only [show (7 : ZMod 8).val = 7 from rfl, show (0 : ZMod 2).val = 0 from rfl,
    show (1 : ZMod 2).val = 1 from rfl]
  push_cast; linear_combination T8 - s14 - T2b
theorem key111 : Φ2 (G (1, 1, 1)) = w (repQ (1, 1, 1)) := by
  rw [show G (1, 1, 1) = (3, 1, 1) by decide, show repQ (1, 1, 1) = 6 by simp +decide [repQ]; norm_num,
    Φ2_apply]
  simp only [show (3 : ZMod 8).val = 3 from rfl, show (1 : ZMod 2).val = 1 from rfl]
  push_cast; linear_combination -s6

theorem key : ∀ k : C2, Φ2 (G k) = w (repQ k) := by
  rintro ⟨e, α, β⟩
  fin_cases e <;> fin_cases α <;> fin_cases β
  exacts [key000, key001, key010, key011, key100, key101, key110, key111]

theorem Φ2_Ψ2 : Φ2.comp Ψ2 = AddMonoidHom.id _ := by
  refine W_hom_ext _ _ fun x => ?_
  rw [AddMonoidHom.comp_apply, Ψ2_gen, key, AddMonoidHom.id_apply, gW_rep x, ← w_unit]
  rfl

theorem Ψ2_w {q : ℚ_[2]} (hq : q ≠ 0) : Ψ2 (w q) = G (cd (Units.mk0 q hq)) := by
  unfold w; rw [dite_eq_right_of_eq_false (eq_false hq), Ψ2_gen]

theorem Ψ2_Φ2 : Ψ2.comp Φ2 = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun ⟨i, j, l⟩ => ?_
  have h1 : Ψ2 (w 1) = (1, 0, 0) := by
    rw [Ψ2_w one_ne_zero, cd_int _ 0 1 (by decide) (by simp)]; unfold epsC omgC twoEps twoOmega; decide
  have h2 : Ψ2 (w 2) = (1, 1, 0) := by
    rw [Ψ2_w two_ne_zero, cd_int _ 1 1 (by decide) (by simp)]; unfold epsC omgC twoEps twoOmega; decide
  have h5 : Ψ2 (w 5) = (1, 0, 1) := by
    rw [Ψ2_w (by norm_num), cd_int _ 0 5 (by decide) (by simp)]; unfold epsC omgC twoEps twoOmega; decide
  have hΦ : Φ2 (i, j, l) = (i.val : ℤ) • w 1 + (j.val : ℤ) • (w 2 - w 1) + (l.val : ℤ) • (w 5 - w 1) := by
    rw [Φ2_apply]; simp only [zsmul_eq_mul, Int.cast_natCast]
  rw [AddMonoidHom.comp_apply, hΦ, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_sub, map_sub, h1, h2, h5,
    AddMonoidHom.id_apply]
  ext <;> simp

end QuadFormsKB.Cassels.WittTwo

namespace QuadFormsKB.Cassels

open WittTwo

/-- **Cassels, Ch. 4, Lemma 3.2.** $W(\mathbb Q_2)$ is the direct sum of a cyclic group of order $8$ and two cyclic
groups of order $2$: $W(\mathbb Q_2) \cong \mathbb Z/8 \oplus \mathbb Z/2 \oplus \mathbb Z/2$, with
$\langle 1\rangle \mapsto (1, 0, 0)$, $\langle 2\rangle - \langle 1\rangle \mapsto (0, 1, 0)$ and
$\langle 5\rangle - \langle 1\rangle \mapsto (0, 0, 1)$. (The book's proof on p. 65 is illegible in the machine-read text;
the proof here is reconstructed, see the module docstring.) -/
@[kb "cassels1978" "Ch. 4, Lemma 3.2, p. 65"]
theorem witt_padic_two : Nonempty (W ℚ_[2] ≃+ ZMod 8 × ZMod 2 × ZMod 2) :=
  ⟨AddMonoidHom.toAddEquiv Ψ2 Φ2 Φ2_Ψ2 Ψ2_Φ2⟩

end QuadFormsKB.Cassels
