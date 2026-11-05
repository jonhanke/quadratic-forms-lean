/-
# Cassels, Chapter 3: Example 10 (a Hilbert symbol identity)

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 3, *Examples*, Ex. 10, p. 50.

**Setting.** $p$ is a prime and $(a, b)_p$ is the Hilbert symbol of $\mathbb Q_p$ (`hilbertSymbol ℚ_[p] a b`, Serre's
definition, which is Cassels' definition of §2, p. 41).

**Proves.** Ex. 10: if $a + b + c = 0$ with $a, b, c \in \mathbb Q_p^{\times}$, then
$(a, b)_p (b, c)_p (c, a)_p = (-1, -abc)_p$ (`ex10`). The displayed identity is partly lost in the machine-read text;
it is reconstructed from the legible fragments ("$(-1, -abc)_p$" and three symbols) and checked by the proof.
-/
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiThree

namespace QuadFormsKB.Cassels.Ch3Ex

variable {p : ℕ} [Fact p.Prime]

/-- Every Hilbert symbol squares to $1$. -/
theorem hilbertSymbol_sq (K : Type*) [Field K] (u v : K) : hilbertSymbol K u v ^ 2 = 1 := by
  unfold hilbertSymbol
  split_ifs <;> norm_num

/-- Bimultiplicativity in the second argument, over $\mathbb Q_p$. -/
theorem hilbertSymbol_padic_mul_right (u v v' : ℚ_[p]) (hu : u ≠ 0) (hv : v ≠ 0) (hv' : v' ≠ 0) :
    hilbertSymbol ℚ_[p] u (v * v') = hilbertSymbol ℚ_[p] u v * hilbertSymbol ℚ_[p] u v' := by
  rw [hilbertSymbol_comm, HilbertLocal.hilbertSymbol_padic_mul_left _ _ _ hv hv' hu, hilbertSymbol_comm,
    hilbertSymbol_comm _ v' u]

/-- **Cassels, Ch. 3, Ex. 10 (p. 50).** Let $a, b, c \in \mathbb Q_p^{\times}$ with $a + b + c = 0$. Then
$$(a, b)_p\,(b, c)_p\,(c, a)_p = (-1, -abc)_p.$$
(Reconstructed: the display is partly illegible in the machine-read text.) -/
@[kb "cassels1978" "Ch. 3, Ex. 10, p. 50"]
theorem ex10 {a b c : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h : a + b + c = 0) :
    hilbertSymbol ℚ_[p] a b * hilbertSymbol ℚ_[p] b c * hilbertSymbol ℚ_[p] c a =
      hilbertSymbol ℚ_[p] (-1) (-(a * b * c)) := by
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  have hm1 : (-1 : ℚ_[p]) ≠ 0 := by norm_num
  have ml := fun u u' v (hu : u ≠ 0) (hu' : u' ≠ 0) (hv : v ≠ 0) =>
    HilbertLocal.hilbertSymbol_padic_mul_left (p := p) u u' v hu hu' hv
  have mr := fun u v v' (hu : u ≠ 0) (hv : v ≠ 0) (hv' : v' ≠ 0) =>
    hilbertSymbol_padic_mul_right (p := p) u v v' hu hv hv'
  -- $x = -a/c$, $y = -b/c$ have $x + y = 1$, so $(x, y) = 1$, i.e. $(-ac, -bc) = 1$.
  have hxy : (-a / c) * 1 ^ 2 + (-b / c) * 1 ^ 2 = 1 := by
    field_simp
    linear_combination -h
  have h1 : hilbertSymbol ℚ_[p] (-a / c) (-b / c) = 1 :=
    (hilbertSymbol_eq_one_iff_conic _ h2 (div_ne_zero (neg_ne_zero.mpr ha) hc)
      (div_ne_zero (neg_ne_zero.mpr hb) hc)).mpr ⟨1, 1, hxy⟩
  have ea : -a / c = (-1) * a * c * c⁻¹ ^ 2 := by field_simp
  have eb : -b / c = (-1) * b * c * c⁻¹ ^ 2 := by field_simp
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hc
  rw [ea, eb, HM3.hilbertSymbol_mul_sq_left _ _ _ _ hci, hilbertSymbol_comm,
    HM3.hilbertSymbol_mul_sq_left _ _ _ _ hci, hilbertSymbol_comm] at h1
  have n1 : (-1 : ℚ_[p]) * a ≠ 0 := mul_ne_zero hm1 ha
  have n2 : (-1 : ℚ_[p]) * b ≠ 0 := mul_ne_zero hm1 hb
  have n3 : (-1 : ℚ_[p]) * b * c ≠ 0 := mul_ne_zero n2 hc
  rw [ml _ _ _ n1 hc n3, ml _ _ _ hm1 ha n3, mr _ _ _ hm1 n2 hc, mr _ _ _ hm1 hm1 hb, mr _ _ _ ha n2 hc,
    mr _ _ _ ha hm1 hb, mr _ _ _ hc n2 hc, mr _ _ _ hc hm1 hb] at h1
  have hcc : hilbertSymbol ℚ_[p] c c = hilbertSymbol ℚ_[p] c (-1) := by
    have h0 := hilbertSymbol_self_neg ℚ_[p] c
    rw [show -c = (-1) * c by ring, mr _ _ _ hc hm1 hc] at h0
    have hs := hilbertSymbol_sq ℚ_[p] c (-1)
    linear_combination hilbertSymbol ℚ_[p] c (-1) * h0 - hilbertSymbol ℚ_[p] c c * hs
  have hn : -(a * b * c) = (-1) * a * b * c := by ring
  rw [hn, mr _ _ _ hm1 (mul_ne_zero (mul_ne_zero hm1 ha) hb) hc, mr _ _ _ hm1 (mul_ne_zero hm1 ha) hb,
    mr _ _ _ hm1 hm1 ha]
  rw [hcc, hilbertSymbol_comm _ a (-1), hilbertSymbol_comm _ c (-1), hilbertSymbol_comm _ c b,
    hilbertSymbol_comm _ a c] at h1
  set A := hilbertSymbol ℚ_[p] (-1) (-1)
  set P := hilbertSymbol ℚ_[p] (-1) a
  set Q := hilbertSymbol ℚ_[p] (-1) b
  set R := hilbertSymbol ℚ_[p] (-1) c
  set X := hilbertSymbol ℚ_[p] a b
  set Y := hilbertSymbol ℚ_[p] b c
  set Z := hilbertSymbol ℚ_[p] c a
  have hX : X ^ 2 = 1 := hilbertSymbol_sq _ _ _
  have hY : Y ^ 2 = 1 := hilbertSymbol_sq _ _ _
  have hZ : Z ^ 2 = 1 := hilbertSymbol_sq _ _ _
  have hR : R ^ 2 = 1 := hilbertSymbol_sq _ _ _
  linear_combination (-(X * Y * Z)) * h1 + (A * P * Q * R) * (Y ^ 2 * Z ^ 2 * R ^ 2 * hX + Z ^ 2 * R ^ 2 * hY +
    R ^ 2 * hZ + hR)

end QuadFormsKB.Cassels.Ch3Ex
