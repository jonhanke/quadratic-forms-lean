/-
# Cassels, Chapter 11, §3: spinor norms of $2$-adic lattices (Lemma 3.8)

**Layer:** $V_2 = \mathbb Q_2^n$, the completion of $\mathbb Q^n$ at the prime $v \mid 2$ of $\mathcal O_{\mathbb Q}$,
with $Q$ = `Q : QuadForm ℚ n`; a lattice $L$ = `L : Lat ℚ n`, its localization $\Lambda_2 = L_v$ = `loc v L.1` with a
basis $b_k = \gamma e_k$ (the columns of $\gamma$, `loc v L.1 = locAct v γ (std v)`), the matrix $G = \gamma^tH\gamma$
of $B(x, y) = Q(x+y) - Q(x) - Q(y)$ on this basis (`locGram`, `Ch11Sec3Local.lean`), so that $G_{kk} = 2\phi(b_k)$ and
$G_{kl} = 2\phi(b_k, b_l)$ in Cassels' notation; $\theta(\Lambda_2)$ = `localSpinorNormGroup`.

**Proves** Cassels' Lemma 3.8 (p. 214; "the proof is left to the reader"): in each of the following cases every
$2$-adic unit is in $\theta(\Lambda_2)$ (as in Lemma 3.7, the lattice of Cassels' lemma is an orthogonal summand of the
basis, using the remark on direct orthogonal summands, p. 213):
* (i) `units_mem_localSpinorNormGroup_two_binary`: $b_i, b_j$ ($i \ne j$) span an orthogonal summand on which the form
  is $\phi(x_ib_i + x_jb_j) = 2^e(a x_i^2 + x_ix_j + c x_j^2)$ with $a, c \in \mathbb Z_2$, i.e. $\lvert G_{ii}\rvert,
  \lvert G_{jj}\rvert \le \lvert 2G_{ij}\rvert$, $G_{ij} \ne 0$;
* (ii) `units_mem_localSpinorNormGroup_two_ternary`: $b_i, b_j, b_k$ are orthogonal to each other and to the other
  basis vectors, $\lvert\phi(b_i)\rvert = \lvert\phi(b_j)\rvert$, and $\lvert\phi(b_k)\rvert$ equals $\lvert\phi(b_i)\rvert$,
  $\tfrac12\lvert\phi(b_i)\rvert$ or $2\lvert\phi(b_i)\rvert$;
* (iii) `units_mem_localSpinorNormGroup_two_ternary'`: as in (ii) but $\lvert\phi(b_j)\rvert = \tfrac12\lvert\phi(b_i)\rvert$,
  $\lvert\phi(b_k)\rvert = \tfrac14\lvert\phi(b_i)\rvert$.

*Reconstruction.* The scan of p. 214 has lost most of the formulas of Lemma 3.8. Case (i) is reconstructed from the
proof of the Corollary (p. 215: "the direct orthogonal sum of $1$-dimensional lattices and of $2$-dimensional lattices
of type (i)", i.e. the binary $2$-adic Jordan components $2^ex_1x_2$ and $2^e(x_1^2 + x_1x_2 + x_2^2)$ of Ch. 8,
Lemma 4.1, which are the two forms printed in (i)); here the common generalization with $a, c$ arbitrary is stated.
In (ii) and (iii) the valuations $v_2(\phi(b_i)), v_2(\phi(b_j)), v_2(\phi(b_k))$ are $(e, e, e)$, $(e, e, e+1)$,
$(e, e, e-1)$ and $(e, e+1, e+2)$; these are the patterns the Corollary excludes to obtain the exponent
$\tfrac12n(n-3) + [\tfrac12(n+1)] = 0 + 0 + 2 + 2 + 4 + 4 + \cdots$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local
import QuadFormsKB.Tamagawa.Indefinite.OneClassExample

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ} (Q : QuadForm ℚ n) {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-! ### Proof infrastructure

*Arithmetic of $\mathbb Z_2$.* Residues mod $8$ (`Rl`), Hensel's lemma for $y^2 + y + e$, and the cover of the unit
classes $\{1, 3, 5, -1\}$ by two products of values of the ternary form (`unit_cover`, `pattern_cover`).
*Lattice side.* The symmetries $\tau_x$, $x = \gamma c$, $c \in \mathfrak o^n$, that lie in $O(L_v)$, and the
membership predicate `InT` for $\theta(O^+(L_v))$ (stated for a general number field, to avoid the diamond
`Algebra ℚ (v.adicCompletion ℚ)`). -/

/-- The ternary form $ps^2 + qt^2 + rz^2$. -/
def Bf {R : Type*} [CommRing R] (p q r s t z : R) : R := p * s ^ 2 + q * t ^ 2 + r * z ^ 2

section Dyad

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.NF

theorem two_eq_pi_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : ∃ w : 𝔬, IsUnit w ∧ (2 : 𝔬) = π v * w := by
  have he := ordTwo_spec v
  rw [Tamagawa.Indefinite.ordTwo_eq_one h2] at he
  obtain ⟨w, hw⟩ := he.1
  refine ⟨w, DVR.dvr_isUnit_of_not_dvd (irreducible_π v) fun hd => he.2 ?_, by simpa using hw⟩
  obtain ⟨c, rfl⟩ := hd
  exact ⟨c, by rw [hw]; ring⟩

/-- $2$ is a non-unit of $\mathbb Z_2$. -/
theorem two_mem_max (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : (2 : 𝔬) ∈ IsLocalRing.maximalIdeal 𝔬 := by
  obtain ⟨w, -, hw⟩ := two_eq_pi_mul h2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hw]
  intro hu
  exact (irreducible_π v).not_isUnit (isUnit_of_mul_isUnit_left hu)

theorem eight_dvd_of_pi_cube (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {y : 𝔬} (hy : π v ^ 3 ∣ y) : (8 : 𝔬) ∣ y := by
  obtain ⟨w, hw, h⟩ := two_eq_pi_mul h2
  obtain ⟨u, rfl⟩ := hw
  refine dvd_trans ?_ hy
  refine ⟨((u⁻¹ : 𝔬ˣ) : 𝔬) ^ 3, ?_⟩
  have : π v = 2 * ((u⁻¹ : 𝔬ˣ) : 𝔬) := by
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  rw [this]; ring

/-- Every element of $\mathbb Z_2$ is an integer plus a multiple of $8$. -/
theorem exists_int_cong (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (x : 𝔬) : ∃ (z : ℤ) (m : 𝔬), x = z + 8 * m := by
  obtain ⟨r, hr⟩ := redHom_surjective v 3 (Ideal.Quotient.mk _ x)
  have hr' : π v ^ 3 ∣ x - ι v r := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hr.symm)
  set z : ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) r
  have hzr : ι v r = (z : 𝔬) := by
    have : (z : 𝓞 ℚ) = r := by
      rw [← Tamagawa.RatHeadline3.intEquiv_symm_intCast]
      exact RingEquiv.symm_apply_apply _ r
    rw [← this, map_intCast]
  rw [hzr] at hr'
  obtain ⟨m, hm⟩ := eight_dvd_of_pi_cube h2 hr'
  exact ⟨z, m, by linear_combination hm⟩

/-- Residue mod $8$: $x \equiv a$ with $a \in \mathbb Z/8$. -/
def Rl (x : 𝔬) (a : ZMod 8) : Prop := ∃ (z : ℤ) (m : 𝔬), (z : ZMod 8) = a ∧ x = z + 8 * m

theorem Rl.add {x y : 𝔬} {a b : ZMod 8} (hx : Rl x a) (hy : Rl y b) : Rl (x + y) (a + b) := by
  obtain ⟨z, m, rfl, rfl⟩ := hx
  obtain ⟨z', m', rfl, rfl⟩ := hy
  exact ⟨z + z', m + m', by push_cast; rfl, by push_cast; ring⟩

theorem Rl.mul {x y : 𝔬} {a b : ZMod 8} (hx : Rl x a) (hy : Rl y b) : Rl (x * y) (a * b) := by
  obtain ⟨z, m, rfl, rfl⟩ := hx
  obtain ⟨z', m', rfl, rfl⟩ := hy
  exact ⟨z * z', z * m' + m * z' + 8 * m * m', by push_cast; rfl, by push_cast; ring⟩

theorem Rl.natCast (k : ℕ) : Rl (k : 𝔬) (k : ZMod 8) := ⟨k, 0, by simp, by simp⟩

theorem Rl.neg {x : 𝔬} {a : ZMod 8} (hx : Rl x a) : Rl (-x) (-a) := by
  obtain ⟨z, m, rfl, rfl⟩ := hx
  exact ⟨-z, -m, by push_cast; rfl, by push_cast; ring⟩

theorem Rl.sub {x y : 𝔬} {a b : ZMod 8} (hx : Rl x a) (hy : Rl y b) : Rl (x - y) (a - b) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem Rl.two : Rl (2 : 𝔬) 2 := by simpa using Rl.natCast (v := v) 2

theorem Rl.pow_two {x : 𝔬} {a : ZMod 8} (hx : Rl x a) : Rl (x ^ 2) (a ^ 2) := by
  simpa [sq] using hx.mul hx

theorem Rl.exists (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (x : 𝔬) : ∃ a, Rl x a := by
  obtain ⟨z, m, h⟩ := exists_int_cong h2 x
  exact ⟨z, z, m, rfl, h⟩

/-- Odd residues mod $8$. -/
def Od (a : ZMod 8) : Prop := a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7

instance (a : ZMod 8) : Decidable (Od a) := by unfold Od; infer_instance

theorem int_mod_of_cast {z : ℤ} {a : ZMod 8} (h : (z : ZMod 8) = a) (n : ℤ) (hn : (n : ZMod 8) = a) :
    (8 : ℤ) ∣ n - z := by
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub z n 8).mp (h.trans hn.symm)
  exact_mod_cast this

theorem Rl.of_cast {x : 𝔬} {n : ℤ} (hx : Rl x (n : ZMod 8)) : ∃ m : 𝔬, x = n + 8 * m := by
  obtain ⟨z, m, hz, rfl⟩ := hx
  obtain ⟨k, hk⟩ := int_mod_of_cast hz n rfl
  refine ⟨m - k, ?_⟩
  have : (z : 𝔬) = n - 8 * k := by
    have : z = n - 8 * k := by omega
    rw [this]; push_cast; ring
  rw [this]; ring

theorem isUnit_one_add_two_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (t : 𝔬) : IsUnit (1 + 2 * t) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro h
  have h1 : (1 : 𝔬) ∈ IsLocalRing.maximalIdeal 𝔬 := by
    have := Ideal.sub_mem _ h (Ideal.mul_mem_right t _ (two_mem_max h2))
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal (1 : 𝔬)).mp h1 isUnit_one

/-- An element with an odd residue mod $8$ is a unit. -/
theorem Rl.od_unit (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : 𝔬} {a : ZMod 8} (hx : Rl x a) (ha : Od a) :
    IsUnit x := by
  rcases ha with rfl | rfl | rfl | rfl
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := 1) (by simpa using hx)
    have := isUnit_one_add_two_mul h2 (4 * m)
    convert this using 1; rw [hm]; push_cast; ring
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := 3) (by simpa using hx)
    have := isUnit_one_add_two_mul h2 (1 + 4 * m)
    convert this using 1; rw [hm]; push_cast; ring
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := 5) (by simpa using hx)
    have := isUnit_one_add_two_mul h2 (2 + 4 * m)
    convert this using 1; rw [hm]; push_cast; ring
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := 7) (by simpa using hx)
    have := isUnit_one_add_two_mul h2 (3 + 4 * m)
    convert this using 1; rw [hm]; push_cast; ring

theorem Rl.even {x : 𝔬} {a : ZMod 8} (hx : Rl x a) (k : ZMod 8) (ha : a = 2 * k) : ∃ y : 𝔬, x = 2 * y := by
  obtain ⟨z, m, hz, rfl⟩ := hx
  have hn : (((2 * k.val : ℕ) : ℤ) : ZMod 8) = a := by
    rw [ha]; push_cast; rw [ZMod.natCast_zmod_val]
  obtain ⟨t, ht⟩ := int_mod_of_cast hz _ hn
  refine ⟨k.val + 4 * (m - t), ?_⟩
  have : (z : 𝔬) = 2 * (k.val : ℤ) - 8 * t := by
    have : z = 2 * (k.val : ℤ) - 8 * t := by push_cast at ht; omega
    rw [this]; push_cast; ring
  rw [this]; push_cast; ring

theorem not_od_even : ∀ a : ZMod 8, ¬ Od a → ∃ k : ZMod 8, a = 2 * k := by decide

theorem od_sub_even : ∀ a b : ZMod 8, Od a → Od b → ∃ k : ZMod 8, a - b = 2 * k := by decide

/-- A unit has an odd residue mod $8$. -/
theorem Rl.unit_od (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : 𝔬} {a : ZMod 8} (hx : Rl x a) (hu : IsUnit x) :
    Od a := by
  by_contra hna
  obtain ⟨k, hk⟩ := not_od_even a hna
  obtain ⟨y, rfl⟩ := hx.even k hk
  have := (IsLocalRing.mem_maximalIdeal (2 * y)).mp (Ideal.mul_mem_right y _ (two_mem_max h2))
  exact this hu

/-- Two units of $\mathbb Z_2$ differ by a non-unit. -/
theorem sub_mem_max (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x y : 𝔬} (hx : IsUnit x) (hy : IsUnit y) :
    x - y ∈ IsLocalRing.maximalIdeal 𝔬 := by
  obtain ⟨a, ha⟩ := Rl.exists h2 x
  obtain ⟨b, hb⟩ := Rl.exists h2 y
  have h1 := ha.unit_od h2 hx
  have h2' := hb.unit_od h2 hy
  obtain ⟨k, hk⟩ := od_sub_even a b h1 h2'
  obtain ⟨t, ht⟩ := (ha.sub hb).even k hk
  rw [ht]
  exact Ideal.mul_mem_right t _ (two_mem_max h2)

/-- Hensel's lemma for $y^2 + y + e$, $e \in \mathfrak m$. -/
theorem exists_quad_root (e : 𝔬) (he : e ∈ IsLocalRing.maximalIdeal 𝔬) :
    ∃ y : 𝔬, y ∈ IsLocalRing.maximalIdeal 𝔬 ∧ y ^ 2 + y + e = 0 := by
  have hmon : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C e : Polynomial 𝔬).Monic := by monicity!
  obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C e)
    hmon 0 (by simpa using he) (by simp)
  refine ⟨a, by simpa using ha', ?_⟩
  simpa using ha

/-- $1 + 8m$ is a square in $\mathbb Z_2$. -/
theorem exists_sq_one_add_eight (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (m : 𝔬) : ∃ s : 𝔬, s ^ 2 = 1 + 8 * m := by
  obtain ⟨y, -, hy⟩ := exists_quad_root (-(2 * m))
    (Ideal.neg_mem_iff _ |>.mpr (Ideal.mul_mem_right m _ (two_mem_max h2)))
  exact ⟨1 + 2 * y, by linear_combination 4 * hy⟩

/-- $ct^2 + t + d = 0$ is solvable in $\mathbb Z_2$ when $cd \in \mathfrak m$. -/
theorem solve_quad (c d : 𝔬) (hcd : c * d ∈ IsLocalRing.maximalIdeal 𝔬) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ t : 𝔬, c * t ^ 2 + t + d = 0 := by
  obtain ⟨y, hym, hy⟩ := exists_quad_root (c * d) hcd
  have hu : IsUnit (1 + y) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro h
    have h1 : (1 : 𝔬) ∈ IsLocalRing.maximalIdeal 𝔬 := by
      have := Ideal.sub_mem _ h hym
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal (1 : 𝔬)).mp h1 isUnit_one
  obtain ⟨k, hk⟩ : ∃ k : 𝔬, (1 + y) * k = 1 := by
    obtain ⟨u, hu⟩ := hu
    exact ⟨((u⁻¹ : 𝔬ˣ) : 𝔬), by rw [← hu]; simp⟩
  refine ⟨-d * k, ?_⟩
  linear_combination (d * k ^ 2) * hy + (-d * (1 + k * y)) * hk

/-- **Every unit of $\mathbb Z_2$ is a value of $as^2 + st + ct^2$, $a, c \in \mathbb Z_2$.** -/
theorem exists_binary_value (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (a c w : 𝔬) (hw : IsUnit w) :
    ∃ s t : 𝔬, a * s ^ 2 + s * t + c * t ^ 2 = w := by
  by_cases h : IsUnit a ∨ c ∈ IsLocalRing.maximalIdeal 𝔬
  · have hcd : c * (a - w) ∈ IsLocalRing.maximalIdeal 𝔬 := by
      rcases h with ha | hc
      · exact Ideal.mul_mem_left _ _ (sub_mem_max h2 ha hw)
      · exact Ideal.mul_mem_right _ _ hc
    obtain ⟨t, ht⟩ := solve_quad c (a - w) hcd h2
    exact ⟨1, t, by linear_combination ht⟩
  · push Not at h
    have ha : a ∈ IsLocalRing.maximalIdeal 𝔬 := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h.1
    have hcd : a * (c - w) ∈ IsLocalRing.maximalIdeal 𝔬 := Ideal.mul_mem_right _ _ ha
    obtain ⟨s, hs⟩ := solve_quad a (c - w) hcd h2
    exact ⟨s, 1, by linear_combination hs⟩

/-- $x \equiv y \pmod 8$ with $y$ a unit makes $x$ a unit times a square. -/
theorem cong_sq (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x y : 𝔬} (hy : IsUnit y) (m : 𝔬) (hxy : x = y + 8 * m) :
    ∃ s : 𝔬, IsUnit s ∧ x = y * s ^ 2 := by
  obtain ⟨k, hk⟩ : ∃ k, y * k = 1 := hy.exists_right_inv
  obtain ⟨s, hs⟩ := exists_sq_one_add_eight h2 (m * k)
  refine ⟨s, ?_, ?_⟩
  · have : IsUnit (s ^ 2) := by
      rw [hs]
      have := isUnit_one_add_two_mul h2 (4 * (m * k))
      convert this using 1; ring
    exact (isUnit_pow_iff two_ne_zero).mp this
  · rw [hs, hxy]; linear_combination (-(8 * m)) * hk

/-- **The abstract cover of the unit classes:** if a predicate `M` on $\mathbb Z_2$ is multiplicative on units,
insensitive to unit squares, holds at $1$, and holds at some $\alpha \equiv 5$ and some $\beta \equiv 3 \pmod 4$
(mod $8$: $\beta \equiv 3$ or $7$), then it holds at every unit. -/
theorem unit_cover (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (M : 𝔬 → Prop)
    (hmul : ∀ x y, IsUnit x → IsUnit y → M x → M y → M (x * y))
    (hsq : ∀ x s, IsUnit x → IsUnit s → (M (x * s ^ 2) ↔ M x)) (hone : M 1)
    {α β : 𝔬} (hMα : M α) (hα : Rl α 5) (hMβ : M β) (hβ : Rl β 3 ∨ Rl β 7) :
    ∀ u : 𝔬, IsUnit u → M u := by
  have hcong : ∀ x y m : 𝔬, IsUnit y → x = y + 8 * m → (M x ↔ M y) := by
    intro x y m hy hxy
    obtain ⟨s, hs, rfl⟩ := cong_sq h2 hy m hxy
    exact hsq y s hy hs
  have u3 : IsUnit (3 : 𝔬) := by
    have := isUnit_one_add_two_mul h2 1; convert this using 1; norm_num
  have u5 : IsUnit (5 : 𝔬) := by
    have := isUnit_one_add_two_mul h2 2; convert this using 1; norm_num
  have um1 : IsUnit (-1 : 𝔬) := isUnit_one.neg
  have um5 : IsUnit (-5 : 𝔬) := u5.neg
  obtain ⟨ma, hma⟩ := Rl.of_cast (n := 5) (by simpa using hα)
  push_cast at hma
  have M5 : M 5 := (hcong α 5 ma u5 hma).mp hMα
  have M3m1 : M 3 ∧ M (-1) := by
    rcases hβ with h3 | h7
    · obtain ⟨mb, hmb⟩ := Rl.of_cast (n := 3) (by simpa using h3)
      push_cast at hmb
      have M3 : M 3 := (hcong _ 3 mb u3 hmb).mp hMβ
      have M15 : M 15 := by
        have := hmul 3 5 u3 u5 M3 M5
        norm_num at this; exact this
      exact ⟨M3, (hcong 15 (-1) 2 um1 (by norm_num)).mp M15⟩
    · obtain ⟨mb, hmb⟩ := Rl.of_cast (n := 7) (by simpa using h7)
      push_cast at hmb
      have Mm1 : M (-1) := (hcong β (-1) (mb + 1) um1 (by rw [hmb]; ring)).mp hMβ
      have Mm5 : M (-5) := by
        have := hmul (-1) 5 um1 u5 Mm1 M5
        norm_num at this; exact this
      exact ⟨(hcong 3 (-5) 1 um5 (by norm_num)).mpr Mm5, Mm1⟩
  intro u hu
  obtain ⟨c, hc, s, rfl⟩ := Tamagawa.Indefinite.exists_unit_eq_mul_sq h2 hu
  have hcu : IsUnit (c : 𝔬) := isUnit_of_mul_isUnit_left hu
  have hsu : IsUnit s := (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_right hu)
  refine (hsq _ s hcu hsu).mpr ?_
  rcases hc with rfl | rfl | rfl | rfl
  · simpa using hone
  · simpa using M3m1.1
  · simpa using M5
  · simpa using M3m1.2

/-! #### Pairs of values of the ternary form -/

/-- Residue of $B(s,t,z)$ for residues $a_p, a_q, a_r$ and natural numbers $s, t, z$. -/
def rs (ap aq ar : ZMod 8) (s t z : ℕ) : ZMod 8 :=
  ap * (s : ZMod 8) ^ 2 + aq * (t : ZMod 8) ^ 2 + ar * (z : ZMod 8) ^ 2

/-- Two unit values of the ternary form whose product satisfies `P`. -/
def HasPair (p q r : 𝔬) (P : 𝔬 → Prop) : Prop :=
  ∃ s t z s' t' z' : 𝔬, IsUnit (Bf p q r s t z) ∧ IsUnit (Bf p q r s' t' z') ∧
    P (Bf p q r s t z * Bf p q r s' t' z')

theorem Bf_res {p q r : 𝔬} {ap aq ar : ZMod 8} (hp : Rl p ap) (hq : Rl q aq) (hr : Rl r ar) (s t z : ℕ) :
    Rl (Bf p q r (s : 𝔬) (t : 𝔬) (z : 𝔬)) (rs ap aq ar s t z) :=
  ((hp.mul (Rl.natCast s).pow_two).add (hq.mul (Rl.natCast t).pow_two)).add (hr.mul (Rl.natCast z).pow_two)

theorem hasPair_res (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {p q r : 𝔬} {ap aq ar : ZMod 8} (hp : Rl p ap) (hq : Rl q aq)
    (hr : Rl r ar) (s t z s' t' z' : ℕ) {P : 𝔬 → Prop} {a : ZMod 8} (hP : ∀ x, Rl x a → P x)
    (h1 : Od (rs ap aq ar s t z)) (h1' : Od (rs ap aq ar s' t' z'))
    (hprod : rs ap aq ar s t z * rs ap aq ar s' t' z' = a) : HasPair p q r P :=
  ⟨s, t, z, s', t', z', (Bf_res hp hq hr s t z).od_unit h2 h1, (Bf_res hp hq hr s' t' z').od_unit h2 h1',
    hP _ (hprod ▸ (Bf_res hp hq hr s t z).mul (Bf_res hp hq hr s' t' z'))⟩

theorem hasPair_res37 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {p q r : 𝔬} {ap aq ar : ZMod 8} (hp : Rl p ap)
    (hq : Rl q aq) (hr : Rl r ar) (s t z s' t' z' : ℕ) (h1 : Od (rs ap aq ar s t z))
    (h1' : Od (rs ap aq ar s' t' z'))
    (hprod : rs ap aq ar s t z * rs ap aq ar s' t' z' = 3 ∨ rs ap aq ar s t z * rs ap aq ar s' t' z' = 7) :
    HasPair p q r (fun x => Rl x 3 ∨ Rl x 7) := by
  rcases hprod with h | h
  · exact hasPair_res h2 hp hq hr s t z s' t' z' (a := 3) (fun x hx => Or.inl hx) h1 h1' h
  · exact hasPair_res h2 hp hq hr s t z s' t' z' (a := 7) (fun x hx => Or.inr hx) h1 h1' h

/-- The unit patterns of Cassels' Lemma 3.8 (ii), (iii), after dividing by the smallest coefficient. -/
def Pat (p q r : 𝔬) : Prop :=
  (IsUnit p ∧ IsUnit q ∧ IsUnit r) ∨
  (IsUnit p ∧ IsUnit q ∧ ∃ r', IsUnit r' ∧ r = 2 * r') ∨
  (IsUnit p ∧ ∃ q' r', IsUnit q' ∧ IsUnit r' ∧ q = 2 * q' ∧ r = 2 * r') ∨
  (IsUnit p ∧ ∃ q' r', IsUnit q' ∧ IsUnit r' ∧ q = 2 * q' ∧ r = 4 * r')

theorem resA5 : ∀ ap aq ar : ZMod 8, Od ap → Od aq → Od ar →
    Od (rs ap aq ar 1 0 0) ∧ Od (rs ap aq ar 1 2 0) ∧ rs ap aq ar 1 0 0 * rs ap aq ar 1 2 0 = 5 := by decide

theorem resA3 : ∀ ap aq ar : ZMod 8, Od ap → Od aq → Od ar →
    (Od (rs ap aq ar 1 0 0) ∧ Od (rs ap aq ar 0 1 0) ∧
      (rs ap aq ar 1 0 0 * rs ap aq ar 0 1 0 = 3 ∨ rs ap aq ar 1 0 0 * rs ap aq ar 0 1 0 = 7)) ∨
    (Od (rs ap aq ar 1 0 0) ∧ Od (rs ap aq ar 0 0 1) ∧
      (rs ap aq ar 1 0 0 * rs ap aq ar 0 0 1 = 3 ∨ rs ap aq ar 1 0 0 * rs ap aq ar 0 0 1 = 7)) ∨
    (Od (rs ap aq ar 1 0 0) ∧ Od (rs ap aq ar 1 1 1) ∧
      (rs ap aq ar 1 0 0 * rs ap aq ar 1 1 1 = 3 ∨ rs ap aq ar 1 0 0 * rs ap aq ar 1 1 1 = 7)) := by decide

theorem resB5 : ∀ ap aq ar : ZMod 8, Od ap → Od aq → Od ar →
    Od (rs ap aq (2 * ar) 1 0 0) ∧ Od (rs ap aq (2 * ar) 1 2 0) ∧
      rs ap aq (2 * ar) 1 0 0 * rs ap aq (2 * ar) 1 2 0 = 5 := by decide

theorem resB3 : ∀ ap aq ar : ZMod 8, Od ap → Od aq → Od ar →
    Od (rs ap aq (2 * ar) 1 0 0) ∧ Od (rs ap aq (2 * ar) 1 0 1) ∧
      (rs ap aq (2 * ar) 1 0 0 * rs ap aq (2 * ar) 1 0 1 = 3 ∨
        rs ap aq (2 * ar) 1 0 0 * rs ap aq (2 * ar) 1 0 1 = 7) := by decide

theorem resC3 : ∀ ap aq ar : ZMod 8, Od ap → Od aq → Od ar →
    Od (rs ap (2 * aq) (2 * ar) 1 0 0) ∧ Od (rs ap (2 * aq) (2 * ar) 1 1 0) ∧
      (rs ap (2 * aq) (2 * ar) 1 0 0 * rs ap (2 * aq) (2 * ar) 1 1 0 = 3 ∨
        rs ap (2 * aq) (2 * ar) 1 0 0 * rs ap (2 * aq) (2 * ar) 1 1 0 = 7) := by decide

theorem resC5 : ∀ ap aq ar : ZMod 8, Od ap → Od aq → Od ar →
    (Od (rs ap (2 * aq) (2 * ar) 1 0 0) ∧ Od (rs ap (2 * aq) (2 * ar) 1 1 1) ∧
      rs ap (2 * aq) (2 * ar) 1 0 0 * rs ap (2 * aq) (2 * ar) 1 1 1 = 5) ∨
    (Od (rs ap (2 * aq) (2 * ar) 1 1 0) ∧ Od (rs ap (2 * aq) (2 * ar) 1 0 1) ∧
      rs ap (2 * aq) (2 * ar) 1 1 0 * rs ap (2 * aq) (2 * ar) 1 0 1 = 5) := by decide

theorem resD5 : ∀ ap aq ar : ZMod 8, Od ap → Od aq → Od ar →
    Od (rs ap (2 * aq) (4 * ar) 1 0 0) ∧ Od (rs ap (2 * aq) (4 * ar) 1 0 1) ∧
      rs ap (2 * aq) (4 * ar) 1 0 0 * rs ap (2 * aq) (4 * ar) 1 0 1 = 5 := by decide

theorem resD3 : ∀ ap aq ar : ZMod 8, Od ap → Od aq → Od ar →
    Od (rs ap (2 * aq) (4 * ar) 1 0 0) ∧ Od (rs ap (2 * aq) (4 * ar) 1 1 0) ∧
      (rs ap (2 * aq) (4 * ar) 1 0 0 * rs ap (2 * aq) (4 * ar) 1 1 0 = 3 ∨
        rs ap (2 * aq) (4 * ar) 1 0 0 * rs ap (2 * aq) (4 * ar) 1 1 0 = 7) := by decide

theorem Rl.unit_exists (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : 𝔬} (hx : IsUnit x) : ∃ a, Rl x a ∧ Od a := by
  obtain ⟨a, ha⟩ := Rl.exists h2 x
  exact ⟨a, ha, ha.unit_od h2 hx⟩

/-- **Cover of the unit classes by the ternary patterns:** in each pattern there are two pairs of unit values of
$ps^2 + qt^2 + rz^2$ whose products are $\equiv 5 \pmod 8$, respectively $\equiv 3 \pmod 4$. -/
theorem pattern_cover (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {p q r : 𝔬} (h : Pat p q r) :
    HasPair p q r (fun x => Rl x 5) ∧ HasPair p q r (fun x => Rl x 3 ∨ Rl x 7) := by
  rcases h with ⟨hp, hq, hr⟩ | ⟨hp, hq, r', hr', rfl⟩ | ⟨hp, q', r', hq', hr', rfl, rfl⟩ |
    ⟨hp, q', r', hq', hr', rfl, rfl⟩
  · obtain ⟨ap, hp1, hp2⟩ := Rl.unit_exists h2 hp
    obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
    obtain ⟨ar, hr1, hr2⟩ := Rl.unit_exists h2 hr
    refine ⟨?_, ?_⟩
    · obtain ⟨k1, k2, k3⟩ := resA5 ap aq ar hp2 hq2 hr2
      exact hasPair_res h2 hp1 hq1 hr1 1 0 0 1 2 0 (fun x hx => hx) k1 k2 k3
    · rcases resA3 ap aq ar hp2 hq2 hr2 with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
      · exact hasPair_res37 h2 hp1 hq1 hr1 1 0 0 0 1 0 k1 k2 k3
      · exact hasPair_res37 h2 hp1 hq1 hr1 1 0 0 0 0 1 k1 k2 k3
      · exact hasPair_res37 h2 hp1 hq1 hr1 1 0 0 1 1 1 k1 k2 k3
  · obtain ⟨ap, hp1, hp2⟩ := Rl.unit_exists h2 hp
    obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq
    obtain ⟨ar, hr1, hr2⟩ := Rl.unit_exists h2 hr'
    have hr1' := Rl.two.mul hr1
    refine ⟨?_, ?_⟩
    · obtain ⟨k1, k2, k3⟩ := resB5 ap aq ar hp2 hq2 hr2
      exact hasPair_res h2 hp1 hq1 hr1' 1 0 0 1 2 0 (fun x hx => hx) k1 k2 k3
    · obtain ⟨k1, k2, k3⟩ := resB3 ap aq ar hp2 hq2 hr2
      exact hasPair_res37 h2 hp1 hq1 hr1' 1 0 0 1 0 1 k1 k2 k3
  · obtain ⟨ap, hp1, hp2⟩ := Rl.unit_exists h2 hp
    obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq'
    obtain ⟨ar, hr1, hr2⟩ := Rl.unit_exists h2 hr'
    have hq1' := Rl.two.mul hq1
    have hr1' := Rl.two.mul hr1
    refine ⟨?_, ?_⟩
    · rcases resC5 ap aq ar hp2 hq2 hr2 with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
      · exact hasPair_res h2 hp1 hq1' hr1' 1 0 0 1 1 1 (fun x hx => hx) k1 k2 k3
      · exact hasPair_res h2 hp1 hq1' hr1' 1 1 0 1 0 1 (fun x hx => hx) k1 k2 k3
    · obtain ⟨k1, k2, k3⟩ := resC3 ap aq ar hp2 hq2 hr2
      exact hasPair_res37 h2 hp1 hq1' hr1' 1 0 0 1 1 0 k1 k2 k3
  · obtain ⟨ap, hp1, hp2⟩ := Rl.unit_exists h2 hp
    obtain ⟨aq, hq1, hq2⟩ := Rl.unit_exists h2 hq'
    obtain ⟨ar, hr1, hr2⟩ := Rl.unit_exists h2 hr'
    have hq1' := Rl.two.mul hq1
    have h4 : Rl (4 : 𝔬) 4 := by simpa using Rl.natCast (v := v) 4
    have hr1' : Rl (4 * r') (4 * ar) := h4.mul hr1
    refine ⟨?_, ?_⟩
    · obtain ⟨k1, k2, k3⟩ := resD5 ap aq ar hp2 hq2 hr2
      exact hasPair_res h2 hp1 hq1' hr1' 1 0 0 1 0 1 (fun x hx => hx) k1 k2 k3
    · obtain ⟨k1, k2, k3⟩ := resD3 ap aq ar hp2 hq2 hr2
      exact hasPair_res37 h2 hp1 hq1' hr1' 1 0 0 1 1 0 k1 k2 k3

end Dyad

/-! ### Membership in $\theta$ and admissible symmetries (general number field) -/

section Spin

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {Q : QuadForm F n} {v : HeightOneSpectrum (𝓞 F)}
  (hQ : Q.Nondegenerate) (L : Lat F n)

local notation "Fw" => v.adicCompletion F
local notation "𝔬w" => v.adicCompletionIntegers F

/-- `a` is a nonzero element of $\theta(O^+(L_v))$. -/
def InT (a : Fw) : Prop := ∃ h : a ≠ 0, Units.mk0 a h ∈ localSpinorNormGroup Q hQ v L

/-- Squares are in $\theta(O^+(L_v))$. -/
theorem sq_mem_T (g : Fwˣ) : g ^ 2 ∈ localSpinorNormGroup Q hQ v L := by
  rw [localSpinorNormGroup, Subgroup.mem_comap, map_pow, sq, SqClass.mul_self]
  exact Subgroup.one_mem _

theorem InT.mul {a b : Fw} (ha : InT hQ L a) (hb : InT hQ L b) : InT hQ L (a * b) := by
  obtain ⟨ha0, ha⟩ := ha
  obtain ⟨hb0, hb⟩ := hb
  refine ⟨mul_ne_zero ha0 hb0, ?_⟩
  have := (localSpinorNormGroup Q hQ v L).mul_mem ha hb
  rwa [← Units.mk0_mul] at this

theorem InT.one : InT hQ L (1 : Fw) := ⟨one_ne_zero, by rw [Units.mk0_one]; exact Subgroup.one_mem _⟩

theorem InT.sq_mul_iff {a b : Fw} (hb : b ≠ 0) : InT hQ L (a * b ^ 2) ↔ InT hQ L a := by
  have hsq : InT hQ L (b ^ 2) := ⟨pow_ne_zero 2 hb, by
    have := sq_mem_T hQ L (Units.mk0 b hb)
    convert this using 1; ext; simp⟩
  have hsq' : InT hQ L ((b⁻¹) ^ 2) := ⟨pow_ne_zero 2 (inv_ne_zero hb), by
    have := sq_mem_T hQ L (Units.mk0 b⁻¹ (inv_ne_zero hb))
    convert this using 1; ext; simp⟩
  constructor
  · intro h
    have := InT.mul hQ L h hsq'
    convert this using 1
    field_simp
  · intro h; exact InT.mul hQ L h hsq

theorem InT.mem {u : Fwˣ} (h : InT hQ L (u : Fw)) : u ∈ localSpinorNormGroup Q hQ v L := by
  obtain ⟨h0, hm⟩ := h
  simpa using hm

theorem InT.of_symm_pair {x y : Fin n → Fw} (hx0 : Q.evalIn Fw x ≠ 0) (hy0 : Q.evalIn Fw y ≠ 0)
    (hxs : symm Q Fw x ∈ locStabV Q v L) (hys : symm Q Fw y ∈ locStabV Q v L) :
    InT hQ L (Q.evalIn Fw x * Q.evalIn Fw y) :=
  ⟨mul_ne_zero hx0 hy0, mem_localSpinorNormGroup_of_symm_pair hQ L hx0 hy0 hxs hys _
    (sqClassOf_of_ne_zero (mul_ne_zero hx0 hy0))⟩

theorem gram_dot_symm (γ : GL (Fin n) Fw) (c d : Fin n → Fw) :
    c ⬝ᵥ (locGram Q v γ *ᵥ d) = (locGram Q v γ *ᵥ c) ⬝ᵥ d := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, locGram_transpose]

theorem vle_one (x : 𝔬w) : Valued.v (x : Fw) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp x.2

/-- **A symmetry $\tau_x$, $x = \gamma c$, $c \in \mathfrak o^n$, lies in $O(L_v)$** when
$\lvert(Gc)_m\rvert \le \lvert Q(x)\rvert$ for all $m$. -/
theorem symm_mem_of_gram (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v)) {c : Fin n → Fw}
    (hc : c ∈ std v) (hx0 : Q.evalIn Fw (γ.val *ᵥ c) ≠ 0)
    (hb : ∀ m, Valued.v ((locGram Q v γ *ᵥ c) m) ≤ Valued.v (Q.evalIn Fw (γ.val *ᵥ c))) :
    symm Q Fw (γ.val *ᵥ c) ∈ locStabV Q v L := by
  have hxM : γ.val *ᵥ c ∈ loc v L.1 := by rw [hγ]; exact ⟨c, hc, rfl⟩
  show locAct v (symm Q Fw (γ.val *ᵥ c) : GL (Fin n) Fw) (loc v L.1) = loc v L.1
  refine locAct_symm_eq hxM hx0 fun y hy => ?_
  rw [hγ, mem_locAct] at hy
  obtain ⟨d, hd, rfl⟩ := hy
  rw [qbil_mulVec_locGram, gram_dot_symm, dotProduct]
  have hd' := mem_std_iff.mp hd
  refine Valuation.map_sum_le _ fun m _ => ?_
  rw [map_mul]
  calc _ ≤ Valued.v ((locGram Q v γ *ᵥ c) m) * 1 := mul_le_mul' le_rfl (hd' m)
    _ ≤ _ := by rw [mul_one]; exact hb m

theorem gram_mulVec_diag_of (γ : GL (Fin n) Fw) {c : Fin n → Fw} {m : Fin n}
    (horth : ∀ l, l ≠ m → c l ≠ 0 → locGram Q v γ m l = 0) :
    (locGram Q v γ *ᵥ c) m = locGram Q v γ m m * c m := by
  rw [mulVec, dotProduct, Finset.sum_eq_single m]
  · intro l _ hl
    by_cases hcl : c l = 0
    · rw [hcl, mul_zero]
    · rw [horth l hl hcl, zero_mul]
  · simp

theorem locGram_symm' (γ : GL (Fin n) Fw) (l m : Fin n) : locGram Q v γ l m = locGram Q v γ m l := by
  have := congr_fun (congr_fun (locGram_transpose (Q := Q) (v := v) γ) m) l
  simpa using this

theorem valued_two_le_one : Valued.v (2 : Fw) ≤ 1 := by
  have h : ((2 : 𝔬w) : Fw) = 2 := rfl
  have := vle_one (v := v) (2 : 𝔬w)
  rwa [h] at this

/-- **Admissible symmetries from the span of three orthogonal basis vectors.** -/
theorem ternary_adm (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    {w : Fw} (hw : w ≠ 0) {p q r : 𝔬w}
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q) (hgk : locGram Q v γ k k = w * r)
    (s t z : 𝔬w) (hB : IsUnit (Bf p q r s t z)) :
    ∃ x, Q.evalIn Fw x = w / 2 * ((Bf p q r s t z : 𝔬w) : Fw) ∧ symm Q Fw x ∈ locStabV Q v L := by
  set c : Fin n → Fw := Pi.single i (s : Fw) + Pi.single j (t : Fw) + Pi.single k (z : Fw) with hc
  have hci : c i = s := by simp [hc, hij, hik]
  have hcj : c j = t := by simp [hc, hij.symm, hjk]
  have hck : c k = z := by simp [hc, hik.symm, hjk.symm]
  have hcm : ∀ m, m ≠ i → m ≠ j → m ≠ k → c m = 0 := by
    intro m h1 h2 h3; simp [hc, h1, h2, h3]
  have hcstd : c ∈ std v :=
    (std v).add_mem ((std v).add_mem (single_mem_std i (vle_one s)) (single_mem_std j (vle_one t)))
      (single_mem_std k (vle_one z))
  have hdiag : ∀ m, (locGram Q v γ *ᵥ c) m = locGram Q v γ m m * c m := fun m =>
    gram_mulVec_diag_of γ fun l hl hcl => by
      have : l = i ∨ l = j ∨ l = k := by
        by_contra h
        push Not at h
        exact hcl (hcm l h.1 h.2.1 h.2.2)
      rw [locGram_symm']
      exact horth l m hl this
  have hdot : ∀ d : Fin n → Fw, c ⬝ᵥ d = s * d i + t * d j + z * d k := fun d => by
    rw [hc, add_dotProduct, add_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
  have h2ne : (2 : Fw) ≠ 0 := two_ne_zero
  have hQ2 : 2 * Q.evalIn Fw (γ.val *ᵥ c) = w * ((Bf p q r s t z : 𝔬w) : Fw) := by
    rw [two_mul_evalIn_locGram, hdot, hdiag i, hdiag j, hdiag k, hci, hcj, hck, hgi, hgj, hgk]
    simp only [Bf]
    push_cast
    ring
  have hQx : Q.evalIn Fw (γ.val *ᵥ c) = w / 2 * ((Bf p q r s t z : 𝔬w) : Fw) := by
    rw [div_mul_eq_mul_div, eq_div_iff h2ne]
    linear_combination hQ2
  have hBne : ((Bf p q r s t z : 𝔬w) : Fw) ≠ 0 := fun h => hB.ne_zero (by exact_mod_cast h)
  have hvB : Valued.v ((Bf p q r s t z : 𝔬w) : Fw) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hB
  have hx0 : Q.evalIn Fw (γ.val *ᵥ c) ≠ 0 := by
    rw [hQx]; exact mul_ne_zero (div_ne_zero hw h2ne) hBne
  refine ⟨γ.val *ᵥ c, hQx, symm_mem_of_gram L γ hγ hcstd hx0 fun m => ?_⟩
  have hle : Valued.v w ≤ Valued.v (Q.evalIn Fw (γ.val *ᵥ c)) := by
    rw [hQx, map_mul, hvB, mul_one, map_div₀,
      le_div_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h2ne))]
    exact mul_le_of_le_one_right' valued_two_le_one
  refine le_trans ?_ hle
  have hbd : ∀ (g : Fw) (x y : 𝔬w), g = w * x → Valued.v (g * y) ≤ Valued.v w := by
    intro g x y hg
    rw [hg, mul_assoc, map_mul, map_mul]
    calc Valued.v w * (Valued.v (x : Fw) * Valued.v (y : Fw)) ≤ Valued.v w * (1 * 1) :=
          mul_le_mul' le_rfl (mul_le_mul' (vle_one x) (vle_one y))
      _ = Valued.v w := by simp
  rw [hdiag m]
  by_cases hmi : m = i
  · subst hmi; rw [hci]; exact hbd _ p s hgi
  by_cases hmj : m = j
  · subst hmj; rw [hcj]; exact hbd _ q t hgj
  by_cases hmk : m = k
  · subst hmk; rw [hck]; exact hbd _ r z hgk
  rw [hcm m hmi hmj hmk, mul_zero, map_zero]
  exact zero_le

/-- **Two unit values of the ternary form** $B(s,t,z) = ps^2 + qt^2 + rz^2$ have product in $\theta(O^+(L_v))$
(up to the square $(w/2)^2$). -/
theorem ternary_InT (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    {w : Fw} (hw : w ≠ 0) {p q r : 𝔬w}
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q) (hgk : locGram Q v γ k k = w * r)
    (s t z s' t' z' : 𝔬w) (hB : IsUnit (Bf p q r s t z)) (hB' : IsUnit (Bf p q r s' t' z')) :
    InT hQ L (((Bf p q r s t z * Bf p q r s' t' z' : 𝔬w)) : Fw) := by
  obtain ⟨x, hx, hxs⟩ := ternary_adm L γ hγ hij hik hjk horth hw hgi hgj hgk s t z hB
  obtain ⟨y, hy, hys⟩ := ternary_adm L γ hγ hij hik hjk horth hw hgi hgj hgk s' t' z' hB'
  have h2ne : (2 : Fw) ≠ 0 := two_ne_zero
  have hBne : ((Bf p q r s t z : 𝔬w) : Fw) ≠ 0 := fun h => hB.ne_zero (by exact_mod_cast h)
  have hBne' : ((Bf p q r s' t' z' : 𝔬w) : Fw) ≠ 0 := fun h => hB'.ne_zero (by exact_mod_cast h)
  have hx0 : Q.evalIn Fw x ≠ 0 := by rw [hx]; exact mul_ne_zero (div_ne_zero hw h2ne) hBne
  have hy0 : Q.evalIn Fw y ≠ 0 := by rw [hy]; exact mul_ne_zero (div_ne_zero hw h2ne) hBne'
  have := InT.of_symm_pair hQ L hx0 hy0 hxs hys
  rw [hx, hy] at this
  have e : w / 2 * ((Bf p q r s t z : 𝔬w) : Fw) * (w / 2 * ((Bf p q r s' t' z' : 𝔬w) : Fw)) =
      ((Bf p q r s t z * Bf p q r s' t' z' : 𝔬w) : Fw) * (w / 2) ^ 2 := by push_cast; ring
  rw [e] at this
  exact (InT.sq_mul_iff hQ L (div_ne_zero hw h2ne)).mp this

/-- **Admissible symmetries from the span of two basis vectors $b_i, b_j$ with $G_{ij} \ne 0$.** -/
theorem binary_adm (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v)) {i j : Fin n} (hij : i ≠ j)
    (horth : ∀ m, m ≠ i → m ≠ j → locGram Q v γ m i = 0 ∧ locGram Q v γ m j = 0)
    (hij0 : locGram Q v γ i j ≠ 0) {a c : 𝔬w}
    (hai : locGram Q v γ i i = 2 * locGram Q v γ i j * a)
    (hcj : locGram Q v γ j j = 2 * locGram Q v γ i j * c)
    (s t : 𝔬w) (hf : IsUnit (a * s ^ 2 + s * t + c * t ^ 2)) :
    ∃ x, Q.evalIn Fw x = locGram Q v γ i j * ((a * s ^ 2 + s * t + c * t ^ 2 : 𝔬w) : Fw) ∧
      symm Q Fw x ∈ locStabV Q v L := by
  set ε := locGram Q v γ i j with hε
  set c0 : Fin n → Fw := Pi.single i (s : Fw) + Pi.single j (t : Fw) with hc0
  have hGc : ∀ m, (locGram Q v γ *ᵥ c0) m = locGram Q v γ m i * s + locGram Q v γ m j * t := by
    intro m
    simp [hc0, Matrix.mulVec_add, Matrix.mulVec_single]
    ring
  have hdot : ∀ d : Fin n → Fw, c0 ⬝ᵥ d = s * d i + t * d j := fun d => by
    rw [hc0, add_dotProduct, single_dotProduct, single_dotProduct]
  have hji : locGram Q v γ j i = ε := locGram_symm' γ j i
  have h2ne : (2 : Fw) ≠ 0 := two_ne_zero
  have hcstd : c0 ∈ std v := (std v).add_mem (single_mem_std i (vle_one s)) (single_mem_std j (vle_one t))
  have hQ2 : 2 * Q.evalIn Fw (γ.val *ᵥ c0) = 2 * (ε * ((a * s ^ 2 + s * t + c * t ^ 2 : 𝔬w) : Fw)) := by
    rw [two_mul_evalIn_locGram, hdot, hGc i, hGc j, hji, hai, hcj]
    push_cast
    ring
  have hQx : Q.evalIn Fw (γ.val *ᵥ c0) = ε * ((a * s ^ 2 + s * t + c * t ^ 2 : 𝔬w) : Fw) :=
    mul_left_cancel₀ h2ne hQ2
  have hfne : ((a * s ^ 2 + s * t + c * t ^ 2 : 𝔬w) : Fw) ≠ 0 := fun h => hf.ne_zero (by exact_mod_cast h)
  have hvf : Valued.v ((a * s ^ 2 + s * t + c * t ^ 2 : 𝔬w) : Fw) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hf
  have hx0 : Q.evalIn Fw (γ.val *ᵥ c0) ≠ 0 := by rw [hQx]; exact mul_ne_zero hij0 hfne
  refine ⟨γ.val *ᵥ c0, hQx, symm_mem_of_gram L γ hγ hcstd hx0 fun m => ?_⟩
  rw [hQx, map_mul, hvf, mul_one, hGc m]
  have hb1 : ∀ y : 𝔬w, Valued.v (ε * (y : Fw)) ≤ Valued.v ε := fun y => by
    rw [map_mul]
    calc Valued.v ε * Valued.v (y : Fw) ≤ Valued.v ε * 1 := mul_le_mul' le_rfl (vle_one y)
      _ = _ := mul_one _
  have hb2 : ∀ x y : 𝔬w, Valued.v (2 * ε * (x : Fw) * (y : Fw)) ≤ Valued.v ε := fun x y => by
    rw [map_mul, map_mul, map_mul]
    calc Valued.v (2 : Fw) * Valued.v ε * Valued.v (x : Fw) * Valued.v (y : Fw) ≤ 1 * Valued.v ε * 1 * 1 :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' valued_two_le_one le_rfl) (vle_one x)) (vle_one y)
      _ = _ := by simp
  by_cases hmi : m = i
  · subst hmi
    rw [hai]
    exact Valuation.map_add_le _ (by rw [mul_assoc, mul_assoc]; rw [← mul_assoc, ← mul_assoc]; exact hb2 a s)
      (hb1 t)
  by_cases hmj : m = j
  · subst hmj
    rw [hji, hcj]
    exact Valuation.map_add_le _ (hb1 s) (hb2 c t)
  rw [(horth m hmi hmj).1, (horth m hmi hmj).2]
  simp

/-- **Two unit values of the binary form** $f(s,t) = as^2 + st + ct^2$ have product in $\theta(O^+(L_v))$. -/
theorem binary_InT (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v)) {i j : Fin n} (hij : i ≠ j)
    (horth : ∀ m, m ≠ i → m ≠ j → locGram Q v γ m i = 0 ∧ locGram Q v γ m j = 0)
    (hij0 : locGram Q v γ i j ≠ 0) {a c : 𝔬w}
    (hai : locGram Q v γ i i = 2 * locGram Q v γ i j * a)
    (hcj : locGram Q v γ j j = 2 * locGram Q v γ i j * c)
    (s t s' t' : 𝔬w) (hf : IsUnit (a * s ^ 2 + s * t + c * t ^ 2))
    (hf' : IsUnit (a * s' ^ 2 + s' * t' + c * t' ^ 2)) :
    InT hQ L (((a * s ^ 2 + s * t + c * t ^ 2) * (a * s' ^ 2 + s' * t' + c * t' ^ 2) : 𝔬w) : Fw) := by
  obtain ⟨x, hx, hxs⟩ := binary_adm L γ hγ hij horth hij0 hai hcj s t hf
  obtain ⟨y, hy, hys⟩ := binary_adm L γ hγ hij horth hij0 hai hcj s' t' hf'
  have hfne : ((a * s ^ 2 + s * t + c * t ^ 2 : 𝔬w) : Fw) ≠ 0 := fun h => hf.ne_zero (by exact_mod_cast h)
  have hfne' : ((a * s' ^ 2 + s' * t' + c * t' ^ 2 : 𝔬w) : Fw) ≠ 0 :=
    fun h => hf'.ne_zero (by exact_mod_cast h)
  have hx0 : Q.evalIn Fw x ≠ 0 := by rw [hx]; exact mul_ne_zero hij0 hfne
  have hy0 : Q.evalIn Fw y ≠ 0 := by rw [hy]; exact mul_ne_zero hij0 hfne'
  have := InT.of_symm_pair hQ L hx0 hy0 hxs hys
  rw [hx, hy] at this
  have e : locGram Q v γ i j * ((a * s ^ 2 + s * t + c * t ^ 2 : 𝔬w) : Fw) *
      (locGram Q v γ i j * ((a * s' ^ 2 + s' * t' + c * t' ^ 2 : 𝔬w) : Fw)) =
      (((a * s ^ 2 + s * t + c * t ^ 2) * (a * s' ^ 2 + s' * t' + c * t' ^ 2) : 𝔬w) : Fw) *
        (locGram Q v γ i j) ^ 2 := by push_cast; ring
  rw [e] at this
  exact (InT.sq_mul_iff hQ L hij0).mp this

end Spin

/-! ### The three cases -/

section Final

variable {n : ℕ} {Q : QuadForm ℚ n} (hQ : Q.Nondegenerate) (L : Lat ℚ n)

/-- Two elements of $\theta$ in $\mathbb Z_2^\times$, $\alpha \equiv 5$ and $\beta \equiv 3 \pmod 4$, give all units. -/
theorem units_of_pair (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {α β : 𝔬} (hMα : InT hQ L (α : Fv)) (hα : Rl α 5)
    (hMβ : InT hQ L (β : Fv)) (hβ : Rl β 3 ∨ Rl β 7) (u : Fvˣ) (hu : Valued.v (u : Fv) = 1) :
    u ∈ localSpinorNormGroup Q hQ v L := by
  have key := unit_cover h2 (fun x : 𝔬 => InT hQ L (x : Fv))
    (fun x y _ _ hx hy => InT.mul hQ L hx hy)
    (fun x s _ hs => by
      have hs0 : (s : Fv) ≠ 0 := fun h => hs.ne_zero (by exact_mod_cast h)
      exact InT.sq_mul_iff hQ L hs0)
    (InT.one hQ L) hMα hα hMβ hβ
  have u0 : IsUnit (toO v (u : Fv) hu.le) :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hu
  exact InT.mem hQ L (key _ u0)

theorem coe_two_eq : ((2 : 𝔬) : Fv) = 2 := rfl

theorem coe_four_eq : ((4 : 𝔬) : Fv) = 4 := by
  have : (4 : 𝔬) = 2 * 2 := by norm_num
  rw [this]; push_cast; rw [coe_two_eq]; norm_num

/-- Equal absolute values: $a = bu$ with $u$ a unit of $\mathfrak o$. -/
theorem exists_unit_ratio {a b : Fv} (hb : b ≠ 0) (h : Valued.v a = Valued.v b) :
    ∃ u : 𝔬, IsUnit u ∧ a = b * (u : Fv) := by
  have hv : Valued.v (a / b) = 1 := by
    rw [map_div₀, h, div_self ((Valuation.ne_zero_iff _).mpr hb)]
  refine ⟨toO v (a / b) hv.le, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hv, ?_⟩
  show a = b * (a / b)
  field_simp

/-- **The ternary patterns give all units.** -/
theorem ternary_units (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    {w : Fv} (hw : w ≠ 0) {p q r : 𝔬} (hpat : Pat p q r)
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q) (hgk : locGram Q v γ k k = w * r)
    (u : Fvˣ) (hu : Valued.v (u : Fv) = 1) : u ∈ localSpinorNormGroup Q hQ v L := by
  obtain ⟨⟨s, t, z, s', t', z', h1, h1', h5⟩, ⟨s2, t2, z2, s3, t3, z3, h2', h2'', h37⟩⟩ :=
    pattern_cover h2 hpat
  exact units_of_pair hQ L h2
    (ternary_InT hQ L γ hγ hij hik hjk horth hw hgi hgj hgk s t z s' t' z' h1 h1') h5
    (ternary_InT hQ L γ hγ hij hik hjk horth hw hgi hgj hgk s2 t2 z2 s3 t3 z3 h2' h2'') h37 u hu

end Final

/-- **Cassels, Lemma 3.8 (i)** (Ch. 11, p. 214): *$\Lambda^{(2)}$ is $2$-dimensional with basis $b_1, b_2$ and
$\phi(x_1b_1 + x_2b_2) = 2^ex_1x_2$ or $2^e(x_1^2 + x_1x_2 + x_2^2)$; then $U_2 \subseteq \theta(\Lambda^{(2)})$.*
Here for an orthogonal summand spanned by $b_i, b_j$ of a basis of $L_2$ on which $\phi = 2^e(ax_i^2 + x_ix_j +
cx_j^2)$ with $a, c \in \mathbb Z_2$ (reconstructed, see the module docstring): every unit of $\mathbb Z_2$ is the
spinor norm of a rotation of $L_2$. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.8 (i), p. 214 (reconstructed; generalization: a, c ∈ ℤ₂)"]
theorem units_mem_localSpinorNormGroup_two_binary (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (L : Lat ℚ n) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j : Fin n} (hij : i ≠ j)
    (horth : ∀ m, m ≠ i → m ≠ j → locGram Q v γ m i = 0 ∧ locGram Q v γ m j = 0)
    (hij0 : locGram Q v γ i j ≠ 0)
    (hi : Valued.v (locGram Q v γ i i) ≤ Valued.v (2 * locGram Q v γ i j))
    (hj : Valued.v (locGram Q v γ j j) ≤ Valued.v (2 * locGram Q v γ i j))
    (u : Fvˣ) (hu : Valued.v (u : Fv) = 1) : u ∈ localSpinorNormGroup Q hQ v L := by
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have h2ε : (2 : Fv) * locGram Q v γ i j ≠ 0 := mul_ne_zero h2ne hij0
  have hpos : 0 < Valued.v ((2 : Fv) * locGram Q v γ i j) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h2ε)
  have hai1 : Valued.v (locGram Q v γ i i / (2 * locGram Q v γ i j)) ≤ 1 := by
    rw [map_div₀, div_le_one₀ hpos]; exact hi
  have hcj1 : Valued.v (locGram Q v γ j j / (2 * locGram Q v γ i j)) ≤ 1 := by
    rw [map_div₀, div_le_one₀ hpos]; exact hj
  have hai : locGram Q v γ i i = 2 * locGram Q v γ i j * ((toO v _ hai1 : 𝔬) : Fv) := by
    show locGram Q v γ i i = 2 * locGram Q v γ i j * (locGram Q v γ i i / (2 * locGram Q v γ i j))
    field_simp
  have hcj : locGram Q v γ j j = 2 * locGram Q v γ i j * ((toO v _ hcj1 : 𝔬) : Fv) := by
    show locGram Q v γ j j = 2 * locGram Q v γ i j * (locGram Q v γ j j / (2 * locGram Q v γ i j))
    field_simp
  have u0 : IsUnit (toO v (u : Fv) hu.le) :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hu
  obtain ⟨s, t, hst⟩ := exists_binary_value h2 (toO v _ hai1) (toO v _ hcj1) _ u0
  obtain ⟨s', t', hst'⟩ := exists_binary_value h2 (toO v _ hai1) (toO v _ hcj1) 1 isUnit_one
  have := binary_InT hQ L γ hγ hij horth hij0 hai hcj s t s' t' (by rw [hst]; exact u0)
    (by rw [hst']; exact isUnit_one)
  rw [hst, hst', mul_one] at this
  exact InT.mem hQ L this

/-- **Cassels, Lemma 3.8 (ii)** (Ch. 11, p. 214): *$\Lambda^{(2)}$ is $3$-dimensional with basis $b_1, b_2, b_3$,
$\phi(x_1b_1 + x_2b_2 + x_3b_3) = a_1x_1^2 + a_2x_2^2 + a_3x_3^2$ and $\lvert a_1\rvert_2 = \lvert a_2\rvert_2$, with
$\lvert a_3\rvert_2 = \lvert a_1\rvert_2$, $\lvert a_3\rvert_2 = \tfrac12\lvert a_1\rvert_2$ or
$\lvert a_3\rvert_2 = 2\lvert a_1\rvert_2$ (reconstructed); then $U_2 \subseteq \theta(\Lambda^{(2)})$*, for such an
orthogonal summand $b_i, b_j, b_k$ of a basis of $L_2$ ($a_\bullet = \phi(b_\bullet) = \tfrac12G_{\bullet\bullet}$). -/
@[kb "cassels1978" "Ch. 11, Lemma 3.8 (ii), p. 214 (reconstructed)"]
theorem units_mem_localSpinorNormGroup_two_ternary (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (L : Lat ℚ n) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    (hji : Valued.v (locGram Q v γ j j) = Valued.v (locGram Q v γ i i))
    (hk : Valued.v (locGram Q v γ k k) = Valued.v (locGram Q v γ i i) ∨
      Valued.v (locGram Q v γ k k) = Valued.v (2 * locGram Q v γ i i) ∨
      Valued.v (locGram Q v γ i i) = Valued.v (2 * locGram Q v γ k k))
    (u : Fvˣ) (hu : Valued.v (u : Fv) = 1) : u ∈ localSpinorNormGroup Q hQ v L := by
  have hrow : ∀ l, (l = i ∨ l = j ∨ l = k) → locGram Q v γ l l ≠ 0 := fun l hl h0 => by
    refine locGram_det_ne_zero hQ γ (Matrix.det_eq_zero_of_row_eq_zero l fun m => ?_)
    by_cases hm : m = l
    · subst hm; exact h0
    · exact horth l m (Ne.symm hm) hl
  have hgi0 := hrow i (Or.inl rfl)
  have hgk0 := hrow k (Or.inr (Or.inr rfl))
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  obtain ⟨uj, huj, hj⟩ := exists_unit_ratio hgi0 hji
  rcases hk with hk | hk | hk
  · obtain ⟨uk, huk, hk'⟩ := exists_unit_ratio hgi0 hk
    exact ternary_units hQ L h2 γ hγ hij hik hjk horth hgi0 (p := 1) (q := uj) (r := uk)
      (Or.inl ⟨isUnit_one, huj, huk⟩) (by simp) hj hk' u hu
  · obtain ⟨uk, huk, hk'⟩ := exists_unit_ratio (mul_ne_zero h2ne hgi0) hk
    exact ternary_units hQ L h2 γ hγ hij hik hjk horth hgi0 (p := 1) (q := uj) (r := 2 * uk)
      (Or.inr (Or.inl ⟨isUnit_one, huj, uk, huk, rfl⟩)) (by simp) hj
      (by rw [hk']; push_cast; rw [coe_two_eq]; ring) u hu
  · obtain ⟨ui, hui, hi'⟩ := exists_unit_ratio (mul_ne_zero h2ne hgk0) hk
    obtain ⟨uj', huj', hj'⟩ := exists_unit_ratio (mul_ne_zero h2ne hgk0) (hji.trans hk)
    exact ternary_units hQ L h2 γ hγ (Ne.symm hik) (Ne.symm hjk) hij
      (fun l m hlm hl => horth l m hlm (by tauto)) hgk0 (p := 1) (q := 2 * ui) (r := 2 * uj')
      (Or.inr (Or.inr (Or.inl ⟨isUnit_one, ui, uj', hui, huj', rfl, rfl⟩))) (by simp)
      (by rw [hi']; push_cast; rw [coe_two_eq]; ring) (by rw [hj']; push_cast; rw [coe_two_eq]; ring) u hu

/-- **Cassels, Lemma 3.8 (iii)** (Ch. 11, p. 214): *as in (ii) but with $\lvert a_2\rvert_2 = \tfrac12\lvert
a_1\rvert_2$ and $\lvert a_3\rvert_2 = \tfrac14\lvert a_1\rvert_2$* (reconstructed: the valuations of $a_1, a_2, a_3$ are
$e, e+1, e+2$); *then $U_2 \subseteq \theta(\Lambda^{(2)})$.* -/
@[kb "cassels1978" "Ch. 11, Lemma 3.8 (iii), p. 214 (reconstructed)"]
theorem units_mem_localSpinorNormGroup_two_ternary' (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (L : Lat ℚ n) (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    (hj : Valued.v (locGram Q v γ j j) = Valued.v (2 * locGram Q v γ i i))
    (hk : Valued.v (locGram Q v γ k k) = Valued.v (4 * locGram Q v γ i i))
    (u : Fvˣ) (hu : Valued.v (u : Fv) = 1) : u ∈ localSpinorNormGroup Q hQ v L := by
  have hgi0 : locGram Q v γ i i ≠ 0 := fun h0 => by
    refine locGram_det_ne_zero hQ γ (Matrix.det_eq_zero_of_row_eq_zero i fun m => ?_)
    by_cases hm : m = i
    · subst hm; exact h0
    · exact horth i m (Ne.symm hm) (Or.inl rfl)
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have h4ne : (4 : Fv) ≠ 0 := by norm_num
  obtain ⟨uj, huj, hj'⟩ := exists_unit_ratio (mul_ne_zero h2ne hgi0) hj
  obtain ⟨uk, huk, hk'⟩ := exists_unit_ratio (mul_ne_zero h4ne hgi0) hk
  exact ternary_units hQ L h2 γ hγ hij hik hjk horth hgi0 (p := 1) (q := 2 * uj) (r := 4 * uk)
    (Or.inr (Or.inr (Or.inr ⟨isUnit_one, uj, uk, huj, huk, rfl, rfl⟩))) (by simp)
    (by rw [hj']; push_cast; rw [coe_two_eq]; ring) (by rw [hk']; push_cast; rw [coe_four_eq]; ring) u hu

end QuadFormsKB.Lattices
