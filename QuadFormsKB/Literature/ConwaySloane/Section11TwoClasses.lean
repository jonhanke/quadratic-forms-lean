/-
# Conway–Sloane, Ch. 15, §11: a genus of two classes

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §11, pp. 404–405
(`conwaysloane1999`): the indefinite ternary form
$$f = \mathrm{diag}(-1, 64, 2), \qquad f(x) = -x_0^2 + 64x_1^2 + 2x_2^2$$
(Gram matrix; the book's genus $\mathrm I_{2,1}(2\times 64)$, determinant $-128$). The book observes that the genus of
$f$ contains two spinor genera and hence two classes, and (51) gives a representative of the second class.

**Layer.** $f$ = `csQ A11` over $\mathbb Q$, the lattice $\mathbb Z^3$ (`stdLat`), Conway–Sloane's set $\Pi$ =
`primeSet (2 det H)` $= \{2\}$ (`P11`, since $2\det H = -2^{11}$), the prime $2$ as `q11`, Cassels' group
$G = R/ST$ (`CasselsG`) acting on the proper spinor genera (Cassels Ch. 11, Thm. 3.1). The square-class subgroup
$H = \langle -1, 2\rangle\mathbb Q_2^{\times2}/\mathbb Q_2^{\times2} = \{1, -1, 2, -2\}$ is `H11`.

**Proves**
* `rootNorm_A11` (unconditional): every $2$-adic root vector $x$ of $\mathbb Z_2^3$ has $f(x) \in H$. Proof: scale $x$
  so that $\max_i\lvert x_i\rvert_2 = 1$ with some coordinate equal to $1$; the root conditions give
  $f(x) \mid 2x_0$ and $f(x) \mid 4x_2$ in $\mathbb Z_2$ (`rootVector_ineq_gen`); then a case analysis on which
  coordinates are units, with $u^2 \equiv 1 \pmod 8$ for units (`rootCore`). Only the case $x_0 \equiv x_2 \equiv 0 \pmod 4$,
  $x_1 = 1$ needs the root conditions, and there they force $f(x) = 64(1 + 8m)$.
* `five_not_mem_H11` (unconditional): $5 \notin H$ ($5, -5, 10, -10$ are not squares in $\mathbb Q_2$);
* `theta2_le_A11_gen` (unconditional): every $2$-adically automorphous number of $f$ lies in $H$ (see the section
  "The $2$-adic bound, unconditional"; formerly derived from the named statement `Theorem18Dyadic`);
* `example11_two_spinorGenera` (**unconditional**): the genus of
  $\mathbb Z^3$ contains a lattice $M$ not in the proper spinor genus of $\mathbb Z^3$ ($\Delta_2(5)$ is not in the
  spinor kernel: the $2$-adically automorphous numbers lie in $H$, which contains $2$ and Cassels' $j = -1$);
* `example11_two_classes` (**unconditional**): moreover no isometry of $(\mathbb Q^3, f)$ maps
  $\mathbb Z^3$ onto $M$ ($\mathbb Z^3$ has the improper automorph $\mathrm{diag}(-1, 1, 1)$);
* `example11_at_most_two_spinorGenera` (unconditional): the genus has at most two proper spinor genera ($G$ has at
  most two elements: $R = XT$, $X$ = the units of $\mathbb Q_2$, whose square classes are $\pm1, \pm5$, and
  $\Delta_2(-1) = j$ is in the spinor kernel by Theorem 17);
* `example11_exactly_two_classes` (**unconditional**): every
  lattice of the genus is properly isometric to $\mathbb Z^3$ or to $M$ (Eichler's theorem, Cassels Ch. 11, Thm. 1.4,
  for the indefinite ternary $f$), and $M$ is not isometric to $\mathbb Z^3$: the genus has exactly two classes.

The representative (51b) of the second class is not formalized here; $M$ is obtained abstractly from the action of
$G$ on the spinor genera.

*The $2$-adic bound.* Conway–Sloane get "$5$ is not $2$-adically automorphous" from Theorem 18 at $p = 2$ (root
vectors, `rootNorm_A11`). Here it is proved directly (`theta2_le_A11_gen`): an automorph moves $e_1$ (the Jordan
constituent of scale $64$) only by a multiple of $16$, a symmetry of norm in $H$ moves it back, and the rest is an
isometry of the binary space $\langle -1, 2\rangle$, whose spinor norms are norms from $\mathbb Q_2(\sqrt2)$ (Wall's
formula). The named statement `Theorem18Dyadic` is no longer needed.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Example96
import QuadFormsKB.Literature.Cassels.Ch11Sec3Dyadic
import QuadFormsKB.Literature.Cassels.Ch9Sec8Int

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

namespace Ex11

section Core

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem isUnit_or_two_dvd (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (x : 𝔬) : IsUnit x ∨ ∃ y : 𝔬, x = 2 * y := by
  obtain ⟨a, ha⟩ := Rl.exists h2 x
  by_cases hod : Od a
  · exact Or.inl (ha.od_unit h2 hod)
  · obtain ⟨k, hk⟩ := not_od_even a hod
    exact Or.inr (ha.even k hk)

theorem od_sq_eq_one : ∀ a : ZMod 8, Od a → a ^ 2 = 1 := by decide

theorem exists_sq_eq_of_isUnit (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : 𝔬} (hx : IsUnit x) :
    ∃ m : 𝔬, x ^ 2 = 1 + 8 * m := by
  obtain ⟨a, ha⟩ := Rl.exists h2 x
  have h := ha.pow_two
  rw [od_sq_eq_one a (ha.unit_od h2 hx)] at h
  obtain ⟨m, hm⟩ := Rl.of_cast (n := 1) (by simpa using h)
  exact ⟨m, by simpa using hm⟩

theorem not_isUnit_two_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (y : 𝔬) : ¬ IsUnit (2 * y) :=
  (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right y _ (two_mem_max h2))

theorem one_ne_two_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (y : 𝔬) : (1 : 𝔬) ≠ 2 * y :=
  fun h => not_isUnit_two_mul h2 y (h ▸ isUnit_one)

theorem natCast_ne_zero_O (k : ℕ) (hk : k ≠ 0) : (k : 𝔬) ≠ 0 := by
  intro h
  have := congrArg (fun z : 𝔬 => (z : Fv)) h
  simp at this
  exact hk this

/-- The square classes $\{1, -1, 2, -2\}$, as a predicate on $\mathbb Z_2$: $q = d s^2 (1 + 8m)$. -/
def GoodVal (q : 𝔬) : Prop :=
  ∃ d : ℤ, (d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2) ∧ ∃ s m : 𝔬, q = d * (s ^ 2 * (1 + 8 * m))

theorem rootCore (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (a b c : 𝔬) (h1 : a = 1 ∨ b = 1 ∨ c = 1)
    (hda : -a ^ 2 + 64 * b ^ 2 + 2 * c ^ 2 ∣ 2 * a) (hdc : -a ^ 2 + 64 * b ^ 2 + 2 * c ^ 2 ∣ 4 * c) :
    GoodVal (-a ^ 2 + 64 * b ^ 2 + 2 * c ^ 2) := by
  rcases isUnit_or_two_dvd h2 a with ha | ⟨a1, rfl⟩
  · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 ha
    rcases isUnit_or_two_dvd h2 c with hc | ⟨c1, rfl⟩
    · obtain ⟨m', hm'⟩ := exists_sq_eq_of_isUnit h2 hc
      exact ⟨1, Or.inl rfl, 1, -m + 8 * b ^ 2 + 2 * m', by rw [hm, hm']; push_cast; ring⟩
    · exact ⟨-1, Or.inr (Or.inl rfl), 1, m - 8 * b ^ 2 - c1 ^ 2, by rw [hm]; push_cast; ring⟩
  rcases isUnit_or_two_dvd h2 c with hc | ⟨c1, rfl⟩
  · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hc
    rcases isUnit_or_two_dvd h2 a1 with ha1 | ⟨a2, rfl⟩
    · obtain ⟨k, hk⟩ := exists_sq_eq_of_isUnit h2 ha1
      exact ⟨-2, Or.inr (Or.inr (Or.inr rfl)), 1, -m - 4 * b ^ 2 + 2 * k, by
        rw [mul_pow, hk, hm]; push_cast; ring⟩
    · exact ⟨2, Or.inr (Or.inr (Or.inl rfl)), 1, m + 4 * b ^ 2 - a2 ^ 2, by rw [hm]; push_cast; ring⟩
  -- `a`, `c` even: then `b = 1`
  have hb : b = 1 := by
    rcases h1 with h | h | h
    · exact absurd h.symm (one_ne_two_mul h2 a1)
    · exact h
    · exact absurd h.symm (one_ne_two_mul h2 c1)
  subst hb
  rcases isUnit_or_two_dvd h2 a1 with ha1 | ⟨a2, rfl⟩
  · obtain ⟨k, hk⟩ := exists_sq_eq_of_isUnit h2 ha1
    rcases isUnit_or_two_dvd h2 c1 with hc1 | ⟨c2, rfl⟩
    · obtain ⟨l, hl⟩ := exists_sq_eq_of_isUnit h2 hc1
      exact ⟨1, Or.inl rfl, 2, -k + 2 + 2 * l, by rw [mul_pow, mul_pow, hk, hl]; push_cast; ring⟩
    · exact ⟨-1, Or.inr (Or.inl rfl), 2, k - 2 - c2 ^ 2, by rw [mul_pow, hk]; push_cast; ring⟩
  rcases isUnit_or_two_dvd h2 c1 with hc1 | ⟨c2, rfl⟩
  · obtain ⟨l, hl⟩ := exists_sq_eq_of_isUnit h2 hc1
    rcases isUnit_or_two_dvd h2 a2 with ha2 | ⟨a3, rfl⟩
    · obtain ⟨k, hk⟩ := exists_sq_eq_of_isUnit h2 ha2
      exact ⟨-2, Or.inr (Or.inr (Or.inr rfl)), 2, -l + 2 * k - 1, by
        push_cast; linear_combination (-16) * hk + 8 * hl⟩
    · exact ⟨2, Or.inr (Or.inr (Or.inl rfl)), 2, l - a3 ^ 2 + 1, by push_cast; linear_combination 8 * hl⟩
  -- the deep case: only the root conditions help
  obtain ⟨S, hS⟩ : ∃ S : 𝔬, S = -a2 ^ 2 + 4 + 2 * c2 ^ 2 := ⟨_, rfl⟩
  have hQ : -(2 * (2 * a2)) ^ 2 + 64 * (1 : 𝔬) ^ 2 + 2 * (2 * (2 * c2)) ^ 2 = 16 * S := by
    rw [hS]; ring
  rw [hQ] at hda hdc ⊢
  obtain ⟨k, hk⟩ := hda
  obtain ⟨l, hl⟩ := hdc
  have ha2 : a2 = 2 * S * k := by
    have h8 : (8 : 𝔬) * (a2 - 2 * S * k) = 0 := by linear_combination hk
    rcases mul_eq_zero.mp h8 with h | h
    · exact absurd h (by exact_mod_cast natCast_ne_zero_O (v := v) 8 (by norm_num))
    · exact sub_eq_zero.mp h
  have hc2 : c2 = S * l := by
    have h16 : (16 : 𝔬) * (c2 - S * l) = 0 := by linear_combination hl
    rcases mul_eq_zero.mp h16 with h | h
    · exact absurd h (by exact_mod_cast natCast_ne_zero_O (v := v) 16 (by norm_num))
    · exact sub_eq_zero.mp h
  rw [ha2, hc2] at hS
  obtain ⟨T, hT⟩ : ∃ T : 𝔬, T = -2 * S ^ 2 * k ^ 2 + 2 + S ^ 2 * l ^ 2 := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : 𝔬, U = -4 * T ^ 2 * k ^ 2 + 1 + 2 * T ^ 2 * l ^ 2 := ⟨_, rfl⟩
  have e1 : S = 2 * T := by linear_combination hS - 2 * hT
  have e2 : T = 2 * U := by linear_combination hT - 2 * hU + (S + 2 * T) * (l ^ 2 - 2 * k ^ 2) * e1
  refine ⟨1, Or.inl rfl, 8, U ^ 2 * (l ^ 2 - 2 * k ^ 2), ?_⟩
  push_cast
  linear_combination 16 * e1 + 32 * e2 + 64 * hU + 128 * (T + 2 * U) * (l ^ 2 - 2 * k ^ 2) * e2

theorem coe_O_ne_zero {q : 𝔬} (hq : q ≠ 0) : (q : Fv) ≠ 0 := fun h => hq (Subtype.ext h)

theorem dvd_of_valued_div_le {p q : 𝔬} (hq : q ≠ 0) (h : Valued.v ((p : Fv) / q) ≤ 1) : q ∣ p := by
  refine ⟨toO v _ h, Subtype.ext ?_⟩
  show (p : Fv) = (q : Fv) * ((p : Fv) / q)
  field_simp [coe_O_ne_zero hq]

theorem not_isSquare_of_O (z : 𝔬) (hz : ∀ r : 𝔬, z ≠ r * r) : ¬ IsSquare (z : Fv) := by
  rintro ⟨r, hr⟩
  have hle : Valued.v r ≤ 1 := by
    have h1 : Valued.v r ^ 2 ≤ 1 := by
      rw [← map_pow, sq, ← hr]; exact vle_one z
    exact (pow_le_one_iff two_ne_zero).mp h1
  exact hz (toO v r hle) (Subtype.ext hr)

theorem four_ne_zero_O : (4 : 𝔬) ≠ 0 := by exact_mod_cast natCast_ne_zero_O (v := v) 4 (by norm_num)

theorem two_ne_zero_O : (2 : 𝔬) ≠ 0 := by exact_mod_cast natCast_ne_zero_O (v := v) 2 (by norm_num)

theorem not_sq_five (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : ∀ r : 𝔬, (5 : 𝔬) ≠ r * r := by
  intro r hr
  rcases isUnit_or_two_dvd h2 r with hu | ⟨y, rfl⟩
  · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hu
    exact one_ne_two_mul h2 m (mul_left_cancel₀ four_ne_zero_O (by linear_combination hr + hm))
  · exact one_ne_two_mul h2 (2 * y ^ 2 - 2) (by linear_combination hr)

theorem not_sq_neg_five (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : ∀ r : 𝔬, (-5 : 𝔬) ≠ r * r := by
  intro r hr
  rcases isUnit_or_two_dvd h2 r with hu | ⟨y, rfl⟩
  · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hu
    have h3 : (3 : 𝔬) = -4 * m := mul_left_cancel₀ two_ne_zero_O (by linear_combination -hr - hm)
    exact one_ne_two_mul h2 (-2 * m - 1) (by linear_combination h3)
  · exact one_ne_two_mul h2 (-2 * y ^ 2 - 2) (by linear_combination -hr)

theorem not_sq_ten (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : ∀ r : 𝔬, (10 : 𝔬) ≠ r * r := by
  intro r hr
  rcases isUnit_or_two_dvd h2 r with hu | ⟨y, rfl⟩
  · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hu
    exact one_ne_two_mul h2 (5 - 4 * m) (by linear_combination -hr - hm)
  · have h5 : (5 : 𝔬) = 2 * y ^ 2 := mul_left_cancel₀ two_ne_zero_O (by linear_combination hr)
    exact one_ne_two_mul h2 (y ^ 2 - 2) (by linear_combination h5)

theorem not_sq_neg_ten (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : ∀ r : 𝔬, (-10 : 𝔬) ≠ r * r := by
  intro r hr
  rcases isUnit_or_two_dvd h2 r with hu | ⟨y, rfl⟩
  · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hu
    exact one_ne_two_mul h2 (-5 - 4 * m) (by linear_combination -hr - hm)
  · have h5 : (-5 : 𝔬) = 2 * y ^ 2 := mul_left_cancel₀ two_ne_zero_O (by linear_combination hr)
    exact one_ne_two_mul h2 (-y ^ 2 - 2) (by linear_combination -h5)

theorem zpow_eq_one_or_self {G : Type*} [Group G] {g : G} (hg : g ^ (2 : ℤ) = 1) (m : ℤ) :
    g ^ m = 1 ∨ g ^ m = g := by
  have hk : m = 2 * (m / 2) + m % 2 := by omega
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left; rw [hk, h, add_zero, _root_.zpow_mul, hg, _root_.one_zpow]
  · right; rw [hk, h, _root_.zpow_add, _root_.zpow_mul, hg, _root_.one_zpow, one_mul, zpow_one]

theorem sqClassOf_sq_eq_one {a : Fv} (ha : a ≠ 0) : sqClassOf a ^ (2 : ℤ) = 1 := by
  rw [zpow_ofNat, sq, ← sqClassOf_mul ha ha, sqClassOf_eq_one_iff (mul_ne_zero ha ha)]
  exact ⟨a, rfl⟩

theorem isSquare_of_sqClassOf_eq {a b : Fv} (ha : a ≠ 0) (hb : b ≠ 0) (h : sqClassOf a = sqClassOf b) :
    IsSquare (a * b) := by
  rw [← sqClassOf_eq_one_iff (mul_ne_zero ha hb), sqClassOf_mul ha hb, h, ← sqClassOf_mul hb hb,
    sqClassOf_eq_one_iff (mul_ne_zero hb hb)]
  exact ⟨b, rfl⟩

end Core

end Ex11

open Ex11

section CoreH

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- The subgroup $H = \langle -1, 2\rangle\mathbb Q_2^{\times 2}/\mathbb Q_2^{\times 2}$ of square classes. -/
def H11 (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (SqClass (v.adicCompletion ℚ)) :=
  Subgroup.closure {sqClassOf (-1 : v.adicCompletion ℚ), sqClassOf (2 : v.adicCompletion ℚ)}

theorem neg_one_mem_H11 : sqClassOf (-1 : Fv) ∈ H11 v := Subgroup.subset_closure (by simp)

theorem two_mem_H11 : sqClassOf (2 : Fv) ∈ H11 v := Subgroup.subset_closure (by simp)

theorem neg_two_mem_H11 : sqClassOf (-2 : Fv) ∈ H11 v := by
  rw [show (-2 : Fv) = -1 * 2 by ring, sqClassOf_mul (by norm_num) (by norm_num)]
  exact (H11 v).mul_mem neg_one_mem_H11 two_mem_H11

theorem mem_H11_of_goodVal (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Qx w : Fv} (hQ0 : Qx ≠ 0) {q : 𝔬}
    (hQ : Qx = w ^ 2 * q) (hg : GoodVal q) : sqClassOf Qx ∈ H11 v := by
  obtain ⟨d, hd, s, m, hq⟩ := hg
  obtain ⟨t, ht⟩ := exists_sq_one_add_eight h2 m
  have hcoe : (q : Fv) = (d : Fv) * ((s : Fv) * (t : Fv)) ^ 2 := by
    rw [hq, ← ht]; push_cast; ring
  rw [hcoe] at hQ
  have hQ' : Qx = (w * ((s : Fv) * (t : Fv))) ^ 2 * (d : Fv) := by rw [hQ]; ring
  have hr : w * ((s : Fv) * (t : Fv)) ≠ 0 := by
    intro h0; apply hQ0; rw [hQ', h0]; ring
  have hd0 : (d : Fv) ≠ 0 := by
    intro h0; apply hQ0; rw [hQ', h0, mul_zero]
  rw [hQ', sqClassOf_sq_mul hr hd0]
  rcases hd with rfl | rfl | rfl | rfl
  · simp only [Int.cast_one, sqClassOf_one]; exact (H11 v).one_mem
  · simpa using neg_one_mem_H11
  · simpa using two_mem_H11
  · simpa using neg_two_mem_H11

end CoreH

/-! ### The form $f = \mathrm{diag}(-1, 64, 2)$ -/

/-- The Gram matrix of the example (Conway–Sloane §11, p. 404): $f = \mathrm{diag}(-1, 64, 2)$. -/
def A11 : Matrix (Fin 3) (Fin 3) ℤ := !![-1, 0, 0; 0, 64, 0; 0, 0, 2]

theorem A11_symm : A11ᵀ = A11 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem A11_det : A11.det = -128 := by
  simp [A11, Matrix.det_fin_three]

theorem A11_hessian : (Cassels.Ch8Ex2.gramForm A11).hessian = !![-2, 0, 0; 0, 128, 0; 0, 0, 4] := by
  rw [hessian_csForm A11_symm]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem A11_hessian_det : (Cassels.Ch8Ex2.gramForm A11).hessian.det = -1024 := by
  rw [A11_hessian]; simp [Matrix.det_fin_three]

theorem A11_nondeg : (csQ A11).Nondegenerate := csQ_nondegenerate A11_symm (by rw [A11_det]; norm_num)

section Two

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F2" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem csQ_A11_eval (x : Fin 3 → F2) :
    (csQ A11).evalIn F2 x = -x 0 ^ 2 + 64 * x 1 ^ 2 + 2 * x 2 ^ 2 := by
  have h := two_mul_evalIn_locGram (Q := csQ A11) (v := v) 1 x
  simp only [Units.val_one, one_mulVec] at h
  have hG : ∀ k l, locGram (csQ A11) v 1 k l = (((Cassels.Ch8Ex2.gramForm A11).hessian k l : ℤ) : F2) :=
    fun k l => locGram_one_int v _ k l
  rw [dotProduct, Fin.sum_univ_three] at h
  simp only [mulVec, dotProduct, Fin.sum_univ_three, hG, A11_hessian] at h
  norm_num at h
  have h2 : (2 : F2) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  rw [h]; ring

theorem csQ_A11_bil (x : Fin 3 → F2) (j : Fin 3) :
    x ⬝ᵥ (locGram (csQ A11) v 1 *ᵥ Pi.single j 1) = ![-2 * x 0, 128 * x 1, 4 * x 2] j := by
  have hG : ∀ k l, locGram (csQ A11) v 1 k l = (((Cassels.Ch8Ex2.gramForm A11).hessian k l : ℤ) : F2) :=
    fun k l => locGram_one_int v _ k l
  fin_cases j <;>
    simp [dotProduct, mulVec, Fin.sum_univ_three, hG, A11_hessian, Pi.single_apply] <;> ring

/-- **The $2$-adic root vectors of $f = \mathrm{diag}(-1, 64, 2)$** (Conway–Sloane §11, p. 404, via the algorithm of
§9.5): every $2$-adic root vector $x$ of $\mathbb Z_2^3$ has $Q(x) \in \{\pm1, \pm2\}\mathbb Q_2^{\times 2}$.
Unconditional. -/
theorem rootNorm_A11 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x : Fin 3 → F2} (hx : IsRootVector (csQ A11) stdLat v x) :
    sqClassOf ((csQ A11).evalIn F2 x) ∈ H11 v := by
  have hγ : loc v (stdLat : Lat ℚ 3).1 = locAct v 1 (std v) := by rw [locAct_one]; exact loc_intVec v
  have hx' : IsRootVector (csQ A11) stdLat v ((1 : GL (Fin 3) F2).val *ᵥ x) := by simpa using hx
  have ineq : ∀ i j, Valued.v (![-2 * x 0, 128 * x 1, 4 * x 2] j) * Valued.v (x i) ≤
      Valued.v ((csQ A11).evalIn F2 x) := fun i j => by
    have := rootVector_ineq_gen stdLat hγ hx' i j
    simp only [Units.val_one, one_mulVec] at this
    rwa [csQ_A11_bil] at this
  have hQ0 : (csQ A11).evalIn F2 x ≠ 0 := hx.1
  rw [csQ_A11_eval] at hQ0 ineq ⊢
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (x i)) Finset.univ_nonempty
  have hxk : x k ≠ 0 := by
    intro h0
    have hz : ∀ i, x i = 0 := fun i => by
      have := hk i (Finset.mem_univ _)
      rw [h0, map_zero] at this
      exact (Valuation.zero_iff _).mp (le_antisymm this zero_le)
    apply hQ0; rw [hz 0, hz 1, hz 2]; ring
  set t := x k with ht
  have hy : ∀ i, Valued.v (x i / t) ≤ 1 := fun i => by
    rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hxk))]
    exact hk i (Finset.mem_univ _)
  set a : 𝔬 := toO v _ (hy 0) with ha
  set b : 𝔬 := toO v _ (hy 1) with hb
  set c : 𝔬 := toO v _ (hy 2) with hc
  have ea : x 0 = t * (a : F2) := by show x 0 = t * (x 0 / t); field_simp
  have eb : x 1 = t * (b : F2) := by show x 1 = t * (x 1 / t); field_simp
  have ec : x 2 = t * (c : F2) := by show x 2 = t * (x 2 / t); field_simp
  set q : 𝔬 := -a ^ 2 + 64 * b ^ 2 + 2 * c ^ 2 with hq
  have eQ : -x 0 ^ 2 + 64 * x 1 ^ 2 + 2 * x 2 ^ 2 = t ^ 2 * (q : F2) := by
    have hqc : (q : F2) = -(a : F2) ^ 2 + 64 * (b : F2) ^ 2 + 2 * (c : F2) ^ 2 := rfl
    rw [hqc, ea, eb, ec]; ring
  have hq0 : q ≠ 0 := by
    intro h0; apply hQ0; rw [eQ, h0]; simp
  have hqF : (q : F2) ≠ 0 := coe_O_ne_zero hq0
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr hxk
  have hda : q ∣ 2 * a := by
    refine dvd_of_valued_div_le hq0 ?_
    have e : ((2 * a : 𝔬) : F2) / q = -(-2 * x 0) * t / (-x 0 ^ 2 + 64 * x 1 ^ 2 + 2 * x 2 ^ 2) := by
      have h2a : ((2 * a : 𝔬) : F2) = 2 * (a : F2) := rfl
      rw [eQ, ea, h2a]; field_simp
    rw [e, map_div₀, map_mul, Valuation.map_neg, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hQ0))]
    simpa using ineq k 0
  have hdc : q ∣ 4 * c := by
    refine dvd_of_valued_div_le hq0 ?_
    have e : ((4 * c : 𝔬) : F2) / q = (4 * x 2) * t / (-x 0 ^ 2 + 64 * x 1 ^ 2 + 2 * x 2 ^ 2) := by
      have h4c : ((4 * c : 𝔬) : F2) = 4 * (c : F2) := rfl
      rw [eQ, ec, h4c]; field_simp
    rw [e, map_div₀, map_mul, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hQ0))]
    simpa using ineq k 2
  have h1 : a = 1 ∨ b = 1 ∨ c = 1 := by
    have e1 : x k / t = 1 := div_self hxk
    fin_cases k
    · exact Or.inl (Subtype.ext e1)
    · exact Or.inr (Or.inl (Subtype.ext e1))
    · exact Or.inr (Or.inr (Subtype.ext e1))
  exact mem_H11_of_goodVal h2 hQ0 eQ (rootCore h2 a b c h1 hda hdc)

/-! ### $5$ is not in $H$ -/

/-- **$5 \notin H$**: none of $5, -5, 10, -10$ is a square in $\mathbb Q_2$. -/
theorem five_not_mem_H11 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : sqClassOf (5 : F2) ∉ H11 v := by
  intro h
  rw [H11, Subgroup.mem_closure_pair] at h
  obtain ⟨m, n, hmn⟩ := h
  have h5 : (5 : F2) ≠ 0 := by norm_num
  have hn1 : (-1 : F2) ≠ 0 := by norm_num
  have h20 : (2 : F2) ≠ 0 := two_ne_zero
  rcases zpow_eq_one_or_self (sqClassOf_sq_eq_one hn1) m with hm | hm <;>
    rcases zpow_eq_one_or_self (sqClassOf_sq_eq_one h20) n with hn | hn <;>
    rw [hm, hn] at hmn
  · rw [one_mul, eq_comm, sqClassOf_eq_one_iff h5] at hmn
    exact not_isSquare_of_O (5 : 𝔬) (not_sq_five h2) hmn
  · rw [one_mul] at hmn
    have := isSquare_of_sqClassOf_eq h5 h20 hmn.symm
    refine not_isSquare_of_O (10 : 𝔬) (not_sq_ten h2) ?_
    rw [show ((10 : 𝔬) : F2) = 5 * 2 by rw [show ((10 : 𝔬) : F2) = 10 from rfl]; norm_num]
    exact this
  · rw [mul_one] at hmn
    have := isSquare_of_sqClassOf_eq h5 hn1 hmn.symm
    refine not_isSquare_of_O (-5 : 𝔬) (not_sq_neg_five h2) ?_
    rw [show ((-5 : 𝔬) : F2) = 5 * -1 by rw [show ((-5 : 𝔬) : F2) = -5 from rfl]; norm_num]
    exact this
  · rw [← sqClassOf_mul hn1 h20] at hmn
    have := isSquare_of_sqClassOf_eq h5 (mul_ne_zero hn1 h20) hmn.symm
    refine not_isSquare_of_O (-10 : 𝔬) (not_sq_neg_ten h2) ?_
    rw [show ((-10 : 𝔬) : F2) = 5 * (-1 * 2) by rw [show ((-10 : 𝔬) : F2) = -10 from rfl]; norm_num]
    exact this

end Two

/-! ### The global data: $\Pi = \{2\}$, Cassels' $j = -1$ -/

/-! The place `v2` of $\mathbb Q$ above $2$ and `primeOf_v2` are from `Section9Theorem16.lean`. -/

theorem Ex11.two_mem_v2 : (2 : 𝓞 ℚ) ∈ v2.asIdeal := (two_mem_iff_natGenerator v2).mpr primeOf_v2

/-- Conway–Sloane's $\Pi$ (without $-1$) for the example: the primes dividing $2\det H = -2^{11}$, i.e. only $2$. -/
abbrev P11 : Finset (HeightOneSpectrum (𝓞 ℚ)) := primeSet (2 * (Cassels.Ch8Ex2.gramForm A11).hessian.det)

theorem mem_P11_iff {v : HeightOneSpectrum (𝓞 ℚ)} : v ∈ P11 ↔ primeOf v = 2 := by
  show v ∈ primeSet _ ↔ _
  rw [primeSet, Finset.mem_preimage, Nat.mem_primeFactors, A11_hessian_det]
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  constructor
  · rintro ⟨-, hd, -⟩
    have h2048 : primeOf v ∣ 2 ^ 11 := by simpa using hd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2048)
  · intro h
    refine ⟨hp, ?_, by norm_num⟩
    simp only [primeOf] at h
    rw [h]; norm_num

theorem v2_mem_P11 : v2 ∈ P11 := mem_P11_iff.mpr primeOf_v2

/-- The prime $2$ as an element of $\Pi$. -/
def q11 : P11 := ⟨v2, v2_mem_P11⟩

theorem eq_q11 (p : P11) : p = q11 :=
  Subtype.ext (primeOf_injective ((mem_P11_iff.mp p.2).trans primeOf_v2.symm))

/-- $f$ is indefinite ($f(e_0) = -1 < 0 < 2 = f(e_2)$), so Cassels' $j = -1$. -/
theorem isIndefinite_A11 : IsIndefinite (csQ A11) :=
  Lattices.isIndefinite_of_neg_pos (Cassels.Ch8Ex2.gramForm A11) ![1, 0, 0] ![0, 0, 1]
    (by simp [QuadForm.evalIn, Cassels.Ch8Ex2.gramForm, A11, Fin.sum_univ_three])
    (by simp [QuadForm.evalIn, Cassels.Ch8Ex2.gramForm, A11, Fin.sum_univ_three])

theorem casselsJ_A11 : casselsJ (csQ A11) = -1 := by
  simp [casselsJ, isIndefinite_A11]

theorem Ex11.sqClass_mk_eq_sqClassOf {K : Type*} [Field K] [CharZero K] (u : Kˣ) :
    SqClass.mk u = sqClassOf (u : K) := by
  rw [sqClassOf_of_ne_zero u.ne_zero, Units.mk0_val]

theorem sqClass_primeUnit_q11 : SqClass.mk (primeUnit P11 q11) = sqClassOf (2 : q11.1.adicCompletion ℚ) := by
  rw [sqClass_mk_eq_sqClassOf]
  congr 1
  show algebraMap ℚ (v2.adicCompletion ℚ) ((natGenUnit v2 : ℚˣ) : ℚ) = 2
  simp only [natGenUnit, Units.val_mk0, show Rat.HeightOneSpectrum.natGenerator v2 = 2 from primeOf_v2,
    map_natCast]
  norm_num

/-- The unit $5$ of $\mathbb Q_2$. -/
def u5_11 : (q11.1.adicCompletion ℚ)ˣ := Units.mk0 5 (by norm_num)

theorem Ex11.valued_five_v2 : Valued.v (5 : v2.adicCompletion ℚ) = 1 := by
  have := valued_intCast_eq_one v2 5 (by rw [show Rat.HeightOneSpectrum.natGenerator v2 = 2 from primeOf_v2]; norm_num)
  simpa using this

/-! ### The $2$-adic bound, unconditional

Every $\sigma \in O^+(L_2)$, $L = \mathbb Z^3$, $f = \mathrm{diag}(-1, 64, 2)$, has $\theta(\sigma) \in H$. *Proof.* Since
$e_1$ (of norm $64$) spans the Jordan constituent of scale $2^6$, $\sigma e_1 = (64a, c, 32b)$ with $a, b, c$ integral,
and $Q(\sigma e_1) = 64$ gives $c^2 = 1 + 64a^2 - 32b^2$, so $c \equiv \pm1 \pmod{16}$. After composing with
$\tau_{e_1}$ (spinor norm $64$, a square) we may take $c = 1 - 16t$; then $t(1 - 8t) = b^2 - 2a^2$. Either
$\sigma e_1 = e_1$, or the symmetry in $x = e_1 - \sigma e_1$ (with $Q(x) = 2^{11}t$, a norm from
$\mathbb Q_2(\sqrt2)$) maps $\sigma e_1$ back to $e_1$. An isometry fixing $e_1$ acts on the binary space
$e_1^\perp = \langle -1, 2\rangle$, whose spinor norms are norms from $\mathbb Q_2(\sqrt 2)$ (computed with Wall's
formula, `spinorNorm_mem_H11_of_fix`). The norms $x^2 - 2y^2$ lie in $H$ (`normH`). -/

section DyadicBound

open Wall EvenUnimodular

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F2" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem goodVal_norm (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (a b : 𝔬) (h1 : a = 1 ∨ b = 1) :
    GoodVal (a ^ 2 - 2 * b ^ 2) := by
  rcases h1 with rfl | rfl
  · rcases isUnit_or_two_dvd h2 b with hb | ⟨b1, rfl⟩
    · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hb
      exact ⟨-1, by norm_num, 1, 2 * m, by rw [hm]; push_cast; ring⟩
    · exact ⟨1, by norm_num, 1, -b1 ^ 2, by push_cast; ring⟩
  · rcases isUnit_or_two_dvd h2 a with ha | ⟨a1, rfl⟩
    · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 ha
      exact ⟨-1, by norm_num, 1, -m, by rw [hm]; push_cast; ring⟩
    · rcases isUnit_or_two_dvd h2 a1 with ha1 | ⟨a2, rfl⟩
      · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 ha1
        exact ⟨2, by norm_num, 1, 2 * m, by
          have : (2 * a1) ^ 2 - 2 * 1 ^ 2 = 4 * a1 ^ 2 - 2 := by ring
          rw [this, hm]; push_cast; ring⟩
      · exact ⟨-2, by norm_num, 1, -a2 ^ 2, by push_cast; ring⟩

/-- **The norms $x^2 - 2y^2$ from $\mathbb Q_2(\sqrt2)$ lie in $H$.** -/
theorem normH (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (x y : F2) (h : x ^ 2 - 2 * y ^ 2 ≠ 0) :
    sqClassOf (x ^ 2 - 2 * y ^ 2) ∈ H11 v := by
  by_cases hxy : Valued.v y ≤ Valued.v x
  · have hx : x ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hxy
      have hy0 : y = 0 := (Valuation.zero_iff _).mp (le_antisymm hxy zero_le')
      apply h; rw [h0, hy0]; ring
    have hb : Valued.v (y / x) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))]; exact hxy
    refine mem_H11_of_goodVal h2 h (w := x) (q := (1 : 𝔬) ^ 2 - 2 * (toOel (y / x) hb) ^ 2) ?_
      (goodVal_norm h2 _ _ (Or.inl rfl))
    change x ^ 2 - 2 * y ^ 2 = x ^ 2 * (1 ^ 2 - 2 * (y / x) ^ 2)
    field_simp
  · push Not at hxy
    have hy : y ≠ 0 := by
      intro h0; rw [h0, map_zero] at hxy; exact (not_lt.mpr zero_le') hxy
    have ha : Valued.v (x / y) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy))]; exact hxy.le
    refine mem_H11_of_goodVal h2 h (w := y) (q := (toOel (x / y) ha) ^ 2 - 2 * (1 : 𝔬) ^ 2) ?_
      (goodVal_norm h2 _ _ (Or.inr rfl))
    change x ^ 2 - 2 * y ^ 2 = y ^ 2 * ((x / y) ^ 2 - 2 * 1 ^ 2)
    field_simp

theorem hess_A11 : (csQ A11).hessian.map (algebraMap ℚ F2) = Matrix.diagonal ![-2, 128, 4] := by
  rw [hessian_csQ_map A11_symm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, A11, smul_eq_mul] <;> push_cast <;>
    norm_num

/-- **Isometries fixing $e_1$ have spinor norms in $H$** (Wall's formula on the binary space
$e_1^\perp = \langle -1, 2\rangle$). -/
theorem spinorNorm_mem_H11_of_fix (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (ρ : orthGroup (csQ A11) F2)
    (hρ : mat (csQ A11) F2 ρ *ᵥ Pi.single 1 1 = Pi.single 1 1) : spinorNorm (csQ A11) F2 ρ ∈ H11 v := by
  obtain ⟨m, P, R, hf⟩ := exists_wallFrame (mat (csQ A11) F2 ρ)
  obtain ⟨hθ, hne, -⟩ := wall_formula A11_nondeg ρ hf
  rw [hθ]
  have hTR := hf.1
  have hcol : ∀ j, (fun k => P k j) = (1 - mat (csQ A11) F2 ρ) *ᵥ (fun k => R k j) := fun j => by
    ext k; rw [← mul_apply_col, hTR]
  -- the columns of `P` lie in `e₁^⊥`
  have hP1 : ∀ j, P 1 j = 0 := by
    intro j
    have h := orth_ker ρ (fun k => R k j) _ hρ
    rw [← hcol j, hess_A11] at h
    simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three, Pi.single_apply] at h
    exact h
  -- so `m ≤ 2`
  have hm : m ≤ 2 := by
    set P' : Matrix (Fin 2) (Fin m) F2 := Matrix.of fun i j => ![P 0 j, P 2 j] i
    have hinj : Function.Injective (Matrix.toLin' P') := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      apply hf.2.1 c
      have hc' : P' *ᵥ c = 0 := by simpa using hc
      have h0 : (P *ᵥ c) 0 = 0 := congrFun hc' 0
      have h2' : (P *ᵥ c) 2 = 0 := congrFun hc' 1
      have h1 : (P *ᵥ c) 1 = 0 := by
        show ∑ j, P 1 j * c j = 0
        simp [hP1]
      funext k
      fin_cases k
      · exact h0
      · exact h1
      · exact h2'
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  have hdiag : ∀ j, (wallGram (csQ A11) F2 P R) j j = (csQ A11).evalIn F2 (fun k => P k j) := by
    intro j
    rw [wallGram, Wall.gram_apply, hcol j]
    exact wall_diag ρ _
  have hQP : ∀ j, (csQ A11).evalIn F2 (fun k => P k j) = -(P 0 j ^ 2 - 2 * P 2 j ^ 2) := by
    intro j; rw [csQ_A11_eval]; simp [hP1]; ring
  interval_cases m
  · rw [Matrix.det_isEmpty, sqClassOf_one]
    exact (H11 v).one_mem
  · rw [Matrix.det_unique, show (default : Fin 1) = 0 from rfl, hdiag, hQP]
    have hne' : P 0 0 ^ 2 - 2 * P 2 0 ^ 2 ≠ 0 := by
      intro h0; apply hne; rw [Matrix.det_unique, show (default : Fin 1) = 0 from rfl, hdiag, hQP, h0, neg_zero]
    rw [show -(P 0 0 ^ 2 - 2 * P 2 0 ^ 2) = -1 * (P 0 0 ^ 2 - 2 * P 2 0 ^ 2) by ring,
      sqClassOf_mul (by norm_num) hne']
    exact (H11 v).mul_mem neg_one_mem_H11 (normH h2 _ _ hne')
  · -- `det C = k² - 2D²`
    have hsym := wall_symm_id (G := (csQ A11).hessian.map (algebraMap ℚ F2))
      (by rw [hess_A11]; simp) (mat_orth ρ) hTR
    have h01 : wallGram (csQ A11) F2 P R 0 1 + wallGram (csQ A11) F2 P R 1 0 =
        -2 * (P 0 0 * P 0 1) + 4 * (P 2 0 * P 2 1) := by
      have := congrFun (congrFun hsym 0) 1
      rw [Matrix.add_apply, transpose_apply] at this
      change wallGram (csQ A11) F2 P R 0 1 + wallGram (csQ A11) F2 P R 1 0 = _ at this
      rw [this, Wall.gram_apply, hess_A11]
      simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three, hP1]
      ring
    set C := wallGram (csQ A11) F2 P R
    have e : C.det = (C 0 1 - (-(P 0 0 * P 0 1) + 2 * (P 2 0 * P 2 1))) ^ 2 -
        2 * (P 0 0 * P 2 1 - P 2 0 * P 0 1) ^ 2 := by
      rw [Matrix.det_fin_two, hdiag, hdiag, hQP, hQP]
      have hC10 : C 1 0 = -2 * (P 0 0 * P 0 1) + 4 * (P 2 0 * P 2 1) - C 0 1 := by
        linear_combination h01
      rw [hC10]; ring
    rw [e] at hne ⊢
    exact normH h2 _ _ hne


theorem eq_zero_of_sq_eq_two_mul_sq (h2v : Valued.v (2 : F2) = exp (-1 : ℤ)) {x y : F2} (h : x ^ 2 = 2 * y ^ 2) :
    y = 0 := by
  by_contra hy
  have hx : x ≠ 0 := by
    intro h0; rw [h0] at h; simp at h; exact hy h
  have := congrArg Valued.v h
  rw [map_pow, map_mul, map_pow, h2v, ← exp_log (show Valued.v x ≠ 0 from (Valuation.ne_zero_iff _).mpr hx),
    ← exp_log (show Valued.v y ≠ 0 from (Valuation.ne_zero_iff _).mpr hy), ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul,
    ← WithZero.exp_add, WithZero.exp_inj] at this
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at this
  omega

/-- The key step: an isometry $\sigma_1$ with $\sigma_1e_1 = (64a, c, 32b)$, $a, b$ integral and
$c \equiv 1 \pmod{16}$, has spinor norm in $H$. -/
theorem spinorNorm_mem_H11_key (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (σ : orthGroup (csQ A11) F2) {a b c : F2}
    (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1)
    (hs : mat (csQ A11) F2 σ *ᵥ Pi.single 1 1 = ![64 * a, c, 32 * b])
    (hc : Valued.v (c - 1) ≤ exp (-4 : ℤ)) : spinorNorm (csQ A11) F2 σ ∈ H11 v := by
  have h2v : Valued.v (2 : F2) = exp (-1 : ℤ) :=
    valued_two_of_primeOf ((two_mem_iff_natGenerator v).mp h2)
  set e1 : Fin 3 → F2 := Pi.single 1 1
  have hQe1 : (csQ A11).evalIn F2 e1 = 64 := by
    rw [csQ_A11_eval]; simp [e1, Pi.single_apply]
  have hQs : (csQ A11).evalIn F2 (mat (csQ A11) F2 σ *ᵥ e1) = 64 := by
    rw [evalIn_mulVec_of_mem (csQ A11) σ.2, hQe1]
  have hQs' := hQs
  rw [hs, csQ_A11_eval] at hQs
  change -(64 * a) ^ 2 + 64 * c ^ 2 + 2 * (32 * b) ^ 2 = 64 at hQs
  have hrel : c ^ 2 = 1 + 64 * a ^ 2 - 32 * b ^ 2 := by linear_combination hQs / 64
  set t : F2 := (1 - c) / 16 with ht
  have h16 : Valued.v (16 : F2) = exp (-4 : ℤ) := by
    rw [show (16 : F2) = 2 ^ 4 by norm_num, map_pow, h2v, ← WithZero.exp_nsmul]; norm_num
  have ht1 : Valued.v t ≤ 1 := by
    rw [ht, map_div₀, h16, div_le_one₀ (zero_lt_iff.mpr exp_ne_zero), ← Valuation.map_neg, neg_sub]
    exact hc
  have htrel : t * (1 - 8 * t) = b ^ 2 - 2 * a ^ 2 := by
    rw [ht]; linear_combination (-1 / 32 : F2) * hrel
  by_cases ht0 : t = 0
  · -- `σ e₁ = e₁`
    have hc1 : c = 1 := by
      have : (1 - c) / 16 = 0 := ht0
      field_simp at this; linear_combination -this
    rw [ht0, zero_mul] at htrel
    have hb0 : a = 0 := eq_zero_of_sq_eq_two_mul_sq h2v (x := b) (by linear_combination -htrel)
    have hb0' : b = 0 := by
      rw [hb0] at htrel; have : b ^ 2 = 0 := by linear_combination -htrel
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    refine spinorNorm_mem_H11_of_fix h2 σ ?_
    rw [hs, hb0, hb0', hc1]
    ext k; fin_cases k <;> simp [Pi.single_apply]
  · set s' := mat (csQ A11) F2 σ *ᵥ e1
    have hs' : s' = ![64 * a, c, 32 * b] := hs
    set x := e1 - s'
    have hxv : x = ![-(64 * a), 1 - c, -(32 * b)] := by
      ext k; fin_cases k <;> simp [x, hs', e1, Pi.single_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
    have hQx : (csQ A11).evalIn F2 x = 2048 * t := by
      rw [csQ_A11_eval, hxv]
      change -(-(64 * a)) ^ 2 + 64 * (1 - c) ^ 2 + 2 * (-(32 * b)) ^ 2 = 2048 * t
      rw [ht]
      linear_combination (64 : F2) * hrel
    have h1t : (1 - 8 * t) ≠ 0 := by
      intro h0
      have : Valued.v (1 - 8 * t) = 1 := by
        rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left]
        · simp
        · rw [Valuation.map_neg, map_one, map_mul]
          have h8 : Valued.v (8 : F2) < 1 := by
            rw [show (8 : F2) = 2 ^ 3 by norm_num, map_pow, h2v, ← WithZero.exp_nsmul, ← exp_zero, exp_lt_exp]
            norm_num
          exact Levels.lt_one_of_lt_le h8 ht1
      rw [h0, map_zero] at this; exact zero_ne_one this
    have hQx0 : (csQ A11).evalIn F2 x ≠ 0 := by rw [hQx]; exact mul_ne_zero (by norm_num) ht0
    have hτ : mat (csQ A11) F2 (symm (csQ A11) F2 x) *ᵥ s' = e1 :=
      symm_sub_apply (csQ A11) F2 (x := e1) (y := s') (by rw [hQe1, hQs']) hQx0
    set ρ := symm (csQ A11) F2 x * σ
    have hρ : mat (csQ A11) F2 ρ *ᵥ e1 = e1 := by
      rw [mat_mul, ← mulVec_mulVec]; exact hτ
    have hθρ := spinorNorm_mem_H11_of_fix h2 ρ hρ
    have hσρ : σ = symm (csQ A11) F2 x * ρ := by
      simp only [ρ, ← mul_assoc, symm_mul_self, one_mul]
    have hmul : spinorNorm (csQ A11) F2 σ =
        spinorNorm (csQ A11) F2 (symm (csQ A11) F2 x) * spinorNorm (csQ A11) F2 ρ := by
      conv_lhs => rw [hσρ]
      exact (spinorNormHom (csQ A11) F2 A11_nondeg).map_mul _ _
    rw [hmul, spinorNorm_symm (csQ A11) F2 A11_nondeg hQx0, hQx]
    refine (H11 v).mul_mem ?_ hθρ
    -- `2048 t = 32² · 2 · t`, and `t ≡ b² - 2a²` modulo squares
    obtain ⟨w, hw⟩ := exists_sq_one_add_eight h2 (toOel (-t) (by rw [Valuation.map_neg]; exact ht1))
    have hw' : ((w : 𝔬) : F2) ^ 2 = 1 - 8 * t := by
      have := congrArg (fun z : 𝔬 => (z : F2)) hw
      simp only [toOel] at this
      push_cast at this
      rw [this, show ((8 : 𝔬) : F2) = 8 from map_ofNat (𝔬).subtype 8]; ring
    have hw0 : ((w : 𝔬) : F2) ≠ 0 := by
      intro h0; rw [h0, zero_pow two_ne_zero] at hw'; exact h1t hw'.symm
    have hnorm : b ^ 2 - 2 * a ^ 2 ≠ 0 := by rw [← htrel]; exact mul_ne_zero ht0 h1t
    have e1' : (2048 : F2) * t = (32 : F2) ^ 2 * (2 * t) := by ring
    rw [e1', sqClassOf_sq_mul (by norm_num) (mul_ne_zero two_ne_zero ht0),
      sqClassOf_mul two_ne_zero ht0]
    refine (H11 v).mul_mem two_mem_H11 ?_
    have e2 : t = ((w : 𝔬) : F2)⁻¹ ^ 2 * (b ^ 2 - 2 * a ^ 2) := by
      rw [← htrel, ← hw']; field_simp
    rw [e2, sqClassOf_sq_mul (inv_ne_zero hw0) hnorm]
    exact normH h2 b a hnorm


/-- **The $2$-adically automorphous numbers of $f = \mathrm{diag}(-1, 64, 2)$ lie in $H$** (unconditional; at any
prime $v \mid 2$). -/
theorem theta2_le_A11_gen (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (A : F2ˣ)
    (hA : A ∈ localSpinorNormGroup (csQ A11) A11_nondeg v stdLat) : SqClass.mk A ∈ H11 v := by
  have h2v : Valued.v (2 : F2) = exp (-1 : ℤ) :=
    valued_two_of_primeOf ((two_mem_iff_natGenerator v).mp h2)
  obtain ⟨σ, ⟨hσL, -⟩, hσB⟩ := (mem_localSpinorNormGroup (csQ A11) A11_nondeg v stdLat).mp hA
  rw [← hσB]
  have hdA : A11.det ≠ 0 := by rw [A11_det]; norm_num
  have hS := entries_le_one_of_mem_locStabV A11_symm hdA hσL
  have hSi := entries_le_one_of_mem_locStabV A11_symm hdA ((locStabV (csQ A11) v stdLat).inv_mem hσL)
  set S := mat (csQ A11) F2 σ
  set Si := mat (csQ A11) F2 σ⁻¹
  have hSSi : S * Si = 1 := by
    rw [← mat_mul, mul_inv_cancel]; rfl
  have hH := hess_A11 (v := v)
  have hrow : Sᵀ * Matrix.diagonal ![-2, 128, 4] = Matrix.diagonal ![-2, 128, 4] * Si := by
    have h := mat_orth σ
    rw [hH] at h
    calc Sᵀ * Matrix.diagonal ![-2, 128, 4] = Sᵀ * Matrix.diagonal ![-2, 128, 4] * (S * Si) := by
          rw [hSSi, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h]
  have h10 := congrFun (congrFun hrow 1) 0
  have h12 := congrFun (congrFun hrow 1) 2
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, transpose_apply] at h10 h12
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h10 h12
  set a := -Si 1 0
  set b := Si 1 2
  set c := S 1 1
  have ha : Valued.v a ≤ 1 := by rw [Valuation.map_neg]; exact hSi 1 0
  have hb : Valued.v b ≤ 1 := hSi 1 2
  have ha_def : a = -Si 1 0 := rfl
  have hb_def : b = Si 1 2 := rfl
  have e0 : S 0 1 = 64 * a := by linear_combination h10 / (-2) + 64 * ha_def
  have e2 : S 2 1 = 32 * b := by linear_combination h12 / 4 - 32 * hb_def
  have hs : S *ᵥ Pi.single 1 1 = ![64 * a, c, 32 * b] := by
    funext k
    rw [mulVec_single_one]
    fin_cases k
    · exact e0
    · rfl
    · exact e2
  -- `c ≡ ±1 (mod 16)`
  have hQs : (csQ A11).evalIn F2 (S *ᵥ Pi.single 1 1) = 64 := by
    rw [evalIn_mulVec_of_mem (csQ A11) σ.2, csQ_A11_eval]; simp [Pi.single_apply]
  rw [hs, csQ_A11_eval] at hQs
  change -(64 * a) ^ 2 + 64 * c ^ 2 + 2 * (32 * b) ^ 2 = 64 at hQs
  have hc2 : Valued.v ((c - 1) * (c + 1)) ≤ exp (-5 : ℤ) := by
    have e : (c - 1) * (c + 1) = 2 ^ 5 * (2 * a ^ 2 - b ^ 2) := by linear_combination hQs / 64
    rw [e, map_mul, map_pow, h2v, ← WithZero.exp_nsmul]
    have : Valued.v (2 * a ^ 2 - b ^ 2) ≤ 1 := by
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
      · rw [map_mul, map_pow]; exact mul_le_one' (by rw [h2v, ← exp_zero, exp_le_exp]; norm_num)
          (pow_le_one' ha 2)
      · rw [map_pow]; exact pow_le_one' hb 2
    calc exp (5 • (-1 : ℤ)) * Valued.v (2 * a ^ 2 - b ^ 2) ≤ exp (5 • (-1 : ℤ)) * 1 := mul_le_mul' le_rfl this
      _ = exp (-5 : ℤ) := by rw [mul_one]; norm_num
  have hdisc : ∀ x : ℤᵐ⁰, exp (-2 : ℤ) < x → exp (-1 : ℤ) ≤ x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hx)
    rw [← exp_log hx0, exp_lt_exp] at hx
    rw [← exp_log hx0, exp_le_exp]
    omega
  have hcancel : ∀ x : ℤᵐ⁰, x * exp (-1 : ℤ) ≤ exp (-5 : ℤ) → x ≤ exp (-4 : ℤ) := by
    intro x hx
    calc x = x * exp (-1 : ℤ) * exp (1 : ℤ) := by rw [mul_assoc, ← exp_add]; norm_num
      _ ≤ exp (-5 : ℤ) * exp (1 : ℤ) := mul_le_mul' hx le_rfl
      _ = exp (-4 : ℤ) := by rw [← exp_add]; norm_num
  have hcases : Valued.v (c - 1) ≤ exp (-4 : ℤ) ∨ Valued.v (c + 1) ≤ exp (-4 : ℤ) := by
    by_cases h : Valued.v (c - 1) ≤ exp (-2 : ℤ)
    · left
      have hp : Valued.v (c + 1) = exp (-1 : ℤ) := by
        rw [show c + 1 = (c - 1) + 2 by ring,
          Valuation.map_add_eq_of_lt_right _ (lt_of_le_of_lt h (by rw [h2v, exp_lt_exp]; norm_num)), h2v]
      refine hcancel _ ?_
      rw [← hp, ← map_mul]; exact hc2
    · right
      have hge := hdisc _ (lt_of_not_ge h)
      refine hcancel _ ?_
      calc Valued.v (c + 1) * exp (-1 : ℤ) ≤ Valued.v (c + 1) * Valued.v (c - 1) := mul_le_mul' le_rfl hge
        _ = Valued.v ((c - 1) * (c + 1)) := by rw [map_mul, mul_comm]
        _ ≤ exp (-5 : ℤ) := hc2
  rcases hcases with h | h
  · exact spinorNorm_mem_H11_key h2 σ ha hb hs h
  · have hQe : (csQ A11).evalIn F2 (Pi.single 1 1) = 64 := by rw [csQ_A11_eval]; simp [Pi.single_apply]
    have hQe0 : (csQ A11).evalIn F2 (Pi.single 1 1) ≠ 0 := by rw [hQe]; norm_num
    set σ₁ := symm (csQ A11) F2 (Pi.single 1 1) * σ
    have hbil : qbil (csQ A11) F2 (Pi.single 1 1) ![64 * a, c, 32 * b] = 128 * c := by
      rw [qbil, hH, single_dotProduct, one_mul, mulVec_diagonal]
      rfl
    have hs1 : mat (csQ A11) F2 σ₁ *ᵥ Pi.single 1 1 = ![64 * a, -c, 32 * b] := by
      rw [mat_mul, ← mulVec_mulVec, hs, symm_mulVec_bil (csQ A11) F2 hQe0, hbil, hQe]
      ext k; fin_cases k <;> simp [Pi.single_apply] <;> ring
    have hk := spinorNorm_mem_H11_key h2 σ₁ ha hb hs1
      (by rw [show -c - 1 = -(c + 1) by ring, Valuation.map_neg]; exact h)
    have hσ : σ = symm (csQ A11) F2 (Pi.single 1 1) * σ₁ := by
      simp only [σ₁, ← mul_assoc, symm_mul_self, one_mul]
    have hmul : spinorNorm (csQ A11) F2 σ =
        spinorNorm (csQ A11) F2 (symm (csQ A11) F2 (Pi.single 1 1)) * spinorNorm (csQ A11) F2 σ₁ := by
      conv_lhs => rw [hσ]
      exact (spinorNormHom (csQ A11) F2 A11_nondeg).map_mul _ _
    rw [hmul, spinorNorm_symm (csQ A11) F2 A11_nondeg hQe0, hQe]
    refine (H11 v).mul_mem ?_ hk
    rw [show (64 : F2) = 8 ^ 2 * 1 by norm_num, sqClassOf_sq_mul (by norm_num) one_ne_zero, sqClassOf_one]
    exact (H11 v).one_mem

end DyadicBound

/-- **The $2$-adically automorphous numbers of $f$ lie in $H = \{\pm1, \pm2\}\mathbb Q_2^{\times2}$** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §11, p. 404 (p = 2: the automorphous numbers are ±1, ±2)"]
theorem theta2_le_A11 (A : (q11.1.adicCompletion ℚ)ˣ)
    (hA : A ∈ localSpinorNormGroup (csQ A11) A11_nondeg q11.1 stdLat) : SqClass.mk A ∈ H11 q11.1 :=
  theta2_le_A11_gen two_mem_v2 A hA

open scoped Classical in
/-- $\Delta_2(5)$: the family with $5$ at $2$ is not in the spinor kernel. -/
theorem mulSingle_five_not_mem :
    (Pi.mulSingle q11 u5_11 : CasselsR P11) ∉ casselsST (csQ A11) A11_nondeg stdLat P11 := by
  classical
  refine not_mem_casselsST_of_subgroup (csQ A11) A11_nondeg stdLat P11 (by norm_num) q11 (H11 q11.1)
    (by rw [sqClass_primeUnit_q11]; exact two_mem_H11) (fun A hA => theta2_le_A11 A hA)
    (fun p hp => absurd (eq_q11 p) hp) ?_ ?_ ?_
  · rw [casselsJ_A11, sqClass_mk_eq_sqClassOf, casselsDiag_apply]
    simpa using neg_one_mem_H11
  · intro p
    rw [eq_q11 p, Pi.mulSingle_eq_same]
    exact valued_five_v2
  · rw [Pi.mulSingle_eq_same, sqClass_mk_eq_sqClassOf]
    exact five_not_mem_H11 two_mem_v2

/-! ### The example: two spinor genera, more than one class -/

/-- **Conway–Sloane §11, the example** (p. 404): *the genus of $f = \mathrm{diag}(-1, 64, 2)$ contains two spinor
genera*. Here: the genus of $\mathbb Z^3$ (with the form $f$) contains a lattice $M$ not in its (proper) spinor genus.
**Unconditional** ("$5$ is not $2$-adically automorphous": `theta2_le_A11`). -/
@[kb "conwaysloane1999" "Ch. 15, §11, pp. 404–405 (diag(−1,64,2): two spinor genera)"]
theorem example11_two_spinorGenera :
    ∃ M : Lat ℚ 3, SameGenus (csQ A11) (stdLat : Lat ℚ 3).1 M.1 ∧
      ¬ SameProperSpinorGenus (csQ A11) stdLat M :=
  exists_not_sameProperSpinorGenus (csQ A11) A11_nondeg stdLat P11 (by norm_num)
    (casselsCond_std (by norm_num) _ A11_nondeg P11 (primeSet_spec A11_symm (by rw [A11_det]; norm_num)))
    mulSingle_five_not_mem

/-- The improper integral automorph $\mathrm{diag}(-1, 1, 1)$ of $f$, over $\mathbb Z$. -/
def αZ11 : GL (Fin 3) (𝓞 ℚ) :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, 1], !![-1, 0, 0; 0, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- $\mathrm{diag}(-1, 1, 1)$ in $\mathrm{GL}_3(\mathbb Q)$. -/
def αQ11 : GL (Fin 3) ℚ := GeneralLinearGroup.map (algebraMap (𝓞 ℚ) ℚ) αZ11

theorem αQ11_val : (αQ11 : Matrix (Fin 3) (Fin 3) ℚ) = !![-1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [αQ11, αZ11]

theorem csQ_A11_hessian : (csQ A11).hessian = !![-2, 0, 0; 0, 128, 0; 0, 0, 4] := by
  rw [csQ, QuadForm.hessian_map, A11_hessian]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem αQ11_mem : αQ11 ∈ orthGroup (csQ A11) ℚ := by
  rw [mem_orthGroup, αQ11_val, csQ_A11_hessian]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- **Conway–Sloane §11, the example** (pp. 404–405): *the genus of $f = \mathrm{diag}(-1, 64, 2)$ has (at least) two
classes*: the genus of $\mathbb Z^3$ contains a lattice $M$, not in the spinor genus of $\mathbb Z^3$, onto which no
isometry of $(\mathbb Q^3, f)$ maps $\mathbb Z^3$ ($\mathbb Z^3$ has the improper automorph $\mathrm{diag}(-1,1,1)$).
**Unconditional.** -/
@[kb "conwaysloane1999" "Ch. 15, §11, pp. 404–405 (diag(−1,64,2): two classes)"]
theorem example11_two_classes :
    ∃ M : Lat ℚ 3, SameGenus (csQ A11) (stdLat : Lat ℚ 3).1 M.1 ∧
      ¬ SameProperSpinorGenus (csQ A11) stdLat M ∧
      ∀ σ : orthGroup (csQ A11) ℚ, glImage (σ : GL (Fin 3) ℚ) (stdLat : Lat ℚ 3).1 ≠ M.1 := by
  obtain ⟨M, hM, hLM⟩ := example11_two_spinorGenera
  refine ⟨M, hM, hLM, fun σ => ?_⟩
  refine not_isometric_of_not_sameProperSpinorGenus (csQ A11) A11_nondeg stdLat hLM (α := ⟨αQ11, αQ11_mem⟩) ?_ ?_ σ
  · show (αQ11 : Matrix (Fin 3) (Fin 3) ℚ).det = -1
    rw [αQ11_val]; simp [Matrix.det_fin_three]
  · exact glImage_map_intVec αZ11

/-! ### At most two spinor genera, exactly two classes -/

section Units

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F2" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- The unit square classes of $\mathbb Q_2$: every unit is $\pm s^2$ or $\pm 5s^2$. -/
theorem Ex11.exists_unit_class (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (u : F2ˣ) (hu : Valued.v (u : F2) = 1) :
    ∃ s : F2, s ≠ 0 ∧
      ((u : F2) = s ^ 2 ∨ (u : F2) = -s ^ 2 ∨ (u : F2) = 5 * s ^ 2 ∨ (u : F2) = -5 * s ^ 2) := by
  set w : 𝔬 := toO v (u : F2) hu.le with hwdef
  have hw : IsUnit w := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hu
  obtain ⟨a, ha⟩ := Rl.exists h2 w
  have hod := ha.unit_od h2 hw
  have key : ∀ y : 𝔬, IsUnit y → (∃ m, w = y + 8 * m) →
      ∃ s : F2, s ≠ 0 ∧ (u : F2) = (y : F2) * s ^ 2 := by
    rintro y hy ⟨m, hm⟩
    obtain ⟨s, hs, e⟩ := cong_sq h2 hy m hm
    refine ⟨s, fun h => hs.ne_zero (Subtype.ext h), ?_⟩
    rw [show (u : F2) = (w : F2) from rfl, e]; push_cast; ring
  have h5 : IsUnit (5 : 𝔬) := by
    have := (Rl.natCast (v := v) 5).od_unit h2 (by decide)
    simpa using this
  rcases hod with rfl | rfl | rfl | rfl
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := 1) (by simpa using ha)
    obtain ⟨s, hs, e⟩ := key 1 isUnit_one ⟨m, by simpa using hm⟩
    exact ⟨s, hs, Or.inl (by rw [e]; simp)⟩
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := -5) (by rw [show ((-5 : ℤ) : ZMod 8) = 3 by decide]; exact ha)
    obtain ⟨s, hs, e⟩ := key (-5) h5.neg ⟨m, by simpa using hm⟩
    exact ⟨s, hs, Or.inr (Or.inr (Or.inr (by rw [e, show ((-5 : 𝔬) : F2) = -5 from rfl])))⟩
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := 5) (by rw [show ((5 : ℤ) : ZMod 8) = 5 by decide]; exact ha)
    obtain ⟨s, hs, e⟩ := key 5 h5 ⟨m, by simpa using hm⟩
    exact ⟨s, hs, Or.inr (Or.inr (Or.inl (by rw [e, show ((5 : 𝔬) : F2) = 5 from rfl])))⟩
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := -1) (by rw [show ((-1 : ℤ) : ZMod 8) = 7 by decide]; exact ha)
    obtain ⟨s, hs, e⟩ := key (-1) isUnit_one.neg ⟨m, by simpa using hm⟩
    exact ⟨s, hs, Or.inr (Or.inl (by rw [e]; push_cast; ring))⟩

end Units

theorem Ex11.mk_mul_of_mem {a b : CasselsR P11} (hb : b ∈ casselsST (csQ A11) A11_nondeg stdLat P11) :
    (QuotientGroup.mk (a * b) : CasselsG (csQ A11) A11_nondeg stdLat P11) = QuotientGroup.mk a := by
  rw [QuotientGroup.eq, _root_.mul_inv_rev, inv_mul_cancel_right]
  exact (casselsST _ _ _ _).inv_mem hb

open scoped Classical in
/-- **Cassels' group $G = R/ST$ of the example has at most two elements**: every class is $1$ or the class of
$\Delta_2(5)$ ($R = XT$, $X$ = the units of $\mathbb Q_2$, and $\Delta_2(-1) = j$ lies in the spinor kernel). Unconditional. -/
theorem Ex11.mk_eq_one_or_eq (r : CasselsR P11) :
    (QuotientGroup.mk r : CasselsG (csQ A11) A11_nondeg stdLat P11) = 1 ∨
      (QuotientGroup.mk r : CasselsG (csQ A11) A11_nondeg stdLat P11) =
        QuotientGroup.mk (Pi.mulSingle q11 u5_11 : CasselsR P11) := by
  classical
  obtain ⟨x, hx, t, ht, rfl⟩ := exists_casselsX_mul_casselsT (csQ A11) A11_nondeg P11 (by norm_num) r
  have hd : casselsDiag P11 t ∈ casselsST (csQ A11) A11_nondeg stdLat P11 :=
    Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  have hj : casselsDiag P11 (casselsJ (csQ A11)) ∈ casselsST (csQ A11) A11_nondeg stdLat P11 := by
    have : casselsDiag P11 (casselsJ (csQ A11)) ∈ casselsY (csQ A11) A11_nondeg stdLat P11 := by
      rw [theorem17 _ _ _ _ (by norm_num)]; exact Subgroup.subset_closure (Or.inr rfl)
    exact this.2
  rw [Ex11.mk_mul_of_mem hd]
  obtain ⟨s, hs0, hcases⟩ := Ex11.exists_unit_class (v := q11.1) Ex11.two_mem_v2 (x q11) (hx q11)
  set S : CasselsR P11 := Pi.mulSingle q11 (Units.mk0 s hs0) with hS
  set J : CasselsR P11 := casselsDiag P11 (casselsJ (csQ A11)) with hJ
  set X0 : CasselsR P11 := Pi.mulSingle q11 u5_11 with hX0
  have hS2 : S ^ 2 ∈ casselsST (csQ A11) A11_nondeg stdLat P11 :=
    Subgroup.mem_sup_left (sq_mem_casselsS _ _ _ _ S)
  have hext : ∀ y z : CasselsR P11, ((y q11 : (q11.1.adicCompletion ℚ)ˣ) : q11.1.adicCompletion ℚ) =
      ((z q11 : (q11.1.adicCompletion ℚ)ˣ) : q11.1.adicCompletion ℚ) → y = z := fun y z h => by
    funext p
    obtain rfl := eq_q11 p
    exact Units.ext h
  have vS : ((S ^ 2) q11 : q11.1.adicCompletion ℚ) = s ^ 2 := by
    rw [hS, Pi.pow_apply, Pi.mulSingle_eq_same, Units.val_pow_eq_pow_val, Units.val_mk0]
  have vJ : ((J q11 : (q11.1.adicCompletion ℚ)ˣ) : q11.1.adicCompletion ℚ) = -1 := by
    rw [hJ, casselsDiag_apply, casselsJ_A11]; simp
  have vX : ((X0 q11 : (q11.1.adicCompletion ℚ)ˣ) : q11.1.adicCompletion ℚ) = 5 := by
    rw [hX0, Pi.mulSingle_eq_same]; rfl
  rcases hcases with h | h | h | h
  · left
    rw [hext x (S ^ 2) (by rw [vS]; exact h)]
    exact (QuotientGroup.eq_one_iff _).mpr hS2
  · left
    rw [hext x (J * S ^ 2) (by rw [Pi.mul_apply, Units.val_mul, vS, vJ, h]; ring)]
    exact (QuotientGroup.eq_one_iff _).mpr ((casselsST _ _ _ _).mul_mem hj hS2)
  · right
    rw [hext x (X0 * S ^ 2) (by rw [Pi.mul_apply, Units.val_mul, vS, vX, h]), Ex11.mk_mul_of_mem hS2]
  · right
    rw [hext x (X0 * (J * S ^ 2)) (by rw [Pi.mul_apply, Pi.mul_apply, Units.val_mul, Units.val_mul, vS, vX, vJ, h]; ring),
      Ex11.mk_mul_of_mem ((casselsST _ _ _ _).mul_mem hj hS2)]

theorem Ex11.casselsCond_A11 : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P11 → ∀ u : (v.adicCompletion ℚ)ˣ,
    u ∈ localSpinorNormGroup (csQ A11) A11_nondeg v stdLat ↔ IsUnitSqClass v (SqClass.mk u) :=
  casselsCond_std (by norm_num) _ A11_nondeg P11 (primeSet_spec A11_symm (by rw [A11_det]; norm_num))

/-- **At most two spinor genera** (Conway–Sloane §11, p. 404, "two spinor genera"; the upper bound): of any two
lattices $M_1, M_2$ in the genus of $\mathbb Z^3$ (with the form $f = \mathrm{diag}(-1, 64, 2)$), one is in the proper
spinor genus of $\mathbb Z^3$ or they are in the same proper spinor genus. Unconditional. -/
@[kb "conwaysloane1999" "Ch. 15, §11, pp. 404–405 (diag(−1,64,2): at most two spinor genera)"]
theorem example11_at_most_two_spinorGenera {M₁ M₂ : Lat ℚ 3}
    (h₁ : SameGenus (csQ A11) (stdLat : Lat ℚ 3).1 M₁.1) (h₂ : SameGenus (csQ A11) (stdLat : Lat ℚ 3).1 M₂.1) :
    SameProperSpinorGenus (csQ A11) stdLat M₁ ∨ SameProperSpinorGenus (csQ A11) stdLat M₂ ∨
      SameProperSpinorGenus (csQ A11) M₁ M₂ := by
  classical
  have : IsPrincipalIdealRing (𝓞 ℚ) := pid_rat
  let _ : MulAction (OAf (csQ A11)) (Lat ℚ 3) := latAction (csQ A11)
  have hP := Ex11.casselsCond_A11
  obtain ⟨Γ₁, hMΓ₁, β₁, rfl, hβ₁, -, hβ₁1, hΓ₁P⟩ :=
    exists_sameProperSpinorGenus_casselsForm_rat (csQ A11) A11_nondeg (by norm_num) stdLat P11 hP h₁
  obtain ⟨Γ₂, hMΓ₂, β₂, rfl, hβ₂, -, hβ₂1, hΓ₂P⟩ :=
    exists_sameProperSpinorGenus_casselsForm_rat (csQ A11) A11_nondeg (by norm_num) stdLat P11 hP h₂
  obtain ⟨z₁, hz₁⟩ := exists_casselsR_rep (csQ A11) P11 β₁
  obtain ⟨z₂, hz₂⟩ := exists_casselsR_rep (csQ A11) P11 β₂
  have h1 : ∀ w : P11, SqClass.mk ((1 : CasselsR P11) w) =
      spinorNorm (csQ A11) (w.1.adicCompletion ℚ) ((1 : OAf (csQ A11)) w) := by
    intro w
    rw [show ((1 : OAf (csQ A11)) w) = 1 from rfl, ← spinorNormHom_apply (csQ A11) _ A11_nondeg, map_one]
    rfl
  have e1 : latSMul (csQ A11) (1 : OAf (csQ A11)) stdLat = stdLat := one_smul (OAf (csQ A11)) _
  have hone : ∀ w, (1 : OAf (csQ A11)) w ∈ Tamagawa.soSub (csQ A11) (w.adicCompletion ℚ) :=
    fun w => (Tamagawa.soSub (csQ A11) _).one_mem
  have shift := fun {α α' : OAf (csQ A11)} (hα : ∀ w, α w ∈ Tamagawa.soSub (csQ A11) (w.adicCompletion ℚ))
      (hα' : ∀ w, α' w ∈ Tamagawa.soSub (csQ A11) (w.adicCompletion ℚ)) (hαP : ∀ w, w ∉ P11 → α w = 1)
      (hα'P : ∀ w, w ∉ P11 → α' w = 1) (x x' : CasselsR P11)
      (hx : ∀ w : P11, SqClass.mk (x w) = spinorNorm (csQ A11) (w.1.adicCompletion ℚ) (α w))
      (hx' : ∀ w : P11, SqClass.mk (x' w) = spinorNorm (csQ A11) (w.1.adicCompletion ℚ) (α' w))
      (hxx : (QuotientGroup.mk x : CasselsG (csQ A11) A11_nondeg stdLat P11) = QuotientGroup.mk x') =>
    sameProperSpinorGenus_casselsShift (csQ A11) A11_nondeg stdLat P11 hP (SameGenus.refl _ _) (fun _ _ => rfl)
      (fun _ _ => rfl) (SameProperSpinorGenus.refl _ _) α α' hα hα' hαP hα'P x x' hx hx' hxx
  rcases Ex11.mk_eq_one_or_eq z₁ with hz₁1 | hz₁5
  · left
    have := shift hβ₁ hone hβ₁1 (fun _ _ => rfl) z₁ 1 hz₁ h1 hz₁1
    rw [e1] at this
    exact SameProperSpinorGenus.trans _ (SameProperSpinorGenus.symm _ this) (SameProperSpinorGenus.symm _ hMΓ₁)
  rcases Ex11.mk_eq_one_or_eq z₂ with hz₂1 | hz₂5
  · right; left
    have := shift hβ₂ hone hβ₂1 (fun _ _ => rfl) z₂ 1 hz₂ h1 hz₂1
    rw [e1] at this
    exact SameProperSpinorGenus.trans _ (SameProperSpinorGenus.symm _ this) (SameProperSpinorGenus.symm _ hMΓ₂)
  · right; right
    have := shift hβ₁ hβ₂ hβ₁1 hβ₂1 z₁ z₂ hz₁ hz₂ (hz₁5.trans hz₂5.symm)
    exact SameProperSpinorGenus.trans _ hMΓ₁ (SameProperSpinorGenus.trans _ this (SameProperSpinorGenus.symm _ hMΓ₂))

/-- **Conway–Sloane §11, the example** (pp. 404–405): *the genus of $f = \mathrm{diag}(-1, 64, 2)$ has exactly two
classes*: there is a lattice $M$ in the genus of $\mathbb Z^3$ that is not the image of $\mathbb Z^3$ under any isometry,
and every lattice of the genus is properly isometric to $\mathbb Z^3$ or to $M$ (Eichler's theorem, Cassels Ch. 11,
Thm. 1.4: $f$ is indefinite and $n = 3$). **Unconditional.** -/
@[kb "conwaysloane1999" "Ch. 15, §11, pp. 404–405 (diag(−1,64,2): exactly two classes)"]
theorem example11_exactly_two_classes :
    ∃ M : Lat ℚ 3, SameGenus (csQ A11) (stdLat : Lat ℚ 3).1 M.1 ∧
      (∀ σ : orthGroup (csQ A11) ℚ, glImage (σ : GL (Fin 3) ℚ) (stdLat : Lat ℚ 3).1 ≠ M.1) ∧
      ∀ N : Lat ℚ 3, SameGenus (csQ A11) (stdLat : Lat ℚ 3).1 N.1 →
        IsProperIsometric (csQ A11) (stdLat : Lat ℚ 3).1 N.1 ∨ IsProperIsometric (csQ A11) M.1 N.1 := by
  obtain ⟨M, hM, hLM, hσ⟩ := example11_two_classes
  refine ⟨M, hM, hσ, fun N hN => ?_⟩
  rcases example11_at_most_two_spinorGenera hM hN with h | h | h
  · exact absurd h hLM
  · exact Or.inl (isProperIsometric_of_sameProperSpinorGenus _ (by norm_num) A11_nondeg isIndefinite_A11 h)
  · exact Or.inr (isProperIsometric_of_sameProperSpinorGenus _ (by norm_num) A11_nondeg isIndefinite_A11 h)

end QuadFormsKB.ConwaySloane
