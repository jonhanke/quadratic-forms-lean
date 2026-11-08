/-
# Cassels, Chapter 11, Example 11: the global-congruence reading is false

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Example 11 (p. 253), as formalized by the named
statement `Ex11Statement` (`Ch11Examples3.lean`). Indices are 0-based.

**Result** (`not_ex11Statement`, *proved*). `Ex11Statement` is false. It asks for $\alpha \in O^+(V)$ (a *global* rational
rotation) with $\alpha b - \eta_p b \in p \Lambda$ (the *global* lattice $p\Lambda \subset V$) for every $p \in P^*$, and
$\alpha \Lambda_p = \Lambda_p$ for $p \ne q$.

**Counterexample.** $V = \mathbb Q^3$, $Q = x_0^2 + x_1^2 + 57 x_2^2$ ($57 = 3 \cdot 19$), $\Lambda = \mathbb Z^3$ (so $Q$ is
integer-valued on $\Lambda$), $q = 5$ ($Q$ is isotropic over $\mathbb Q_5$: $-61/64 \equiv 1 \bmod 5^3$ is a square $s^2$ and
$(8s)^2 + 2^2 + 57 = 0$), $P^* = \{3, 19\}$ (both $\equiv 3 \bmod 4$, so $x^2 + y^2$ is anisotropic mod $p$; a primitive zero of
$Q$ over $\mathbb Z_p$ would have $p \mid x, y$, then $p^2 \mid 57 z^2$, so $p \mid z$; hence $Q$ is anisotropic over $\mathbb Q_3$
and $\mathbb Q_{19}$), $b = (0, 0, 1)$ with $Q(b) = 57$ of valuation exactly $1$ at $3$ and $19$, $\eta_{19} = 1$, $\eta_3 = -1$
($\eta = 1$ elsewhere). The determinant hypothesis holds with $\gamma = 1$: the Gram matrix of the bilinear form is
$\operatorname{diag}(2, 2, 114)$ of determinant $456 = 2^3 \cdot 3 \cdot 19$, of valuation $e^{-1}$ at $3$ and at $19$.

**Why no $\alpha$ exists.** Put $x = \alpha b \in \mathbb Q^3$. The conditions say $x - b \in 19 \mathbb Z^3$ and
$x + b \in 3 \mathbb Z^3$, so $x_2 = 1 + 19 m$ with $m \in \mathbb Z$ and $x_2 + 1 = 3 m'$. Since $\alpha$ preserves $Q$,
$x_0^2 + x_1^2 + 57 x_2^2 = Q(x) = Q(b) = 57$, hence $x_2^2 \le 1$, forcing $m = 0$, $x_2 = 1$; then $2 = 3 m'$, a
contradiction. (Only the third coordinate and the invariance of $Q$ are used; the hypotheses at $q$ and on the determinant are
irrelevant to the contradiction.)

**The faithful reading.** The conclusion in the exercise is the *local* congruence $\alpha b \equiv \eta_p b \pmod{p \Lambda_p}$
(in $\Lambda_p$, i.e. in $\mathbb Z_p^3$ after localization), which is how Example 11 is used in the hint to Example 12 (apply
it at primes dividing $g$, where only the local behaviour of $\alpha$ at $p$ matters). The global congruence mod $p\Lambda$
asks for a single rational $\alpha b$ that is simultaneously close to $\pm b$ at several primes, which is false as above.

**Axioms.** Only `propext`, `Classical.choice`, `Quot.sound`.
-/
import QuadFormsKB.Literature.Cassels.Ch11Examples3
import QuadFormsKB.Literature.Cassels.Ch11Sec8Cor

open Polynomial Matrix NumberField IsDedekindDomain WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Cassels

namespace Ex11Counter

/-- **One step of the descent for $x^2 + y^2 + p k z^2 = 0$ over $\mathbb Z_p$.** If $-1$ is not a square mod $p$ (`hsq`: the
form $a^2 + b^2$ has only the trivial zero in $\mathbb Z/p$) and $p \nmid k$, then every $\mathbb Z_p$-solution has $x, y, z$
all in $p\mathbb Z_p$ (their residues mod $p$ vanish). Arguments: `p` prime, `hsq`, `k`, `hk`, `x y z`, `h` the equation. -/
theorem step_padic (p : ℕ) [hp : Fact p.Prime] (hsq : ∀ a b : ZMod p, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0)
    (k : ℕ) (hk : ¬ p ∣ k) (x y z : ℤ_[p])
    (h : x ^ 2 + y ^ 2 + (p : ℤ_[p]) * k * z ^ 2 = 0) :
    PadicInt.toZMod x = 0 ∧ PadicInt.toZMod y = 0 ∧ PadicInt.toZMod z = 0 := by
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  have h1 := congrArg PadicInt.toZMod h
  simp only [map_add, map_mul, map_pow, map_natCast, map_zero, hp0, zero_mul, add_zero] at h1
  obtain ⟨hx, hy⟩ := hsq _ _ h1
  refine ⟨hx, hy, ?_⟩
  have hdiv : ∀ w : ℤ_[p], PadicInt.toZMod w = 0 → ∃ w1 : ℤ_[p], w = p * w1 := by
    intro w hw
    have : w ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod]; exact hw
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc⟩
  obtain ⟨x1, rfl⟩ := hdiv x hx
  obtain ⟨y1, rfl⟩ := hdiv y hy
  have hp1 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h2 : (p : ℤ_[p]) * ((p : ℤ_[p]) * (x1 ^ 2 + y1 ^ 2) + k * z ^ 2) = 0 := by
    linear_combination h
  have h3 : (p : ℤ_[p]) * (x1 ^ 2 + y1 ^ 2) + k * z ^ 2 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hp1
    · exact h
  have h4 := congrArg PadicInt.toZMod h3
  simp only [map_add, map_mul, map_pow, map_natCast, map_zero, hp0, zero_mul, zero_add] at h4
  have hk0 : (k : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h hk0
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h


/-- **Anisotropy of $x^2 + y^2 + p k z^2$ over $\mathbb Q_p$** under the hypotheses of `step_padic`: any $\mathbb Q_p$-solution
is $0$. Proof: divide by the coordinate of largest norm to get a $\mathbb Z_p$-solution with a unit coordinate, contradicting
`step_padic`. -/
theorem aniso_padic (p : ℕ) [hp : Fact p.Prime] (hsq : ∀ a b : ZMod p, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0)
    (k : ℕ) (hk : ¬ p ∣ k) (x y z : ℚ_[p])
    (h : x ^ 2 + y ^ 2 + (p : ℚ_[p]) * k * z ^ 2 = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  classical
  by_contra hne
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image ({x, y, z} : Finset ℚ_[p]) norm (by simp)
  have hx := hmax x (by simp)
  have hy := hmax y (by simp)
  have hz := hmax z (by simp)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hne
    refine ⟨?_, ?_, ?_⟩
    · exact norm_le_zero_iff.mp (by simpa using hx)
    · exact norm_le_zero_iff.mp (by simpa using hy)
    · exact norm_le_zero_iff.mp (by simpa using hz)
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hint : ∀ w : ℚ_[p], ‖w‖ ≤ ‖a‖ → ‖w / a‖ ≤ 1 := fun w hw => by
    rw [norm_div, div_le_one hn]; exact hw
  let x' : ℤ_[p] := ⟨x / a, hint x hx⟩
  let y' : ℤ_[p] := ⟨y / a, hint y hy⟩
  let z' : ℤ_[p] := ⟨z / a, hint z hz⟩
  have heq : x' ^ 2 + y' ^ 2 + (p : ℤ_[p]) * k * z' ^ 2 = 0 := by
    apply Subtype.ext
    have h2 : (x / a) ^ 2 + (y / a) ^ 2 + (p : ℚ_[p]) * k * (z / a) ^ 2 = 0 := by
      have : (x / a) ^ 2 + (y / a) ^ 2 + (p : ℚ_[p]) * k * (z / a) ^ 2
          = (x ^ 2 + y ^ 2 + (p : ℚ_[p]) * k * z ^ 2) / a ^ 2 := by field_simp
      rw [this, h, zero_div]
    have e : ((x' ^ 2 + y' ^ 2 + (p : ℤ_[p]) * k * z' ^ 2 : ℤ_[p]) : ℚ_[p]) =
        (x / a) ^ 2 + (y / a) ^ 2 + (p : ℚ_[p]) * k * (z / a) ^ 2 := by
      push_cast; rfl
    rw [e]; simpa using h2
  obtain ⟨h1, h2, h3⟩ := step_padic p hsq k hk x' y' z' heq
  have hone : ∀ w' : ℤ_[p], PadicInt.toZMod w' = 0 → (w' : ℚ_[p]) = 1 → False := by
    intro w' hw hw1
    have : w' = 1 := Subtype.ext (by simpa using hw1)
    rw [this, map_one] at hw
    exact one_ne_zero hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact hone x' h1 (div_self ha0)
  · exact hone y' h2 (div_self ha0)
  · exact hone z' h3 (div_self ha0)

/-- $a^2 + b^2 = 0$ in $\mathbb Z/3$ forces $a = b = 0$ (finite check). -/
theorem aniso_three : ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
/-- $a^2 + b^2 = 0$ in $\mathbb Z/19$ forces $a = b = 0$ (finite check). -/
theorem aniso_nineteen : ∀ a b : ZMod 19, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide


/-! ### primes -/

/-- **The height-one prime of $\mathcal O_{\mathbb Q}$ over the rational prime $p$.** -/
def primeSpec (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

/-- `primeSpec p` corresponds to $p$ under `primesEquiv`. -/
theorem primesEquiv_primeSpec (p : ℕ) (hp : p.Prime) :
    (Rat.HeightOneSpectrum.primesEquiv (primeSpec p hp) : ℕ) = p :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩)

/-- The natural generator of `primeSpec p` is $p$. -/
theorem natGenerator_primeSpec (p : ℕ) (hp : p.Prime) :
    Rat.HeightOneSpectrum.natGenerator (primeSpec p hp) = p := primesEquiv_primeSpec p hp

/-- **Membership in a prime of $\mathcal O_{\mathbb Q}$:** $a \in \mathfrak p$ iff $p \mid a$ (via $\mathcal O_{\mathbb Q} \cong \mathbb Z$),
where $p$ is the natural generator of $\mathfrak p$. -/
theorem mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a : 𝓞 ℚ) :
    a ∈ v.asIdeal ↔ (Rat.HeightOneSpectrum.natGenerator v : ℤ) ∣ Rat.ringOfIntegersEquiv a := by
  rw [← Ideal.mem_span_singleton, Rat.HeightOneSpectrum.span_natGenerator]
  have := Ideal.apply_mem_of_equiv_iff (f := (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))) (I := v.asIdeal) (x := a)
  rw [← this]
  simp

/-- A prime of $\mathcal O_{\mathbb Q}$ is the principal ideal generated by its natural generator. -/
theorem asIdeal_eq_span (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)} := by
  ext a
  rw [mem_asIdeal_iff, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Rat.ringOfIntegersEquiv.symm c, ?_⟩
    apply Rat.ringOfIntegersEquiv.injective
    simpa using hc
  · rintro ⟨c, rfl⟩
    exact ⟨Rat.ringOfIntegersEquiv c, by simp⟩


open QuadFormsKB.Lattices

/-- **The inclusion $\mathcal O_{\mathbb Q} \to \mathbb Q$ is $\mathbb Z \to \mathbb Q$:** `algebraMap (𝓞 ℚ) ℚ r` is the image of
`Rat.ringOfIntegersEquiv r`. -/
theorem algebraMap_eq_ringOfIntegersEquiv (r : 𝓞 ℚ) :
    algebraMap (𝓞 ℚ) ℚ r = (Rat.ringOfIntegersEquiv r : ℚ) := by
  conv_lhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply r]
  have e : Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r) = ((Rat.ringOfIntegersEquiv r : ℤ) : 𝓞 ℚ) :=
    eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _
  rw [e, map_intCast]

/-- **Coordinates of $\mathfrak p \Lambda$ for $\Lambda = \mathbb Z^3$:** every coordinate of an element of
`v.asIdeal • intVec` is $p$ times an integer, $p$ the natural generator of $v$. -/
theorem coord_of_mem_smul_intVec (v : HeightOneSpectrum (𝓞 ℚ)) {z : Fin 3 → ℚ}
    (hz : z ∈ v.asIdeal • (intVec : Submodule (𝓞 ℚ) (Fin 3 → ℚ))) (i : Fin 3) :
    ∃ m : ℤ, z i = (Rat.HeightOneSpectrum.natGenerator v : ℚ) * m := by
  revert i
  refine Submodule.smul_induction_on (p := fun z => ∀ i, ∃ m : ℤ,
    z i = (Rat.HeightOneSpectrum.natGenerator v : ℚ) * m) hz (fun r hr n hn i => ?_) (fun a b ha hb i => ?_)
  · obtain ⟨a, ha⟩ := hn i
    obtain ⟨c, hc⟩ := (mem_asIdeal_iff v r).mp hr
    refine ⟨c * Rat.ringOfIntegersEquiv a, ?_⟩
    have hr' := algebraMap_eq_ringOfIntegersEquiv r
    have ha' := algebraMap_eq_ringOfIntegersEquiv a
    rw [smul_apply_int, ← ha, hr', ha', hc]
    push_cast; ring
  · obtain ⟨m, hm⟩ := ha i
    obtain ⟨m', hm'⟩ := hb i
    exact ⟨m + m', by rw [Pi.add_apply, hm, hm']; push_cast; ring⟩

section LocalInst

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **Valuation of $p k$ at $\mathfrak p$:** if $p \nmid k$ then $|p k|_{\mathfrak p} = e^{-1}$, in $\mathbb Q_{\mathfrak p}$. -/
theorem val_prime_mul (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) (hk : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ k) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((Rat.HeightOneSpectrum.natGenerator v : ℚ) * k)) =
      exp (-1 : ℤ) := by
  set p := Rat.HeightOneSpectrum.natGenerator v with hpdef
  have hpp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  rw [valued_algebraMap v]
  have e : ((p : ℚ) * k) = algebraMap (𝓞 ℚ) ℚ ((p : 𝓞 ℚ) * (k : 𝓞 ℚ)) := by simp
  have hp0 : (p : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  rw [e, HeightOneSpectrum.valuation_of_algebraMap, map_mul,
    HeightOneSpectrum.intValuation_singleton v (r := (p : 𝓞 ℚ)) hp0 (asIdeal_eq_span v),
    HeightOneSpectrum.intValuation_eq_one_iff.mpr, mul_one]
  · rw [mem_asIdeal_iff, map_natCast]
    exact_mod_cast hk


/-- **The counterexample form** $Q = x_0^2 + x_1^2 + 57 x_2^2$ over $\mathbb Q$ ($57 = 3 \cdot 19$). -/
def ex11Q : QuadForm ℚ 3 := QuadForm.diag ![1, 1, 57]

/-- Values of the form: $Q(x) = x_0^2 + x_1^2 + 57 x_2^2$ over any $\mathbb Q$-algebra. -/
theorem ex11Q_evalIn (K : Type*) [CommRing K] [Algebra ℚ K] (x : Fin 3 → K) :
    ex11Q.evalIn K x = x 0 ^ 2 + x 1 ^ 2 + 57 * x 2 ^ 2 := by
  simp [ex11Q, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three, Matrix.diagonal]
  rw [map_ofNat]; ring

/-- The Hessian is $\operatorname{diag}(2, 2, 114)$. -/
theorem ex11Q_hessian : ex11Q.hessian = Matrix.diagonal ![2, 2, 114] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ex11Q, QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> norm_num

/-- The form is nondegenerate: the Hessian has determinant $456 \ne 0$. -/
theorem ex11Q_nondegenerate : ex11Q.Nondegenerate := by
  rw [QuadForm.Nondegenerate, ex11Q_hessian, det_diagonal, Fin.prod_univ_three]
  norm_num

/-- $5$ is prime. -/
local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- $|2|_5 = 1$. -/
theorem norm_two_five : ‖(2 : ℚ_[5])‖ = 1 := by
  have h1 : ‖((2 : ℤ) : ℤ_[5])‖ ≤ 1 := PadicInt.norm_le_one _
  have h2 : ¬ ‖((2 : ℤ) : ℤ_[5])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]; norm_num
  have : ((2 : ℤ) : ℤ_[5]) = 2 := by norm_num
  rw [this] at h1 h2
  exact le_antisymm h1 (not_lt.mp h2)

/-- $|{-125}/64|_5 < |2|_5^2 / 8$, the hypothesis of the square-near-one lemma for $-61/64$. -/
theorem norm_125 : ‖((-125 : ℚ_[5]) / 64)‖ < ‖(2 : ℚ_[5])‖ ^ 2 / 8 := by
  rw [norm_two_five, norm_div, norm_neg]
  have h64 : ‖(64 : ℚ_[5])‖ = 1 := by
    have : (64 : ℚ_[5]) = 2 ^ 6 := by norm_num
    rw [this, norm_pow, norm_two_five, one_pow]
  have h125 : ‖(125 : ℚ_[5])‖ = 1 / 125 := by
    have : (125 : ℚ_[5]) = (5 : ℚ_[5]) ^ 3 := by norm_num
    have h5 : ‖(5 : ℚ_[5])‖ = 1 / 5 := by simpa using Padic.norm_p (p := 5)
    rw [this, norm_pow, h5]
    norm_num
  rw [h64, h125]; norm_num


/-- **$Q$ is isotropic over $\mathbb Q_5$:** $-61/64 \equiv 1 \pmod{5^3}$ is a square $s^2$, and
$(8 s)^2 + 2^2 + 57 \cdot 1^2 = 0$. -/
theorem ex11Q_isotropic_five : ex11Q.IsotropicIn ℚ_[5] := by
  obtain ⟨s, hs⟩ : IsSquare ((-61 / 64 : ℚ_[5])) := by
    refine Lattices.isSquare_of_norm_sub_one_lt (by norm_num) ?_
    have : (-61 / 64 : ℚ_[5]) - 1 = (-125 : ℚ_[5]) / 64 := by norm_num
    rw [this]; exact norm_125
  refine ⟨![8 * s, 2, 1], ?_, ?_⟩
  · intro h
    have := congrFun h 2
    simp at this
  · rw [ex11Q_evalIn]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have : (8 * s) ^ 2 = 64 * (s * s) := by ring
    rw [this, ← hs]; norm_num

/-- **Anisotropy at a prime dividing $57$ once:** if the natural generator $p$ of $v$ has $57 = p k$ with $p \nmid k$ and
$-1$ a nonsquare mod $p$ (`hsq`), then $Q$ is anisotropic over the completion at $v$ (transported to $\mathbb Q_p$). -/
theorem ex11Q_aniso (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ)
    (hsq : ∀ a b : ZMod (Rat.HeightOneSpectrum.natGenerator v), a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0)
    (hk : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ k)
    (h57 : (57 : ℚ) = (Rat.HeightOneSpectrum.natGenerator v : ℚ) * k) :
    ¬ ex11Q.IsotropicIn (v.adicCompletion ℚ) := by
  have : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  rintro hiso
  have hiso' : ex11Q.IsotropicIn ℚ_[Rat.HeightOneSpectrum.natGenerator v] :=
    isotropicIn_of_ringHom ex11Q (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.toRingHom hiso
  obtain ⟨x, hx0, hx⟩ := hiso'
  rw [ex11Q_evalIn] at hx
  have h57' : (57 : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) =
      (Rat.HeightOneSpectrum.natGenerator v : ℚ_[Rat.HeightOneSpectrum.natGenerator v]) * k := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℚ_[Rat.HeightOneSpectrum.natGenerator v])) h57
  rw [h57'] at hx
  obtain ⟨h0, h1, h2⟩ := aniso_padic _ hsq k hk (x 0) (x 1) (x 2) (by linear_combination hx)
  apply hx0
  funext i
  fin_cases i <;> simpa

/-- **The determinant hypothesis of Example 11 at $v$, with $\gamma = 1$:** if $456 = p k$ with $p \nmid k$, the Gram matrix
$\operatorname{diag}(2,2,114)$ has determinant of valuation $e^{-1}$ and $\Lambda_v = \mathfrak o_v^3$. -/
theorem ex11_hdet (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) (hk : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ k)
    (h : (456 : ℚ) = (Rat.HeightOneSpectrum.natGenerator v : ℚ) * k) :
    ∃ γ : GL (Fin 3) (v.adicCompletion ℚ), loc v (stdLat : Lat ℚ 3).1 = locAct v γ (std v) ∧
        Valued.v (locGram ex11Q v γ).det = exp (-1 : ℤ) := by
  refine ⟨1, ?_, ?_⟩
  · rw [locAct_one]; exact loc_intVec v
  · have e : locGram ex11Q v 1 = (Matrix.diagonal ![2, 2, 114] : Matrix (Fin 3) (Fin 3) ℚ).map
        (algebraMap ℚ (v.adicCompletion ℚ)) := by
      simp [locGram, ex11Q_hessian]
    rw [e, show (Matrix.diagonal ![2, 2, 114] : Matrix (Fin 3) (Fin 3) ℚ).map (algebraMap ℚ (v.adicCompletion ℚ)) =
      (algebraMap ℚ (v.adicCompletion ℚ)).mapMatrix (Matrix.diagonal ![2, 2, 114]) from rfl, ← RingHom.map_det]
    have : (Matrix.diagonal ![2, 2, 114] : Matrix (Fin 3) (Fin 3) ℚ).det =
        (Rat.HeightOneSpectrum.natGenerator v : ℚ) * k := by
      rw [det_diagonal, Fin.prod_univ_three]; rw [← h]; norm_num
    rw [this]
    exact val_prime_mul v k hk

/-- **The valuation of $Q(b)$:** for $b = (0,0,1)$, $Q(b) = 57 = p k$ has valuation $e^{-1}$. -/
theorem ex11_hbv (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) (hk : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ k)
    (h : (57 : ℚ) = (Rat.HeightOneSpectrum.natGenerator v : ℚ) * k) :
    Valued.v (ex11Q.evalIn (v.adicCompletion ℚ) (locVec v (![0, 0, 1] : Fin 3 → ℚ))) = exp (-1 : ℤ) := by
  have e : ex11Q.evalIn (v.adicCompletion ℚ) (locVec v (![0, 0, 1] : Fin 3 → ℚ)) =
      algebraMap ℚ (v.adicCompletion ℚ) ((Rat.HeightOneSpectrum.natGenerator v : ℚ) * k) := by
    rw [ex11Q_evalIn, ← h]
    simp [locVec_apply]
  rw [e]
  exact val_prime_mul v k hk

end LocalInst

/-- Isotropy does not depend on the choice of `Algebra ℚ K` structure (a subsingleton). -/
theorem isotropicIn_instance_irrel {K : Type*} [CommRing K] (i1 i2 : Algebra ℚ K) (Q : QuadForm ℚ 3) :
    @QuadForm.IsotropicIn ℚ _ 3 K _ i1 Q ↔ @QuadForm.IsotropicIn ℚ _ 3 K _ i2 Q := by
  cases Subsingleton.elim i1 i2; exact Iff.rfl

/-- Evaluation does not depend on the choice of `Algebra ℚ K` structure (a subsingleton). -/
theorem evalIn_instance_irrel {K : Type*} [CommRing K] (i1 i2 : Algebra ℚ K) (Q : QuadForm ℚ 3) :
    @QuadForm.evalIn ℚ _ 3 K _ i1 Q = @QuadForm.evalIn ℚ _ 3 K _ i2 Q := by
  cases Subsingleton.elim i1 i2; rfl

end Ex11Counter

open Ex11Counter QuadFormsKB.Lattices in
/-- **Example 11 (global-congruence reading) is false.** Counterexample: $Q = x_0^2 + x_1^2 + 57 x_2^2$ on $\Lambda = \mathbb Z^3$,
$q = 5$, $P^* = \{3, 19\}$, $b = (0, 0, 1)$, $\eta_{19} = 1$, $\eta_3 = -1$; see the module docstring. Every hypothesis of
`Ex11Statement` holds but no rotation $\alpha$ satisfies $\alpha b - b \in 19 \Lambda$ and $\alpha b + b \in 3 \Lambda$. -/
@[kb "cassels1978" "Ch. 11, Ex. 11, p. 253 (the global-congruence reading is false; counterexample)"]
theorem not_ex11Statement : ¬ Ex11Statement := by
  intro H
  have p3 : Nat.Prime 3 := by norm_num
  have p19 : Nat.Prime 19 := by norm_num
  have p5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨p5⟩
  set v3 := primeSpec 3 p3 with hv3
  set v19 := primeSpec 19 p19 with hv19
  set v5 := primeSpec 5 p5 with hv5
  have g3 : Rat.HeightOneSpectrum.natGenerator v3 = 3 := natGenerator_primeSpec 3 p3
  have g19 : Rat.HeightOneSpectrum.natGenerator v19 = 19 := natGenerator_primeSpec 19 p19
  have hint : ∀ x ∈ (stdLat : Lat ℚ 3).1, ∃ z : ℤ, ex11Q.eval x = z := by
    intro x hx
    obtain ⟨a, rfl⟩ := mem_intVec_iff_exists.mp hx
    refine ⟨Rat.ringOfIntegersEquiv (a 0) ^ 2 + Rat.ringOfIntegersEquiv (a 1) ^ 2 +
      57 * Rat.ringOfIntegersEquiv (a 2) ^ 2, ?_⟩
    rw [QuadForm.eval, ex11Q_evalIn]
    simp only [intCoe, algebraMap_eq_ringOfIntegersEquiv]
    push_cast; ring
  have hiso5 : ex11Q.IsotropicIn (v5.adicCompletion ℚ) :=
    (isotropicIn_instance_irrel _ _ _).mp
      (isotropicIn_adicCompletion_of_padic ex11Q v5 5 (primesEquiv_primeSpec 5 p5).symm ex11Q_isotropic_five)
  have h2 : ∀ v ∈ ({v3, v19} : Set (HeightOneSpectrum (𝓞 ℚ))), (2 : 𝓞 ℚ) ∉ v.asIdeal := by
    intro v hv
    rw [mem_asIdeal_iff, map_ofNat]
    rcases hv with rfl | rfl
    · rw [g3]; norm_num
    · rw [g19]; norm_num
  have hani : ∀ v ∈ ({v3, v19} : Set (HeightOneSpectrum (𝓞 ℚ))), ¬ ex11Q.IsotropicIn (v.adicCompletion ℚ) := by
    intro v hv
    rcases hv with rfl | rfl
    · exact fun h => ex11Q_aniso _ 19 (by rw [g3]; exact aniso_three) (by rw [g3]; norm_num) (by rw [g3]; norm_num) ((isotropicIn_instance_irrel _ _ _).mpr h)
    · exact fun h => ex11Q_aniso _ 3 (by rw [g19]; exact aniso_nineteen) (by rw [g19]; norm_num) (by rw [g19]; norm_num) ((isotropicIn_instance_irrel _ _ _).mpr h)
  have hdet : ∀ v ∈ ({v3, v19} : Set (HeightOneSpectrum (𝓞 ℚ))), ∃ γ : GL (Fin 3) (v.adicCompletion ℚ),
      loc v (stdLat : Lat ℚ 3).1 = locAct v γ (std v) ∧ Valued.v (locGram ex11Q v γ).det = exp (-1 : ℤ) := by
    intro v hv
    rcases hv with rfl | rfl
    · exact ex11_hdet _ 152 (by rw [g3]; norm_num) (by rw [g3]; norm_num)
    · exact ex11_hdet _ 24 (by rw [g19]; norm_num) (by rw [g19]; norm_num)
  have hb : (![0, 0, 1] : Fin 3 → ℚ) ∈ (stdLat : Lat ℚ 3).1 := by
    refine mem_intVec_iff_exists.mpr ⟨![0, 0, 1], ?_⟩
    funext i; fin_cases i <;> simp [intCoe]
  have hbv : ∀ v ∈ ({v3, v19} : Set (HeightOneSpectrum (𝓞 ℚ))),
      Valued.v (ex11Q.evalIn (v.adicCompletion ℚ) (locVec v (![0, 0, 1] : Fin 3 → ℚ))) = exp (-1 : ℤ) := by
    intro v hv
    rcases hv with rfl | rfl
    · rw [evalIn_instance_irrel _ _ _]; exact ex11_hbv _ 19 (by rw [g3]; norm_num) (by rw [g3]; norm_num)
    · rw [evalIn_instance_irrel _ _ _]; exact ex11_hbv _ 3 (by rw [g19]; norm_num) (by rw [g19]; norm_num)
  obtain ⟨α, hα, h1, -⟩ := H.holds ex11Q ex11Q_nondegenerate stdLat hint v5 hiso5 {v3, v19} h2 hani hdet
    ![0, 0, 1] hb hbv (fun v => if Rat.HeightOneSpectrum.natGenerator v = 3 then -1 else 1)
    (fun v _ => by by_cases h : Rat.HeightOneSpectrum.natGenerator v = 3 <;> simp [h])
  set x : Fin 3 → ℚ := ((α : orthGroup ex11Q ℚ) : GL (Fin 3) ℚ).val.mulVec ![0, 0, 1] with hx
  have hQx : ex11Q.evalIn ℚ x = 57 := by
    rw [hx, evalIn_mulVec_of_mem ex11Q (α : orthGroup ex11Q ℚ).2, ex11Q_evalIn]
    simp
  have e19 := h1 v19 (by simp)
  have e3 := h1 v3 (by simp)
  simp only [g19, g3] at e19 e3
  obtain ⟨m19, hm19⟩ := coord_of_mem_smul_intVec v19 e19 2
  obtain ⟨m3, hm3⟩ := coord_of_mem_smul_intVec v3 e3 2
  simp only [g19, g3] at hm19 hm3
  rw [ex11Q_evalIn] at hQx
  simp at hm19 hm3
  have hx2 : x 2 = 1 + 19 * (m19 : ℚ) := by linarith
  have hle : ((1 + 19 * m19 : ℤ) : ℚ) ^ 2 ≤ 1 := by
    push_cast; rw [← hx2]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have hle' : (1 + 19 * m19) ^ 2 ≤ (1 : ℤ) := by exact_mod_cast hle
  have hm0 : m19 = 0 := by nlinarith
  have h3 : (2 : ℚ) = 3 * m3 := by rw [hm0] at hx2; push_cast at hx2; linarith
  have h3' : (2 : ℤ) = 3 * m3 := by exact_mod_cast h3
  omega

end QuadFormsKB.Cassels
