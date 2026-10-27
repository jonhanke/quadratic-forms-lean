/-
# The rank of an even unimodular positive definite lattice is divisible by 8

**Layer:** integer-valued positive definite forms $Q$ in $n$ variables (`IntQF n`, `IntQF.PosDef`) with Hessian $H$,
$Q(\vec x) = \tfrac12\vec x^{\mathsf T}H\vec x$; theta series `theta Q` (`Siegel/Theta.lean`, `Siegel/ThetaModular.lean`).

**Proves**
* `eight_dvd_of_posDef_det_one`: if $Q$ is positive definite and $\det H = 1$ (an even unimodular lattice), then
  $8 \mid n$.

*Proof:* (Serre, *A Course in Arithmetic*, Ch. VII, §6.1, Cor. 1 to Thm. 7.) The Hessian is symmetric with even diagonal, so
$\det H$ is even when $n$ is odd (`det_even_of_odd`); hence $n = 2k$. Since $\det H = 1$, $\Theta_{Q^*} = \Theta_Q$
and `theta_S'` gives $\Theta_Q(-1/z) = (-i)^k z^k\,\Theta_Q(z)$ (`theta_S_unimodular_neg_I`); with $\Theta_Q(z+1) =
\Theta_Q(z)$ this says that $\Theta_Q$ is a weight-$k$ form for $S$ and $T$ up to the constant $(-i)^k$. Iterating $z \mapsto
-1/(z+1)$ three times at $z = i$ returns to $i$ (the relation $(ST)^3 = \pm 1$ in $\mathrm{SL}_2(\mathbb Z)$), and gives
$\Theta_Q(i) = (-i)^{k}\,\Theta_Q(i)$. As $\Theta_Q(i) > 0$ (a sum of positive terms), $(-i)^k = 1$, so $4 \mid k$.
This is elementary (no slash action, no valence formula).
-/
import QuadFormsKB.Siegel.LevelCharacter

open Complex Matrix Filter Topology

namespace QuadFormsKB.Siegel

noncomputable section

variable {n : ℕ}

/-- **Inversion law for an even unimodular form, any even rank:** if $Q$ is positive definite, $\det H = 1$ and $n = 2k$,
then for $\operatorname{Im} z > 0$
$$\Theta_Q(-1/z) = (-i)^k\, z^k\, \Theta_Q(z).$$
(`theta_S_unimodular` is the case $4 \mid k$, where $(-i)^k = 1$.) *Proof:* `theta_S'`, $\det H = 1$,
$\Theta_{Q^*} = \Theta_Q$ and $(n : \mathbb C)/2 = k$. -/
theorem theta_S_unimodular_neg_I {Q : IntQF n} (hQ : Q.PosDef) (hdet : Q.hessian.det = 1) {k : ℕ}
    (hn : n = 2 * k) {z : ℂ} (hz : 0 < z.im) :
    theta Q (-1 / z) = (-I) ^ k * z ^ k * theta Q z := by
  rw [theta_S' hQ hz, hdet, thetaDual_eq_theta_of_isUnit (by rw [hdet]; exact isUnit_one),
    show ((n : ℂ) / 2) = ((k : ℕ) : ℂ) by rw [hn]; push_cast; ring, cpow_natCast, mul_pow]
  simp

/-- One step of the iteration: for $\operatorname{Im} w > 0$ (hypotheses of `theta_S_unimodular_neg_I`),
$\Theta_Q(-1/(w+1)) = (-i)^k (w+1)^k\,\Theta_Q(w)$, using $\Theta_Q(w + 1) = \Theta_Q(w)$ (`theta_add_one`). -/
private theorem theta_step {Q : IntQF n} (hQ : Q.PosDef) (hdet : Q.hessian.det = 1) {k : ℕ}
    (hn : n = 2 * k) {w : ℂ} (hw : 0 < w.im) :
    theta Q (-1 / (w + 1)) = (-I) ^ k * (w + 1) ^ k * theta Q w := by
  rw [theta_S_unimodular_neg_I hQ hdet hn (by simpa using hw), theta_add_one]

/-- **$\Theta_Q(i) \ne 0$** for $Q$ positive definite: $\Theta_Q(i) = \sum_{\vec x} e^{-2\pi Q(\vec x)}$ is a convergent
sum of positive real numbers. -/
theorem theta_I_ne_zero {Q : IntQF n} (hQ : Q.PosDef) : theta Q I ≠ 0 := by
  have hterm : ∀ x : Fin n → ℤ, cexp (2 * Real.pi * I * I * (Q.eval x : ℂ)) =
      ((Real.exp (-(2 * Real.pi * (Q.eval x : ℝ))) : ℝ) : ℂ) := by
    intro x
    rw [Complex.ofReal_exp]; congr 1; push_cast
    rw [mul_assoc (2 * (Real.pi : ℂ)) I I, I_mul_I]; ring
  have hsum : Summable fun x : Fin n → ℤ => cexp (2 * Real.pi * I * I * (Q.eval x : ℂ)) :=
    summable_theta_term hQ (by simp)
  simp_rw [hterm] at hsum
  have hsumR := Complex.summable_ofReal.mp hsum
  have hpos : 0 < ∑' x : Fin n → ℤ, Real.exp (-(2 * Real.pi * (Q.eval x : ℝ))) :=
    hsumR.tsum_pos (fun x => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  unfold theta
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum]
  exact_mod_cast hpos.ne'

/-- $(-i)^k = 1$ implies $4 \mid k$. -/
private theorem four_dvd_of_neg_I_pow {k : ℕ} (h : (-I) ^ k = 1) : 4 ∣ k := by
  have h4 : (-I) ^ 4 = (1 : ℂ) := by rw [neg_pow, I_pow_four]; norm_num
  have hk : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
  rw [hk, pow_add, pow_mul, h4, one_pow, one_mul] at h
  have hr : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have : k % 4 = 0 := by
    interval_cases hr' : k % 4
    · rfl
    · exfalso; have := congrArg Complex.re h; simp at this
    · exfalso; rw [neg_pow, I_sq] at h; norm_num at h
    · exfalso
      have : (-I) ^ 3 = I := by rw [neg_pow, show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]; ring
      rw [this] at h; have := congrArg Complex.re h; simp at this
  omega

/-- **The rank of an even unimodular positive definite lattice is divisible by 8.** If $Q$ is an integer-valued positive
definite form in $n$ variables whose Hessian $H$ has $\det H = 1$ (equivalently: $f = 2Q$ is a positive definite
classically integral form with all $f_{ii}$ even and $\det(f_{ij}) = 1$), then $8 \mid n$.

*Proof:* Serre's argument via theta series (see the module header): $n$ is even because the even symmetric matrix $H$
of odd size has even determinant (`det_even_of_odd`); for $n = 2k$ the transformations
$\Theta_Q(-1/z) = (-i)^k z^k\Theta_Q(z)$, $\Theta_Q(z+1) = \Theta_Q(z)$ iterated along $z \mapsto -1/(z+1)$ at $z = i$
(a 3-cycle $i \mapsto \frac{-1+i}{2} \mapsto -1+i \mapsto i$, with $(1+i)\cdot\frac{1+i}{2}\cdot i = -1$) give
$\Theta_Q(i) = (-i)^k\,\Theta_Q(i)$ and $\Theta_Q(i) > 0$. -/
@[kb "serre1973" "Ch. VII, §6.1, Cor. 1 to Thm. 7 [unverified]"]
theorem eight_dvd_of_posDef_det_one {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) (hdet : Q.hessian.det = 1) :
    8 ∣ n := by
  -- n is even
  have hev : Even n := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have := det_even_of_odd hodd (hessian_isEvenSymm Q)
    rw [hdet] at this
    exact absurd this (by decide)
  obtain ⟨k, hk⟩ := hev
  have hn : n = 2 * k := by omega
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (-I) ^ k := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = (-1 + I) / 2 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℂ, d = -1 + I := ⟨_, rfl⟩
  have hI1 : (I + 1 : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have hb1 : (b + 1 : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hb] at this; linarith
  have hd1 : (d + 1 : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp [hd] at this
  have e1 : -1 / (I + 1 : ℂ) = b := by
    rw [hb, div_eq_div_iff hI1 (by norm_num)]; linear_combination (-1 : ℂ) * I_sq
  have e2 : -1 / (b + 1 : ℂ) = d := by
    rw [div_eq_iff hb1, hb, hd]; linear_combination (-1 / 2 : ℂ) * I_sq
  have e3 : -1 / (d + 1 : ℂ) = I := by
    rw [div_eq_iff hd1, hd]; linear_combination (-1 : ℂ) * I_sq
  have hbim : 0 < b.im := by simp [hb]
  have hdim : 0 < d.im := by simp [hd]
  have h1 := theta_step hQ hdet hn (w := I) (by simp)
  have h2 := theta_step hQ hdet hn hbim
  have h3 := theta_step hQ hdet hn hdim
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [← hc] at h1 h2 h3
  have hprod : (d + 1) * (b + 1) * (I + 1) = -1 := by
    rw [hb, hd]; linear_combination ((I + 2) / 2 : ℂ) * I_sq
  have key : theta Q I = c ^ 3 * (-1) ^ k * theta Q I := by
    calc theta Q I = c * (d + 1) ^ k * theta Q d := h3
      _ = c * (d + 1) ^ k * (c * (b + 1) ^ k * (c * (I + 1) ^ k * theta Q I)) := by rw [h2, h1]
      _ = c ^ 3 * ((d + 1) * (b + 1) * (I + 1)) ^ k * theta Q I := by
          rw [mul_pow, mul_pow]; ring
      _ = c ^ 3 * (-1) ^ k * theta Q I := by rw [hprod]
  have hne := theta_I_ne_zero hQ
  have hone : c ^ 3 * (-1) ^ k = 1 := by
    have := mul_right_cancel₀ hne (key.symm.trans (one_mul _).symm)
    exact this
  have hnI : (-I) ^ k = 1 := by
    have hI3 : (-I : ℂ) ^ 3 = I := by
      rw [show (-I : ℂ) ^ 3 = -(I ^ 2 * I) by ring, I_sq]; ring
    rw [← hone, hc, ← pow_mul, mul_comm k 3, pow_mul, hI3, ← mul_pow]
    congr 1; ring
  have h4 := four_dvd_of_neg_I_pow hnI
  omega

end

end QuadFormsKB.Siegel
