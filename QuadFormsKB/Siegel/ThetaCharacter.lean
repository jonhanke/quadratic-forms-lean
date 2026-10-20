/-
# The character of an even-rank form, modulo the level (stage B)

Let $Q$ be a positive definite integral form in $n = 2k$ variables with Hessian $H$, level $N = N_Q$ (`level`), and
$\Delta = (-1)^k\det H$ (`disc`, equal to `thetaDisc Q k`). Two value functions for "the" character existed before this
file: `chi Q b` $= \left(\frac{\Delta}{b}\right)$ (Jacobi symbol at odd $b$; `LevelCharacter.lean`, as the Dirichlet character
`chiChar` modulo $4N$) and `thetaChi Q k N d` $= \left(\frac{\Delta}{\tilde d}\right)$ at an odd positive $\tilde d \equiv d \pmod N$
(`ThetaGamma0.lean`, the multiplier of $\Theta_Q$ on $\Gamma_0(N)$). This file reconciles them.

* **The canonical character** is `chiCharLevel hQ hn : DirichletCharacter ℤ (level Q)`, the character modulo $N_Q$ itself;
  on units $x$ it is `thetaChi Q k (level Q) x.val` (`chiCharLevel_apply`), and at an integer $d$ prime to $N_Q$ it is
  $\left(\frac{\Delta}{x}\right)$ for every odd $x \ge 1$, $x \equiv d \pmod{N_Q}$ (`chiCharLevel_intCast_eq_chi`).
* Agreement: `changeLevel_chiCharLevel` (lifting it to modulus $4N_Q$ gives `chiChar`), `thetaChi_eq_chi`,
  `thetaChi_eq_of_dvd` (`thetaChi` does not depend on the chosen level $N$), `thetaChi_eq_chiCharLevel`,
  `chiCharLevel_natCast_of_odd` (equal to `chi` at every odd $b$).
* `chi_eq_of_modEq_level`: $\chi_Q(b) = \chi_Q(b')$ for odd $b \equiv b' \pmod{N_Q}$ (periodicity modulo $N$, not just $4N$).
* `theta_gamma0_chiCharLevel`: the $\Gamma_0(N)$ law of `theta_gamma0_chi` with the canonical character.
* `kroneckerSym`, `chiCharLevel_two`, `chiCharLevel_natCast_eq_kroneckerSym`: for odd $N_Q$ the character at even $d$ is the
  Kronecker symbol $\left(\frac{\Delta}{d}\right)$ (with $\left(\frac{\Delta}{2}\right) = \chi_8(\Delta)$ for odd $\Delta$).

All of this rests on the theta transformation law (`jacobiSym_thetaDisc_periodic`, via Dirichlet's theorem), so it is
proved for **positive definite** $Q$ only. For indefinite $Q$ periodicity modulo $N$ is still true classically (2-adic
Jordan decomposition) but not formalized [unverified].
-/
import QuadFormsKB.Siegel.LevelCharacter
import QuadFormsKB.Siegel.ThetaGamma0

open Matrix

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### Discriminants and levels -/

/-- For $n = 2k$ the two discriminants agree: `thetaDisc Q k` $= (-1)^k\det H =$ `disc Q`. -/
theorem thetaDisc_eq_disc (Q : QuadForm ℤ n) {k : ℕ} (hn : n = 2 * k) : thetaDisc Q k = disc Q := by
  rw [thetaDisc, disc, show n / 2 = k by omega]

/-- The level $N_Q$ is a level in the sense of `IsThetaLevel`. -/
theorem isThetaLevel_level {Q : IntQF n} (hQ : Q.PosDef) : IsThetaLevel Q (level Q) :=
  (isLevel_iff_isThetaLevel hQ.nondegenerate).1 (isLevel_level hQ.nondegenerate)

/-! ### `thetaChi` versus `chi` -/

/-- `thetaChi` at $d$ is `chi` at the odd representative $\tilde d$ = `oddRep N d` (by definition, for $n = 2k$). -/
theorem thetaChi_eq_chi_oddRep (Q : QuadForm ℤ n) {k : ℕ} (hn : n = 2 * k) (N : ℕ) (d : ℤ) :
    thetaChi Q k N d = chi Q (oddRep N d) := by
  rw [thetaChi, chi, thetaDisc_eq_disc Q hn]

/-- **Bridge `thetaChi` = `chi`:** for $Q$ positive definite, $n = 2k$, $N$ a level and $\gcd(d, N) = 1$,
$\chi_Q(d)$ (`thetaChi`) $= \left(\frac{\Delta}{x}\right)$ (`chi Q x`) for every odd $x \ge 1$ with $x \equiv d \pmod N$. -/
theorem thetaChi_eq_chi {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {d : ℤ} (hd : IsCoprime d N) {x : ℕ} (hx : Odd x)
    (hxd : (x : ℤ) % N = d % N) : thetaChi Q k N d = chi Q x := by
  rw [thetaChi_eq_jacobiSym hQ hn hN0 hN hd hx hxd, chi, thetaDisc_eq_disc Q hn]

/-- **`thetaChi` does not depend on the level:** if $N$ is a level, $N \mid M$ and $\gcd(d, M) = 1$, then
`thetaChi Q k M d = thetaChi Q k N d`. -/
theorem thetaChi_eq_of_dvd {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N M : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) (hM0 : 0 < M) (hNM : N ∣ M) {d : ℤ} (hd : IsCoprime d M) :
    thetaChi Q k M d = thetaChi Q k N d := by
  obtain ⟨h1, h2, -⟩ := oddRep_spec hM0 hd
  have hdN : IsCoprime d N := hd.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hNM)
  exact (thetaChi_eq_jacobiSym hQ hn hN0 hN hdN h1
    (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 hNM) h2)).symm

/-! ### The character modulo a level -/

private lemma isCoprime_val {N : ℕ} [NeZero N] {x : ZMod N} (hx : IsUnit x) :
    IsCoprime (x.val : ℤ) (N : ℤ) := by
  rw [Nat.isCoprime_iff_coprime]
  have := ZMod.val_coe_unit_coprime hx.unit
  rwa [IsUnit.unit_spec] at this

private lemma cast_eq_iff {N : ℕ} {a : ℕ} {d : ℤ} :
    (a : ℤ) % N = d % N ↔ (a : ZMod N) = (d : ZMod N) := by
  rw [← Int.cast_natCast (R := ZMod N) a]
  exact (ZMod.intCast_eq_intCast_iff _ _ _).symm

private lemma oddRep_val {N : ℕ} (hN0 : 0 < N) {x : ZMod N} (hx : IsUnit x) :
    Odd (oddRep N x.val) ∧ ((oddRep N x.val : ℕ) : ZMod N) = x := by
  have : NeZero N := ⟨hN0.ne'⟩
  obtain ⟨h1, h2, -⟩ := oddRep_spec hN0 (isCoprime_val hx)
  refine ⟨h1, ?_⟩
  rw [cast_eq_iff] at h2
  rw [h2, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- At a unit $x$ of $\mathbb{Z}/N$: `thetaChi Q k N x.val` $= \left(\frac{\Delta_Q}{a}\right)$ for every odd $a$ with $a \equiv x$. -/
lemma thetaChi_val {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ} (hN0 : 0 < N)
    (hN : IsThetaLevel Q N) {x : ZMod N} (hx : IsUnit x) {a : ℕ} (ha : Odd a)
    (hax : (a : ZMod N) = x) : thetaChi Q k N x.val = jacobiSym (thetaDisc Q k) a := by
  have : NeZero N := ⟨hN0.ne'⟩
  refine thetaChi_eq_jacobiSym hQ hn hN0 hN (isCoprime_val hx) ha ?_
  rw [cast_eq_iff, Int.cast_natCast, ZMod.natCast_zmod_val]
  exact hax

/-- **$\chi_Q$ as a Dirichlet character modulo a level $N$** (values in $\mathbb{Z}$): $x \mapsto$ `thetaChi Q k N x.val` on
units of $\mathbb{Z}/N$, $0$ on non-units. Well defined and multiplicative because `thetaChi` is the Jacobi symbol
$\left(\frac{\Delta_Q}{\cdot}\right)$ at **any** odd representative (`thetaChi_eq_jacobiSym`, from the theta transformation law). -/
noncomputable def thetaChiChar {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) : DirichletCharacter ℤ N where
  toFun x := by classical exact if IsUnit x then thetaChi Q k N x.val else 0
  map_one' := by
    classical
    simp only [isUnit_one, ite_true]
    rw [thetaChi_val hQ hn hN0 hN isUnit_one odd_one Nat.cast_one, jacobiSym.one_right]
  map_mul' x y := by
    classical
    by_cases hx : IsUnit x
    · by_cases hy : IsUnit y
      · simp only [hx, hy, hx.mul hy, ite_true]
        obtain ⟨ox, cx⟩ := oddRep_val hN0 hx
        obtain ⟨oy, cy⟩ := oddRep_val hN0 hy
        rw [thetaChi_val hQ hn hN0 hN (hx.mul hy) (ox.mul oy) (by push_cast; rw [cx, cy]),
          jacobiSym.mul_right' _ ox.pos.ne' oy.pos.ne']
        rfl
      · simp [hy, hx, IsUnit.mul_iff]
    · simp [hx, IsUnit.mul_iff]
  map_nonunit' x hx := by classical simp [hx]

theorem thetaChiChar_apply {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {x : ZMod N} (hx : IsUnit x) :
    thetaChiChar hQ hn hN0 hN x = thetaChi Q k N x.val := by
  classical
  show (if IsUnit x then thetaChi Q k N x.val else 0) = _
  simp [hx]

/-- At an integer $d$ prime to $N$: `thetaChiChar` $(d \bmod N)$ = `thetaChi Q k N d`. -/
theorem thetaChiChar_intCast {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {d : ℤ} (hd : IsCoprime d N) :
    thetaChiChar hQ hn hN0 hN (d : ZMod N) = thetaChi Q k N d := by
  have : NeZero N := ⟨hN0.ne'⟩
  have hu : IsUnit (d : ZMod N) := ⟨ZMod.unitOfIsCoprime d hd, ZMod.coe_unitOfIsCoprime d hd⟩
  rw [thetaChiChar_apply hQ hn hN0 hN hu]
  apply thetaChi_congr
  rw [ZMod.val_intCast, Int.emod_emod_of_dvd _ dvd_rfl]

/-- **The canonical character of $Q$** ($n = 2k$, $Q$ positive definite): $\chi_Q$ as a Dirichlet character modulo the
level $N_Q$ itself (`thetaChiChar` at $N = N_Q$). This is the character of $\Theta_Q \in M_k(\Gamma_0(N_Q), \chi_Q)$
(`theta_gamma0_chiCharLevel`); the value functions `chi` (Jacobi symbol at odd $b$), `thetaChi` (at an odd representative
modulo any level) and the modulus-$4N_Q$ character `chiChar` all agree with it (`chiCharLevel_intCast_eq_chi`,
`thetaChi_eq_chiCharLevel`, `changeLevel_chiCharLevel`). For odd $N_Q$ its values at even $d$ are the Kronecker symbol
(`chiCharLevel_natCast_eq_kroneckerSym`). -/
@[kb "hanke2004" "p. 357 / §4 p. 364 (the character χ, mod N) [unverified]"]
noncomputable def chiCharLevel {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) :
    DirichletCharacter ℤ (level Q) :=
  thetaChiChar hQ hn (level_pos hQ.nondegenerate) (isThetaLevel_level hQ)

theorem chiCharLevel_apply {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k)
    {x : ZMod (level Q)} (hx : IsUnit x) : chiCharLevel hQ hn x = thetaChi Q k (level Q) x.val :=
  thetaChiChar_apply hQ hn _ _ hx

/-- **`chiCharLevel` = `chi`:** for $\gcd(d, N_Q) = 1$, $\chi_Q(d \bmod N_Q) = \left(\frac{\Delta}{x}\right)$ for every odd
$x \ge 1$ with $x \equiv d \pmod{N_Q}$. -/
theorem chiCharLevel_intCast_eq_chi {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {d : ℤ}
    (hd : IsCoprime d (level Q)) {x : ℕ} (hx : Odd x) (hxd : (x : ℤ) % level Q = d % level Q) :
    chiCharLevel hQ hn (d : ZMod (level Q)) = chi Q x := by
  rw [chiCharLevel, thetaChiChar_intCast hQ hn _ _ hd,
    thetaChi_eq_chi hQ hn (level_pos hQ.nondegenerate) (isThetaLevel_level hQ) hd hx hxd]

/-- **`thetaChi` = `chiCharLevel`:** for any level $N$ (a multiple of $N_Q$) and $\gcd(d, N) = 1$, the multiplier character
`thetaChi Q k N d` of `theta_gamma0_chi` is the canonical character at $d \bmod N_Q$. -/
theorem thetaChi_eq_chiCharLevel {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {d : ℤ} (hd : IsCoprime d N) :
    thetaChi Q k N d = chiCharLevel hQ hn (d : ZMod (level Q)) := by
  have hNQ : level Q ∣ N :=
    (isLevel_iff_level_dvd hQ.nondegenerate).1 ((isLevel_iff_isThetaLevel hQ.nondegenerate).2 hN)
  rw [chiCharLevel, thetaChiChar_intCast hQ hn _ _
      (hd.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hNQ)),
    thetaChi_eq_of_dvd hQ hn (level_pos hQ.nondegenerate) (isThetaLevel_level hQ) hN0 hNQ hd]

/-- **`chiChar` is `chiCharLevel` lifted to modulus $4N_Q$** (Mathlib's `DirichletCharacter.changeLevel`). In particular
`chiChar` is induced from a character modulo $N_Q$. -/
theorem changeLevel_chiCharLevel {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) :
    DirichletCharacter.changeLevel (dvd_mul_left (level Q) 4) (chiCharLevel hQ hn) =
      chiChar hQ.nondegenerate := by
  have hL0 := level_pos hQ.nondegenerate
  have : NeZero (4 * level Q) := ⟨by omega⟩
  refine MulChar.ext fun u => ?_
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, chiChar_apply _ u.isUnit]
  have hu : IsUnit (ZMod.cast (u : ZMod (4 * level Q)) : ZMod (level Q)) :=
    (ZMod.unitsMap (dvd_mul_left (level Q) 4) u).isUnit
  have hcast : (ZMod.cast (u : ZMod (4 * level Q)) : ZMod (level Q)) =
      (((u : ZMod (4 * level Q)).val : ℤ) : ZMod (level Q)) := by
    rw [Int.cast_natCast, ZMod.cast_eq_val]
  have hco : IsCoprime (((u : ZMod (4 * level Q)).val : ℕ) : ℤ) (level Q) := by
    have : NeZero (level Q) := ⟨hL0.ne'⟩
    have := isCoprime_val hu
    rw [hcast, ZMod.val_intCast] at this
    have h' := this.add_mul_left_left ((((u : ZMod (4 * level Q)).val : ℕ) : ℤ) / level Q)
    rwa [Int.emod_add_mul_ediv] at h'
  have hodd : Odd (u : ZMod (4 * level Q)).val := by
    rcases Nat.even_or_odd (u : ZMod (4 * level Q)).val with he | ho
    · exfalso
      have hc := ZMod.val_coe_unit_coprime u
      have : 2 ∣ Nat.gcd (u : ZMod (4 * level Q)).val (4 * level Q) :=
        Nat.dvd_gcd (even_iff_two_dvd.1 he) (Dvd.dvd.mul_right (by norm_num) _)
      rw [hc] at this; omega
    · exact ho
  rw [hcast, chiCharLevel_intCast_eq_chi hQ hn hco hodd rfl]

/-- **$\chi_Q$ is periodic modulo $N_Q$** (item 3; for positive definite $Q$, $n$ even): $\chi_Q(b) = \chi_Q(b')$ for odd
$b, b' \ge 1$ with $b \equiv b' \pmod{N_Q}$. Strengthens `chi_eq_of_modEq` (modulo $4N_Q$). If $\gcd(b, N_Q) > 1$ both
sides are $0$: a common prime of $b$ and $N_Q$ divides $\Delta$ (`prime_dvd_level_iff`). -/
@[kb "hanke2004" "p. 357 (the character for even n, mod N) [unverified]"]
theorem chi_eq_of_modEq_level {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {b b' : ℕ}
    (hb : Odd b) (hb' : Odd b') (h : b ≡ b' [MOD level Q]) : chi Q b = chi Q b' := by
  have hQn := hQ.nondegenerate
  have hL0 := level_pos hQn
  have hz : (b : ℤ) % level Q = (b' : ℤ) % level Q := by exact_mod_cast h
  by_cases hc : Nat.Coprime b (level Q)
  · have hd : IsCoprime (b : ℤ) (level Q) := Nat.isCoprime_iff_coprime.2 hc
    rw [← chiCharLevel_intCast_eq_chi hQ hn hd hb rfl, chiCharLevel_intCast_eq_chi hQ hn hd hb' hz.symm]
  · -- a prime `p ∣ gcd(b, N)` divides `Δ`, `b` and `b'`, so both symbols vanish
    obtain ⟨p, hp, hpb, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
    have hpb' : p ∣ b' := (Nat.ModEq.dvd_iff h hpN).1 hpb
    have hpΔ : (p : ℤ) ∣ disc Q := by
      rw [disc]; exact Dvd.dvd.mul_left ((prime_dvd_level_iff hQn hp).1 hpN) _
    have hz0 : ∀ c : ℕ, p ∣ c → Odd c → chi Q c = 0 := by
      intro c hpc hco
      rw [chi, jacobiSym.eq_zero_iff]
      refine ⟨by rintro rfl; simp at hco, fun h1 => ?_⟩
      have : (p : ℤ) ∣ ((disc Q).gcd c : ℤ) := Int.dvd_coe_gcd hpΔ (Int.natCast_dvd_natCast.2 hpc)
      rw [h1] at this
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
    rw [hz0 b hpb hb, hz0 b' hpb' hb']

/-- **The $\Gamma_0(N)$ law with the canonical character** (equivalent restatement of `theta_gamma0_chi`): for $Q$ positive
definite, $n = 2k$, $N$ a level, $\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$, $N \mid c$, $\operatorname{Im} z > 0$:
$$\Theta_Q\Big(\frac{az+b}{cz+d}\Big) = \chi_Q(d \bmod N_Q)\,(cz+d)^k\,\Theta_Q(z),\qquad \chi_Q = \texttt{chiCharLevel}.$$ -/
@[kb "hanke2004" "§4, p. 364 (Θ_Q ∈ M_{n/2}(Γ₀(N), χ)) [unverified]"]
theorem theta_gamma0_chiCharLevel {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {a b c d : ℤ} (hdet : a * d - b * c = 1)
    (hNc : (N : ℤ) ∣ c) {z : ℂ} (hz : 0 < z.im) :
    theta Q ((a * z + b) / (c * z + d)) =
      (chiCharLevel hQ hn (d : ZMod (level Q)) : ℂ) * (c * z + d) ^ k * theta Q z := by
  obtain ⟨c0, hc0⟩ := hNc
  have hdN : IsCoprime d N := ⟨a, -b * c0, by rw [← hdet, hc0]; ring⟩
  rw [theta_gamma0_chi hQ hn hN0 hN hdet ⟨c0, hc0⟩ hz, thetaChi_eq_chiCharLevel hQ hn hN0 hN hdN]

/-! ### Odd level: the Kronecker symbol at even arguments -/

/-- **The Kronecker symbol** $\left(\frac{a}{b}\right)$ for $b \ge 1$: writing $b = 2^e m$ with $m$ odd,
$\left(\frac{a}{b}\right) = \left(\frac{a}{2}\right)^e\left(\frac{a}{m}\right)$ with the Jacobi symbol $\left(\frac{a}{m}\right)$ and
$\left(\frac{a}{2}\right) = 0$ for even $a$, $= \chi_8(a)$ ($1$ if $a \equiv \pm 1$, $-1$ if $a \equiv \pm 3 \pmod 8$) for odd $a$.
(Mathlib has no Kronecker symbol. The value at $b = 0$ is a junk value $1$.) -/
def kroneckerSym (a : ℤ) (b : ℕ) : ℤ :=
  (if Even a then 0 else ZMod.χ₈ a) ^ b.factorization 2 * jacobiSym a (ordCompl[2] b)

/-- For odd $b$ the Kronecker symbol is the Jacobi symbol. -/
theorem kroneckerSym_of_odd (a : ℤ) {b : ℕ} (hb : Odd b) : kroneckerSym a b = jacobiSym a b := by
  have h0 : b.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => by rcases hb with ⟨m, rfl⟩; omega)
  rw [kroneckerSym, h0, pow_zero, one_mul, pow_zero, Nat.div_one]

/-- If $N_Q$ is odd then $\Delta$ is odd (every prime factor of $\Delta$ divides $N_Q$). -/
theorem disc_odd_of_level_odd {Q : IntQF n} (hQ : Q.PosDef) (hN : Odd (level Q)) : Odd (disc Q) := by
  rw [← Int.not_even_iff_odd]
  rintro he
  have h2 : ((2 : ℕ) : ℤ) ∣ Q.hessian.det := by
    have : (2 : ℤ) ∣ disc Q := even_iff_two_dvd.1 he
    rw [disc] at this
    rcases neg_one_pow_eq_or ℤ (n / 2) with h1 | h1 <;> rw [h1] at this <;> simpa using this
  have := (prime_dvd_level_iff hQ.nondegenerate Nat.prime_two).2 h2
  rcases hN with ⟨m, hm⟩; omega

/-- **$\chi_Q(2) = \chi_8(\Delta)$ for odd $N_Q$** (the Kronecker value $\left(\frac{\Delta}{2}\right)$). *Proof:* take the odd
$x = 2 + tN_Q|\Delta|$, $t \in \{1, 3\}$, with $x \equiv 1 \pmod 4$; then $\chi_Q(2) = \left(\frac{\Delta}{x}\right) = \left(\frac{|\Delta|}{x}\right)
= \left(\frac{x}{|\Delta|}\right) = \left(\frac{2}{|\Delta|}\right) = \chi_8(|\Delta|) = \chi_8(\Delta)$ (reciprocity, $x \equiv 2 \bmod |\Delta|$). -/
theorem chiCharLevel_two {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) (hN : Odd (level Q)) :
    chiCharLevel hQ hn (2 : ℤ) = ZMod.χ₈ (disc Q) := by
  have hΔo := disc_odd_of_level_odd hQ hN
  set Δ := disc Q with hΔ
  set m : ℕ := Δ.natAbs with hm
  have hmo : Odd m := by rw [hm]; exact Int.natAbs_odd.2 hΔo
  set L := level Q
  have hLm : Odd (L * m) := hN.mul hmo
  set t : ℕ := if (L * m) % 4 = 1 then 3 else 1 with ht
  set x : ℕ := 2 + t * (L * m) with hx
  have hx4 : x % 4 = 1 := by
    have : (L * m) % 4 = 1 ∨ (L * m) % 4 = 3 := by rcases hLm with ⟨r, hr⟩; omega
    rcases this with h | h <;> simp only [hx, ht, h, ite_true] <;> [skip; simp only [show (3:ℕ) ≠ 1 by decide,
      ite_false]] <;> omega
  have hxo : Odd x := Nat.odd_iff.2 (by omega)
  have hco : IsCoprime (2 : ℤ) L := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_two_left).2 hN
  have hxL : (x : ℤ) % L = (2 : ℤ) % L := by
    rw [hx]; push_cast
    rw [show (2 : ℤ) + t * (L * m) = 2 + (t * m) * L by ring, Int.add_mul_emod_self_right]
  rw [chiCharLevel_intCast_eq_chi hQ hn hco hxo hxL, chi, ← hΔ]
  -- `J(Δ | x) = J(m | x)` since `x ≡ 1 mod 4`
  have hJm : jacobiSym Δ x = jacobiSym m x := by
    rcases Int.natAbs_eq Δ with h | h
    · rw [← hm] at h; rw [h]
    · rw [← hm] at h
      rw [h, jacobiSym.neg _ hxo, ZMod.χ₄_nat_one_mod_four hx4, one_mul]
  have hmx : jacobiSym m x = jacobiSym x m := by
    have := jacobiSym.quadratic_reciprocity_one_mod_four' hmo hx4
    exact_mod_cast this
  have hx2 : jacobiSym x m = jacobiSym 2 m := by
    apply jacobiSym.mod_left'
    rw [hx]; push_cast
    rw [show (2 : ℤ) + t * (L * m) = 2 + (t * L) * m by ring, Int.add_mul_emod_self_right]
  rw [hJm, hmx, hx2, jacobiSym.at_two hmo]
  -- `χ₈ m = χ₈ Δ`
  rcases Int.natAbs_eq Δ with h | h
  · rw [← hm] at h; rw [h]; simp
  · rw [← hm] at h
    rw [h, neg_eq_neg_one_mul, Int.cast_mul, map_mul, Int.cast_neg, Int.cast_one,
      show ZMod.χ₈ (-1) = 1 from rfl, one_mul]
    simp

/-- At an odd natural $m$ (prime to $N_Q$ or not) the canonical character is $\chi_Q(m) = \left(\frac{\Delta}{m}\right)$. -/
theorem chiCharLevel_natCast_of_odd {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {m : ℕ}
    (hm : Odd m) : chiCharLevel hQ hn (m : ZMod (level Q)) = chi Q m := by
  have hQn := hQ.nondegenerate
  by_cases hc : Nat.Coprime m (level Q)
  · have hd : IsCoprime (m : ℤ) (level Q) := Nat.isCoprime_iff_coprime.2 hc
    rw [← chiCharLevel_intCast_eq_chi hQ hn hd hm rfl, Int.cast_natCast]
  · obtain ⟨p, hp, hpm, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
    have hnu : ¬ IsUnit (m : ZMod (level Q)) := by
      rw [ZMod.isUnit_iff_coprime]; exact hc
    rw [MulChar.map_nonunit _ hnu, chi, eq_comm, jacobiSym.eq_zero_iff]
    have hpΔ : (p : ℤ) ∣ disc Q := by
      rw [disc]; exact Dvd.dvd.mul_left ((prime_dvd_level_iff hQn hp).1 hpN) _
    refine ⟨by rintro rfl; simp at hm, fun h1 => ?_⟩
    have : (p : ℤ) ∣ ((disc Q).gcd m : ℤ) := Int.dvd_coe_gcd hpΔ (Int.natCast_dvd_natCast.2 hpm)
    rw [h1] at this
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

/-- **For odd level the canonical character is the Kronecker symbol**: if $N_Q$ is odd, then for every
$d \ge 1$, $\chi_Q(d \bmod N_Q) = \left(\frac{\Delta}{d}\right)$ (`kroneckerSym`), including even $d$, where
$\left(\frac{\Delta}{2}\right) = \chi_8(\Delta)$ (`chiCharLevel_two`). -/
@[kb "hanke2004" "p. 357 (χ(d) = (Δ/d) Kronecker symbol, odd N) [unverified]"]
theorem chiCharLevel_natCast_eq_kroneckerSym {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k)
    (hN : Odd (level Q)) {d : ℕ} (hd : 0 < d) :
    chiCharLevel hQ hn (d : ZMod (level Q)) = kroneckerSym (disc Q) d := by
  have hodd : Odd (ordCompl[2] d) := Nat.coprime_two_left.1 (Nat.coprime_ordCompl Nat.prime_two hd.ne')
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self d 2]
  have h2 := chiCharLevel_two hQ hn hN
  rw [Int.cast_ofNat] at h2
  rw [Nat.cast_mul, map_mul, Nat.cast_pow, map_pow, Nat.cast_ofNat, h2,
    chiCharLevel_natCast_of_odd hQ hn hodd, kroneckerSym, chi]
  simp [Int.not_even_iff_odd.2 (disc_odd_of_level_odd hQ hN)]

end QuadFormsKB.Siegel
