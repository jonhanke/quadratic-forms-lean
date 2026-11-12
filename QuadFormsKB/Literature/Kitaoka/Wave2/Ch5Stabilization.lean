/-
# Kitaoka 1993, §5.6: stabilization of $\#A_{p^r}(T, S)$ (Lemma 5.6.1) and the local density as a stable value

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, Lemma 5.6.1, pp. 94–95, Lemma 5.6.2, p. 95,
Proposition 5.6.1 (i), (iii), p. 99, Theorem 5.6.4 (a), p. 115 (printed pages).

**Setting** (as in `Ch5Densities.lean`). $p$ is a prime, $R = \mathbb Z_p$, $S$ is an integral symmetric
$n \times n$ matrix (the Gram matrix of $N$), $T$ an integral symmetric $m \times m$ matrix (the Gram matrix of $M$),
$E_m = \{B = B^{\mathsf T} \in M_m(R) \mid \text{all diagonal entries of } B \text{ lie in } 2R\}$ and
$A_{p^r}(T, S) = \{X \in M_{n,m}(R/p^rR) \mid S[X] \equiv T \bmod p^r E_m\}$, counted by `countA p r S T`.

**Defines**
* `ModE p k D`: $D \in p^k E_m$, written $D = p^k(F + F^{\mathsf T})$ for some $F \in M_m(R)$; for symmetric $D$
  this is the entrywise condition of `countA` (`modE_iff_dvd`);
* `normA p S T r` $= (p^r)^{m(m+1)/2 - mn}\#A_{p^r}(T, S)$, the sequence whose limit is `betaP p S T`.

**Proves**
* `lemma561` (Lemma 5.6.1, case $e = 0$): if $p^hT^{-1} \in E_m$ and $r \ge h + 1$ then
  $(p^{r+1})^{m(m+1)/2-mn}\#A_{p^{r+1}}(T, S) = (p^r)^{m(m+1)/2-mn}\#A_{p^r}(T, S)$;
* `betaP_eq` (Proposition 5.6.1 (i), case $e = 0$): $\beta_p(M, N) = (p^r)^{m(m+1)/2-mn}\#A_{p^r}(T, S)$ for
  $r \ge h + 1$; in particular the limit defining $\beta_p$ exists (`tendsto_normA`) for every regular $T$;
* `countA_scale` (Lemma 5.6.2, case $e = 0$): $\#A_{p^{r+a}}(p^aT, p^aS) = p^{anm}\#A_{p^r}(T, S)$ for $r \ge 1$;
* `betaP_scale` (Proposition 5.6.1 (iii)): $\beta_p(M(p^a), N(p^a)) = p^{am(m+1)/2}\beta_p(M, N)$;
* `theorem564a` (Theorem 5.6.4 (a)): Kitaoka's statement `Theorem564a`.

*Proof of Lemma 5.6.1 (Kitaoka's argument).* The matrices $X \bmod p^{r+1}$ with $S[X] \equiv T \bmod p^rE_m$ number
$p^{nm}\#A_{p^r}(T, S)$ (the condition depends on $X \bmod p^r$). They split according to the class of
$p^{-r}(S[X] - T)$ in $E_m/pE_m$, which has $p^{m(m+1)/2}$ elements, represented by $E_c$ for
$c : \mathrm{Sym}^2(\{0, \dots, m-1\}) \to \{0, \dots, p-1\}$. For each class, $T_c = T + p^rE_c$ is $T[U]$ modulo
$p^{r+1}E_m$ for $U = 1 + p^{r-h}(p^hT^{-1})F_c$ ($E_c = F_c + F_c^{\mathsf T}$), and $X \mapsto XU^{-1}$ maps the
class of $c$ bijectively onto $A_{p^{r+1}}(T, S)$. Kitaoka quotes Corollary 5.4.4 (an exact $U$ with $T_c = T[U]$);
the counting only needs $T[U] \equiv T_c \bmod p^{r+1}E_m$, which is the one-step computation `exists_hensel`.
For the same reason the bound $r > h + \max(e, 1)$ of the book relaxes to $r \ge h + 1$ here, and $S$ need only be
symmetric.

Only the case $e = 0$ (no congruence condition $X \equiv G \bmod p^e$) is treated: that is the case used for
$\beta_p(M, N)$, which is what `betaP` defines.
-/
import QuadFormsKB.Literature.Kitaoka.Ch5Densities
import Mathlib.Data.Sym.Card
import Mathlib.NumberTheory.Padics.RingHoms

open Matrix Filter

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {m n : ℕ}

/-! ### The set $p^k E_m$ -/

/-- **$D \in p^kE_m$** (Kitaoka 1993, §5.6, p. 94): $D = p^k(F + F^{\mathsf T})$ for some $F \in M_m(\mathbb Z_p)$, i.e.
$D$ is $p^k$ times a symmetric matrix with even diagonal. -/
def ModE (p : ℕ) [Fact p.Prime] (k : ℕ) (D : Matrix (Fin m) (Fin m) ℤ_[p]) : Prop :=
  ∃ F : Matrix (Fin m) (Fin m) ℤ_[p], D = (p : ℤ_[p]) ^ k • (F + Fᵀ)

namespace ModE

variable {k l : ℕ} {D D' : Matrix (Fin m) (Fin m) ℤ_[p]}

theorem zero : ModE p k (0 : Matrix (Fin m) (Fin m) ℤ_[p]) := ⟨0, by simp⟩

theorem add (h : ModE p k D) (h' : ModE p k D') : ModE p k (D + D') := by
  obtain ⟨F, rfl⟩ := h; obtain ⟨F', rfl⟩ := h'
  exact ⟨F + F', by rw [transpose_add, ← smul_add]; abel_nf⟩

theorem neg (h : ModE p k D) : ModE p k (-D) := by
  obtain ⟨F, rfl⟩ := h
  exact ⟨-F, by rw [transpose_neg, ← neg_add, smul_neg]⟩

theorem sub (h : ModE p k D) (h' : ModE p k D') : ModE p k (D - D') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem conj (h : ModE p k D) {j : ℕ} (V : Matrix (Fin m) (Fin j) ℤ_[p]) : ModE p k (Vᵀ * D * V) := by
  obtain ⟨F, rfl⟩ := h
  refine ⟨Vᵀ * F * V, ?_⟩
  simp only [transpose_mul, transpose_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]

/-- $p^j \cdot (p^kE) \subseteq p^{k+j}E$. -/
theorem smul_pow (h : ModE p k D) (j : ℕ) : ModE p (k + j) ((p : ℤ_[p]) ^ j • D) := by
  obtain ⟨F, rfl⟩ := h
  exact ⟨F, by rw [smul_smul, pow_add, mul_comm]⟩

theorem mono (h : ModE p l D) (hkl : k ≤ l) : ModE p k D := by
  obtain ⟨F, rfl⟩ := h
  refine ⟨(p : ℤ_[p]) ^ (l - k) • F, ?_⟩
  rw [transpose_smul, ← smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hkl]

/-- Cancelling a power of $p$: $p^jD \in p^{k+j}E \Rightarrow D \in p^kE$. -/
theorem of_smul_pow {j : ℕ} (h : ModE p (k + j) ((p : ℤ_[p]) ^ j • D)) : ModE p k D := by
  obtain ⟨F, hF⟩ := h
  refine ⟨F, ?_⟩
  have hp0 : ((p : ℤ_[p]) ^ j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  apply smul_right_injective (Matrix (Fin m) (Fin m) ℤ_[p]) hp0
  simp only [hF, smul_smul, pow_add]
  ring_nf

end ModE

/-- A symmetric matrix $M$ has $pM \in E_m$: for $p = 2$, $2M = M + M^{\mathsf T}$; for odd $p$, $2$ is a unit of
$\mathbb Z_p$ and $pM = F + F^{\mathsf T}$ with $F = \frac p2 M$. -/
theorem modE_p_smul {M : Matrix (Fin m) (Fin m) ℤ_[p]} (hM : Mᵀ = M) : ModE p 0 ((p : ℤ_[p]) • M) := by
  by_cases h2 : p = 2
  · subst h2
    exact ⟨M, by rw [hM, pow_zero, one_smul, Nat.cast_ofNat, two_smul]⟩
  · have hu : IsUnit (2 : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      have : ‖((2 : ℕ) : ℤ_[p])‖ = 1 := by
        rw [PadicInt.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes hp.out Nat.prime_two).mpr h2
      exact_mod_cast this
    obtain ⟨u, hu⟩ := hu
    refine ⟨((↑u⁻¹ : ℤ_[p]) * p) • M, ?_⟩
    rw [transpose_smul, hM, pow_zero, one_smul, ← two_smul ℤ_[p], smul_smul, ← mul_assoc, ← hu,
      Units.mul_inv, one_mul]

/-- $p^{k+1}M \in p^kE_m$ for symmetric $M$. -/
theorem modE_pow_succ_smul {M : Matrix (Fin m) (Fin m) ℤ_[p]} (hM : Mᵀ = M) (k : ℕ) :
    ModE p k ((p : ℤ_[p]) ^ (k + 1) • M) := by
  have := (modE_p_smul hM).smul_pow k
  rw [zero_add, smul_smul, ← pow_succ] at this
  exact this

/-- **For symmetric $D$, $D \in p^kE_m$ is the entrywise condition of `countA`**: $p^k \mid D_{ij}$ for $i \ne j$ and
$2p^k \mid D_{ii}$. -/
theorem modE_iff_dvd {k : ℕ} {D : Matrix (Fin m) (Fin m) ℤ_[p]} (hD : Dᵀ = D) :
    ModE p k D ↔ ∀ i j, ((p : ℤ_[p]) ^ k * if i = j then 2 else 1) ∣ D i j := by
  constructor
  · rintro ⟨F, rfl⟩ i j
    by_cases hij : i = j
    · subst hij
      exact ⟨F i i, by simp; ring⟩
    · exact ⟨(F + Fᵀ) i j, by simp [hij]⟩
  · intro h
    choose w hw using h
    refine ⟨Matrix.of fun i j => if i < j then w i j else if i = j then w i i else 0, ?_⟩
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.add_apply, transpose_apply, of_apply, smul_eq_mul]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [hw i j]; simp [hij, hij.ne, hij.ne', not_lt.mpr hij.le]
    · rw [hw i i]; simp; ring
    · have hs : D i j = D j i := by rw [← transpose_apply D j i, hD]
      rw [hs, hw j i]; simp [hij, hij.ne, hij.ne', not_lt.mpr hij.le]

/-! ### Residues modulo $p^r$ -/

/-- The residue $0 \le a < p^r$ of $x \in \mathbb Z_p$ modulo $p^r$ (Mathlib's `PadicInt.appr`). -/
def red (p : ℕ) [Fact p.Prime] (r : ℕ) (x : ℤ_[p]) : Fin (p ^ r) := ⟨x.appr r, x.appr_lt r⟩

theorem red_spec (r : ℕ) (x : ℤ_[p]) : ∃ y, (((red p r x : ℕ) : ℤ_[p])) = x + (p : ℤ_[p]) ^ r * y := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec r x)
  exact ⟨-y, by simp only [red]; linear_combination hy⟩

theorem natCast_inj_of_dvd {r : ℕ} {a b : Fin (p ^ r)}
    (h : (p : ℤ_[p]) ^ r ∣ ((a : ℕ) : ℤ_[p]) - ((b : ℕ) : ℤ_[p])) : a = b := by
  have hk : ((a : ℕ) : ℤ_[p]) - ((b : ℕ) : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow r : ℤ_[p] →+* ZMod (p ^ r)) := by
    rw [PadicInt.ker_toZModPow]; exact Ideal.mem_span_singleton.mpr h
  rw [RingHom.mem_ker, map_sub, map_natCast, map_natCast, sub_eq_zero,
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at hk
  exact Fin.ext hk

theorem red_eq_iff {r : ℕ} {x y : ℤ_[p]} : red p r x = red p r y ↔ (p : ℤ_[p]) ^ r ∣ x - y := by
  obtain ⟨a, ha⟩ := red_spec r x
  obtain ⟨b, hb⟩ := red_spec r y
  constructor
  · intro h
    rw [h] at ha
    exact ⟨b - a, by linear_combination hb - ha⟩
  · rintro ⟨c, hc⟩
    exact natCast_inj_of_dvd ⟨a - b + c, by linear_combination ha - hb + hc⟩

theorem red_natCast {r : ℕ} (a : Fin (p ^ r)) : red p r ((a : ℕ) : ℤ_[p]) = a := by
  apply natCast_inj_of_dvd
  obtain ⟨y, hy⟩ := red_spec r ((a : ℕ) : ℤ_[p])
  exact ⟨y, by rw [hy]; ring⟩

/-- **Congruence of matrices modulo $p^k$**: $X = X' + p^kY$ for an integral $Y$. -/
def MCong (p : ℕ) [Fact p.Prime] {a b : ℕ} (k : ℕ) (X X' : Matrix (Fin a) (Fin b) ℤ_[p]) : Prop :=
  ∃ Y : Matrix (Fin a) (Fin b) ℤ_[p], X = X' + (p : ℤ_[p]) ^ k • Y

theorem mcong_liftRes_red {a b k : ℕ} (X : Matrix (Fin a) (Fin b) ℤ_[p]) :
    MCong p k (liftRes p k (X.map (red p k))) X := by
  choose y hy using fun i j => red_spec (p := p) k (X i j)
  exact ⟨Matrix.of y, by refine Matrix.ext fun i j => ?_; simp [liftRes, hy]⟩

theorem red_map_eq_of_mcong {a b k : ℕ} {X X' : Matrix (Fin a) (Fin b) ℤ_[p]} (h : MCong p k X X') :
    X.map (red p k) = X'.map (red p k) := by
  obtain ⟨Y, rfl⟩ := h
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hd : (p : ℤ_[p]) ^ k ∣ (X' i j + (p : ℤ_[p]) ^ k * Y i j) - X' i j := ⟨Y i j, by ring⟩
  exact congrArg Fin.val (red_eq_iff.mpr hd)

theorem red_map_liftRes {a b k : ℕ} (X : Matrix (Fin a) (Fin b) (Fin (p ^ k))) :
    (liftRes p k X).map (red p k) = X := by
  ext i j; simp [liftRes, red_natCast]

theorem MCong.mul_right {a b c k : ℕ} {X X' : Matrix (Fin a) (Fin b) ℤ_[p]} (h : MCong p k X X')
    (U : Matrix (Fin b) (Fin c) ℤ_[p]) : MCong p k (X * U) (X' * U) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y * U, by rw [Matrix.add_mul, Matrix.smul_mul]⟩

/-- **The Gram matrix modulo $p^kE$ depends only on $X \bmod p^k$** ($k \ge 1$, $S$ symmetric):
$S[X + p^kY] - S[X] = p^k(X^{\mathsf T}SY + Y^{\mathsf T}SX) + p^{2k}S[Y]$. -/
theorem modE_gram_of_mcong {S : Matrix (Fin n) (Fin n) ℤ_[p]} (hS : Sᵀ = S) {k : ℕ} (hk : 1 ≤ k)
    {X X' : Matrix (Fin n) (Fin m) ℤ_[p]} (h : MCong p k X X') : ModE p k (Xᵀ * S * X - X'ᵀ * S * X') := by
  obtain ⟨Y, rfl⟩ := h
  have e : (X' + (p : ℤ_[p]) ^ k • Y)ᵀ * S * (X' + (p : ℤ_[p]) ^ k • Y) - X'ᵀ * S * X' =
      (p : ℤ_[p]) ^ k • (Yᵀ * S * X' + (Yᵀ * S * X')ᵀ) + (p : ℤ_[p]) ^ (2 * k - 1 + 1) • (Yᵀ * S * Y) := by
    rw [Nat.sub_add_cancel (by omega), two_mul, pow_add]
    simp only [transpose_add, transpose_smul, transpose_mul, transpose_transpose, hS, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, Matrix.mul_assoc]
    abel
  rw [e]
  refine ModE.add ⟨_, rfl⟩ ?_
  have := modE_pow_succ_smul (p := p) (M := Yᵀ * S * Y)
    (by simp [transpose_mul, hS, Matrix.mul_assoc]) (2 * k - 1)
  exact this.mono (by omega)

/-! ### One Hensel step (in place of Kitaoka's Corollary 5.4.4) -/

/-- **One Hensel step.** Let $T$ be symmetric, $A = p^hT^{-1} \in E_m$ (i.e. $TA = p^h1$, $A \in E_m$) and
$r \ge h + 1$. For every $F$ there are mutually inverse $U, V \in M_m(\mathbb Z_p)$ with
$T[U] \equiv T + p^r(F + F^{\mathsf T}) \bmod p^{r+1}E_m$: take $U = 1 + p^{r-h}AF$, so that
$T[U] = T + p^r(F + F^{\mathsf T}) + p^{2r-h}F^{\mathsf T}AF$. -/
theorem exists_hensel {T A : Matrix (Fin m) (Fin m) ℤ_[p]} (hT : Tᵀ = T) {h : ℕ}
    (hA : T * A = (p : ℤ_[p]) ^ h • 1) (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r)
    (F : Matrix (Fin m) (Fin m) ℤ_[p]) :
    ∃ U V : Matrix (Fin m) (Fin m) ℤ_[p], U * V = 1 ∧ V * U = 1 ∧
      ModE p (r + 1) (Uᵀ * T * U - (T + (p : ℤ_[p]) ^ r • (F + Fᵀ))) := by
  obtain ⟨G, hG⟩ := hAE
  rw [pow_zero, one_smul] at hG
  have hAs : Aᵀ = A := by rw [hG]; simp [add_comm]
  have hAT : A * T = (p : ℤ_[p]) ^ h • 1 := by
    have := congrArg transpose hA
    rwa [transpose_mul, hT, hAs, transpose_smul, transpose_one] at this
  have hTA' : ∀ X : Matrix (Fin m) (Fin m) ℤ_[p], T * (A * X) = (p : ℤ_[p]) ^ h • X := fun X => by
    rw [← Matrix.mul_assoc, hA, Matrix.smul_mul, Matrix.one_mul]
  obtain ⟨k, rfl⟩ : ∃ k, r = h + 1 + k := ⟨r - (h + 1), by omega⟩
  set U : Matrix (Fin m) (Fin m) ℤ_[p] := 1 + (p : ℤ_[p]) ^ (k + 1) • (A * F) with hU
  have hdet : IsUnit U.det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det]
    have : (PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix U = 1 := by
      ext i j
      simp [U, Matrix.one_apply, apply_ite]
    rw [this, det_one]
    exact one_ne_zero
  refine ⟨U, U⁻¹, mul_nonsing_inv _ hdet, nonsing_inv_mul _ hdet, ?_⟩
  refine ⟨(p : ℤ_[p]) ^ k • (Fᵀ * (G * F)), ?_⟩
  have hTU : Uᵀ * T * U = T + (p : ℤ_[p]) ^ (h + 1 + k) • (F + Fᵀ) +
      (p : ℤ_[p]) ^ (h + 1 + k + 1) • ((p : ℤ_[p]) ^ k • (Fᵀ * (A * F))) := by
    have e1 : Uᵀ = 1 + (p : ℤ_[p]) ^ (k + 1) • (Fᵀ * A) := by
      simp [U, transpose_mul, hAs]
    rw [e1]
    simp only [U, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, hTA']
    rw [hAT]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul]
    module
  rw [hTU, hG]
  simp only [transpose_mul, transpose_transpose, transpose_smul, transpose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, smul_add]
  module

/-- **The inverse of the regular matrix $T$ up to a power of $p$** (Kitaoka's integer $h$ with $p^hT^{-1} \in E_m$,
p. 94): for symmetric $T$ with $\det T \ne 0$ there are $h$ and $A \in E_m$ with $TA = p^h1$. Take
$\det T = up^v$ ($u$ a unit) and $A = pu^{-1}\operatorname{adj}T$, $h = v + 1$. -/
theorem exists_h {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hT : Tᵀ = T) (hdet : T.det ≠ 0) :
    ∃ (h : ℕ) (A : Matrix (Fin m) (Fin m) ℤ_[p]), T * A = (p : ℤ_[p]) ^ h • 1 ∧ ModE p 0 A := by
  obtain ⟨v, u, hu⟩ : ∃ (v : ℕ) (u : ℤ_[p]ˣ), T.det = u * (p : ℤ_[p]) ^ v :=
    ⟨_, _, PadicInt.unitCoeff_spec hdet⟩
  refine ⟨v + 1, (p : ℤ_[p]) • ((↑u⁻¹ : ℤ_[p]) • adjugate T), ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_smul, mul_adjugate, hu, smul_smul, smul_smul]
    congr 1
    calc (p : ℤ_[p]) * (↑u⁻¹ : ℤ_[p]) * (↑u * (p : ℤ_[p]) ^ v)
        = (↑u⁻¹ * ↑u : ℤ_[p]) * ((p : ℤ_[p]) ^ v * p) := by ring
      _ = _ := by rw [Units.inv_mul, one_mul, pow_succ]
  · apply modE_p_smul
    rw [transpose_smul, adjugate_transpose, hT]

/-! ### Counting -/

/-- The condition of `countA` in the form $S[X] - T \in p^rE_m$, for residues modulo $p^k$. -/
abbrev GoodA (p : ℕ) [Fact p.Prime] (k r : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p])
    (T : Matrix (Fin m) (Fin m) ℤ_[p]) (X : Matrix (Fin n) (Fin m) (Fin (p ^ k))) : Prop :=
  ModE p r ((liftRes p k X)ᵀ * S * liftRes p k X - T)

theorem countA_eq_card {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (r : ℕ) : countA p r S T = Nat.card {X // GoodA p r r S T X} := by
  unfold countA
  refine Nat.card_congr (Equiv.subtypeEquivRight fun X => (modE_iff_dvd ?_).symm)
  simp [transpose_sub, transpose_mul, hS, hT, Matrix.mul_assoc]

/-- Splitting a residue modulo $p^{r+a}$ into its residue modulo $p^r$ and the next $a$ digits:
$x = b + p^rc$. -/
def splitE (p r a : ℕ) : Fin (p ^ (r + a)) ≃ Fin (p ^ r) × Fin (p ^ a) :=
  (finCongr (by ring : p ^ (r + a) = p ^ a * p ^ r)).trans (finProdFinEquiv.symm.trans (Equiv.prodComm _ _))

theorem splitE_val (p r a : ℕ) (x : Fin (p ^ (r + a))) :
    (x : ℕ) = ((splitE p r a x).1 : ℕ) + p ^ r * ((splitE p r a x).2 : ℕ) := by
  have := congrArg Fin.val
    (finProdFinEquiv.apply_symm_apply (finCongr (by ring : p ^ (r + a) = p ^ a * p ^ r) x))
  simp only [finProdFinEquiv_apply_val, finCongr_apply, Fin.val_cast] at this
  simp only [splitE, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, finCongr_apply]
  omega

/-- Matrices modulo $p^{r+a}$ as pairs (matrix modulo $p^r$, matrix of the next $a$ digits). -/
def splitM (p r a : ℕ) :
    Matrix (Fin n) (Fin m) (Fin (p ^ (r + a))) ≃
      Matrix (Fin n) (Fin m) (Fin (p ^ r)) × Matrix (Fin n) (Fin m) (Fin (p ^ a)) where
  toFun X := (X.map fun x => (splitE p r a x).1, X.map fun x => (splitE p r a x).2)
  invFun Y := Matrix.of fun i j => (splitE p r a).symm (Y.1 i j, Y.2 i j)
  left_inv X := by ext i j; simp
  right_inv Y := by ext i j <;> simp

theorem mcong_splitM (r a : ℕ) (X : Matrix (Fin n) (Fin m) (Fin (p ^ (r + a)))) :
    MCong p r (liftRes p (r + a) X) (liftRes p r (splitM p r a X).1) := by
  refine ⟨liftRes p a (splitM p r a X).2, ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [liftRes, splitM, Equiv.coe_fn_mk, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [splitE_val p r a (X i j)]
  push_cast
  ring

theorem modE_gram_iff_of_mcong {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]}
    (hS : Sᵀ = S) {r : ℕ} (hr : 1 ≤ r) {X X' : Matrix (Fin n) (Fin m) ℤ_[p]} (h : MCong p r X X') :
    ModE p r (Xᵀ * S * X - T) ↔ ModE p r (X'ᵀ * S * X' - T) := by
  have hd := modE_gram_of_mcong hS hr h
  constructor
  · intro hX
    have := hX.sub hd
    rwa [sub_sub_sub_cancel_left] at this
  · intro hX
    have := hX.add hd
    rwa [sub_add_sub_cancel'] at this

/-- **Lifting** (Kitaoka, proof of Lemma 5.6.1, p. 94): for $r \ge 1$ the matrices $X \bmod p^{r+a}$ with
$S[X] \equiv T \bmod p^rE_m$ number $p^{anm}\#A_{p^r}(T, S)$. -/
theorem card_lift {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    {r : ℕ} (hr : 1 ≤ r) (a : ℕ) :
    Nat.card {X // GoodA p (r + a) r S T X} = Nat.card {X // GoodA p r r S T X} * (p ^ a) ^ (n * m) := by
  have hX : ∀ X, GoodA p (r + a) r S T X ↔ GoodA p r r S T (splitM p r a X).1 := fun X =>
    modE_gram_iff_of_mcong hS hr (mcong_splitM r a X)
  have e1 : {X // GoodA p (r + a) r S T X} ≃ {Y : Matrix (Fin n) (Fin m) (Fin (p ^ r)) ×
      Matrix (Fin n) (Fin m) (Fin (p ^ a)) // GoodA p r r S T Y.1} :=
    Equiv.subtypeEquiv (splitM p r a) hX
  have e2 : {Y : Matrix (Fin n) (Fin m) (Fin (p ^ r)) × Matrix (Fin n) (Fin m) (Fin (p ^ a)) //
      GoodA p r r S T Y.1} ≃ {X // GoodA p r r S T X} × Matrix (Fin n) (Fin m) (Fin (p ^ a)) :=
    Equiv.prodSubtypeFstEquivSubtypeProd
  have hc : Nat.card (Matrix (Fin n) (Fin m) (Fin (p ^ a))) = (p ^ a) ^ (n * m) := by
    rw [show Nat.card (Matrix (Fin n) (Fin m) (Fin (p ^ a))) = Nat.card (Fin n → Fin m → Fin (p ^ a)) from rfl,
      Nat.card_fun, Nat.card_fun]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]; ring
  rw [Nat.card_congr (e1.trans e2), Nat.card_prod, hc]

/-! ### The classes of $E_m/pE_m$ -/

/-- **Representatives of $E_m/pE_m$**: for $c : \mathrm{Sym}^2(\{0, \dots, m-1\}) \to \{0, \dots, p-1\}$, the upper
triangular $F_c$ with $(F_c)_{ij} = c\{i, j\}$ for $i \le j$; then $E_c = F_c + F_c^{\mathsf T}$ has off-diagonal
entries $c\{i, j\}$ and diagonal entries $2c\{i, i\}$. -/
def classF (c : Sym2 (Fin m) → Fin (p ^ 1)) : Matrix (Fin m) (Fin m) ℤ_[p] :=
  Matrix.of fun i j => if i ≤ j then (((c s(i, j)) : ℕ) : ℤ_[p]) else 0

theorem classE_apply (c : Sym2 (Fin m) → Fin (p ^ 1)) (i j : Fin m) :
    (classF c + (classF c)ᵀ) i j =
      if i = j then 2 * (((c s(i, i)) : ℕ) : ℤ_[p]) else (((c s(i, j)) : ℕ) : ℤ_[p]) := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [classF, h.le, not_le.mpr h, h.ne]
  · simp [classF, two_mul]
  · simp [classF, h.le, not_le.mpr h, h.ne', Sym2.eq_swap]

theorem classE_symm (c : Sym2 (Fin m) → Fin (p ^ 1)) : (classF c + (classF c)ᵀ)ᵀ = classF c + (classF c)ᵀ := by
  rw [transpose_add, transpose_transpose, add_comm]

/-- Every $D \in p^rE_m$ lies in $p^rE_c + p^{r+1}E_m$ for some class $c$. -/
theorem exists_class {r : ℕ} {D : Matrix (Fin m) (Fin m) ℤ_[p]} (hD : ModE p r D) :
    ∃ c : Sym2 (Fin m) → Fin (p ^ 1),
      ModE p (r + 1) (D - (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)) := by
  obtain ⟨F, rfl⟩ := hD
  let g : Fin m → Fin m → Fin (p ^ 1) := fun i j => red p 1 (if i = j then F i i else F i j + F j i)
  have hg : ∀ i j, g i j = g j i := by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp only [g, h, Ne.symm h, if_false, add_comm]
  refine ⟨Sym2.lift ⟨g, hg⟩, ?_⟩
  rw [← smul_sub]
  have hΔ : ModE p 1 (F + Fᵀ - (classF (Sym2.lift ⟨g, hg⟩) + (classF (Sym2.lift ⟨g, hg⟩))ᵀ)) := by
    rw [modE_iff_dvd (by rw [transpose_sub, classE_symm, transpose_add, transpose_transpose, add_comm Fᵀ])]
    intro i j
    rw [Matrix.sub_apply, classE_apply]
    simp only [Matrix.add_apply, transpose_apply, Sym2.lift_mk]
    by_cases h : i = j
    · subst h
      obtain ⟨y, hy⟩ := red_spec (p := p) 1 (F i i)
      simp only [if_true, g, hy]
      exact ⟨-y, by ring⟩
    · obtain ⟨y, hy⟩ := red_spec (p := p) 1 (F i j + F j i)
      simp only [h, if_false, g, hy]
      exact ⟨-y, by ring⟩
  have := hΔ.smul_pow r
  rwa [add_comm] at this

/-- The class is unique: $D - p^rE_c, D - p^rE_{c'} \in p^{r+1}E_m$ imply $c = c'$. -/
theorem class_unique {r : ℕ} {D : Matrix (Fin m) (Fin m) ℤ_[p]} {c c' : Sym2 (Fin m) → Fin (p ^ 1)}
    (h : ModE p (r + 1) (D - (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)))
    (h' : ModE p (r + 1) (D - (p : ℤ_[p]) ^ r • (classF c' + (classF c')ᵀ))) : c = c' := by
  have h2 := h'.sub h
  rw [sub_sub_sub_cancel_left, ← smul_sub, add_comm] at h2
  have h3 := ModE.of_smul_pow h2
  rw [modE_iff_dvd (by rw [transpose_sub, classE_symm, classE_symm])] at h3
  funext s
  induction s using Sym2.ind with
  | _ i j =>
    have hij := h3 i j
    rw [Matrix.sub_apply, classE_apply, classE_apply] at hij
    apply natCast_inj_of_dvd
    rw [pow_one]
    by_cases e : i = j
    · subst e
      simp only [if_true] at hij
      obtain ⟨w, hw⟩ := hij
      refine ⟨w, mul_left_cancel₀ (two_ne_zero : (2 : ℤ_[p]) ≠ 0) ?_⟩
      linear_combination hw
    · simpa [e] using hij

/-- **The classes are equinumerous** (Kitaoka, proof of Lemma 5.6.1, p. 95): for $r \ge h + 1$ and every class $c$,
$X \mapsto XU^{-1}$ maps $\{X \bmod p^{r+1} \mid S[X] \equiv T + p^rE_c \bmod p^{r+1}E_m\}$ bijectively onto
$A_{p^{r+1}}(T, S)$, where $T[U] \equiv T + p^rE_c$ (`exists_hensel`). -/
theorem card_class {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) (c : Sym2 (Fin m) → Fin (p ^ 1)) :
    Nat.card {X : Matrix (Fin n) (Fin m) (Fin (p ^ (r + 1))) //
      GoodA p (r + 1) (r + 1) S (T + (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)) X} =
    Nat.card {X // GoodA p (r + 1) (r + 1) S T X} := by
  obtain ⟨U, V, hUV, hVU, hU⟩ := exists_hensel hT hA hAE hr (classF c)
  set Tc := T + (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)
  have h1 : 1 ≤ r + 1 := by omega
  refine Nat.card_congr
    { toFun := fun X => ⟨(liftRes p (r + 1) X.1 * V).map (red p (r + 1)), ?_⟩
      invFun := fun Y => ⟨(liftRes p (r + 1) Y.1 * U).map (red p (r + 1)), ?_⟩
      left_inv := fun X => ?_
      right_inv := fun Y => ?_ }
  · rw [GoodA, modE_gram_iff_of_mcong hS h1 (mcong_liftRes_red _)]
    set L := liftRes p (r + 1) X.1
    have hI : Vᵀ * (Uᵀ * T * U) * V = T := by
      rw [show Vᵀ * (Uᵀ * T * U) * V = (U * V)ᵀ * T * (U * V) by
        simp only [transpose_mul, Matrix.mul_assoc], hUV, transpose_one, Matrix.one_mul, Matrix.mul_one]
    have key : (L * V)ᵀ * S * (L * V) - T = Vᵀ * (Lᵀ * S * L - Tc) * V - Vᵀ * (Uᵀ * T * U - Tc) * V := by
      calc (L * V)ᵀ * S * (L * V) - T = Vᵀ * (Lᵀ * S * L) * V - Vᵀ * (Uᵀ * T * U) * V := by
            rw [hI, transpose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [key]
    exact (X.2.conj V).sub (hU.conj V)
  · rw [GoodA, modE_gram_iff_of_mcong hS h1 (mcong_liftRes_red _)]
    set L := liftRes p (r + 1) Y.1
    have key : (L * U)ᵀ * S * (L * U) - Tc = Uᵀ * (Lᵀ * S * L - T) * U + (Uᵀ * T * U - Tc) := by
      rw [transpose_mul]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      abel
    rw [key]
    exact (Y.2.conj U).add hU
  · apply Subtype.ext
    have hm : MCong p (r + 1) (liftRes p (r + 1) ((liftRes p (r + 1) X.1 * V).map (red p (r + 1))) * U)
        (liftRes p (r + 1) X.1) := by
      have := (mcong_liftRes_red (k := r + 1) (liftRes p (r + 1) X.1 * V)).mul_right U
      rwa [Matrix.mul_assoc, hVU, Matrix.mul_one] at this
    exact (red_map_eq_of_mcong hm).trans (red_map_liftRes _)
  · apply Subtype.ext
    have hm : MCong p (r + 1) (liftRes p (r + 1) ((liftRes p (r + 1) Y.1 * U).map (red p (r + 1))) * V)
        (liftRes p (r + 1) Y.1) := by
      have := (mcong_liftRes_red (k := r + 1) (liftRes p (r + 1) Y.1 * U)).mul_right V
      rwa [Matrix.mul_assoc, hUV, Matrix.mul_one] at this
    exact (red_map_eq_of_mcong hm).trans (red_map_liftRes _)

theorem card_sym2_fun : Nat.card (Sym2 (Fin m) → Fin (p ^ 1)) = p ^ (m * (m + 1) / 2) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Sym2.card, Fintype.card_fin, Fintype.card_fin, pow_one,
    Nat.choose_two_right, Nat.add_sub_cancel, mul_comm (m + 1)]

/-- **The counting identity of Lemma 5.6.1**: $p^{nm}\#A_{p^r}(T, S) = p^{m(m+1)/2}\#A_{p^{r+1}}(T, S)$ for
$r \ge h + 1$. -/
theorem countA_succ {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) :
    countA p r S T * p ^ (n * m) = p ^ (m * (m + 1) / 2) * countA p (r + 1) S T := by
  classical
  rw [countA_eq_card hS hT, countA_eq_card hS hT]
  have h1 := card_lift (p := p) (T := T) hS (r := r) (by omega) 1
  rw [pow_one] at h1
  rw [← h1]
  have : Nonempty (Fin (p ^ 1)) := ⟨⟨0, pow_pos hp.out.pos 1⟩⟩
  let Fib : (Sym2 (Fin m) → Fin (p ^ 1)) → Matrix (Fin n) (Fin m) (Fin (p ^ (r + 1))) → Prop := fun c X =>
    GoodA p (r + 1) (r + 1) S (T + (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)) X
  let κ : Matrix (Fin n) (Fin m) (Fin (p ^ (r + 1))) → Sym2 (Fin m) → Fin (p ^ 1) := fun X =>
    Classical.epsilon fun c => Fib c X
  have hP : ∀ c X, Fib c X → GoodA p (r + 1) r S T X := by
    intro c X hX
    have := (ModE.mono hX (Nat.le_succ r)).add (⟨classF c, rfl⟩ : ModE p r ((p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)))
    convert this using 1
    abel
  have hfib : ∀ c X, (GoodA p (r + 1) r S T X ∧ κ X = c) ↔ Fib c X := by
    intro c X
    constructor
    · rintro ⟨hX, rfl⟩
      obtain ⟨c, hc⟩ := exists_class hX
      exact Classical.epsilon_spec (p := fun c => Fib c X) ⟨c, by
        simp only [Fib, GoodA]; convert hc using 1; abel⟩
    · intro hX
      refine ⟨hP c X hX, ?_⟩
      have hκ : Fib (κ X) X := Classical.epsilon_spec (p := fun c => Fib c X) ⟨c, hX⟩
      exact class_unique (D := (liftRes p (r + 1) X)ᵀ * S * liftRes p (r + 1) X - T)
        (by simp only [Fib, GoodA] at hκ; convert hκ using 1; abel)
        (by simp only [Fib, GoodA] at hX; convert hX using 1; abel)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise (f := κ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  have hc : ∀ c, (Finset.univ.filter (GoodA p (r + 1) r S T) |>.filter fun X => κ X = c).card =
      Nat.card {X // GoodA p (r + 1) (r + 1) S T X} := by
    intro c
    rw [Finset.filter_filter, ← card_class hS hT hA hAE hr c, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfib c X
  rw [Finset.sum_congr rfl fun c _ => hc c, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, card_sym2_fun]

/-! ### Lemma 5.6.1 and Proposition 5.6.1 (i): the local density is a stable value -/

/-- The sequence $(p^r)^{m(m+1)/2 - mn}\#A_{p^r}(T, S)$ whose limit is $\beta_p(M, N)$. -/
def normA (p : ℕ) [Fact p.Prime] (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (r : ℕ) :
    ℝ :=
  ((p : ℝ) ^ r) ^ (((m * (m + 1) / 2 : ℕ) : ℤ) - (m : ℤ) * n) * (countA p r S T : ℝ)

theorem betaP_eq_limUnder (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) :
    betaP p S T = limUnder atTop (normA p S T) := rfl

theorem normA_eq (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (r : ℕ) :
    normA p S T r = (p : ℝ) ^ ((r : ℤ) * (((m * (m + 1) / 2 : ℕ) : ℤ) - (m : ℤ) * n)) * (countA p r S T : ℝ) := by
  rw [normA, ← zpow_natCast, ← _root_.zpow_mul]

/-- **Kitaoka 1993, Lemma 5.6.1** (p. 94), case $e = 0$: let $S$ ($n \times n$) and $T$ ($m \times m$) be integral
symmetric matrices over $\mathbb Z_p$ and $h \ge 0$ with $p^hT^{-1} \in E_m$, i.e. $TA = p^h1$ for some $A \in E_m$.
If $r \ge h + 1$ then
$$(p^{r+1})^{m(m+1)/2 - mn}\#A_{p^{r+1}}(T, S) = (p^r)^{m(m+1)/2 - mn}\#A_{p^r}(T, S).$$
Kitaoka assumes $r > h + \max(e, 1)$ and $S$ regular; neither is needed for $e = 0$ (see the module docstring). -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.1, p. 94"]
theorem lemma561 {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) : normA p S T (r + 1) = normA p S T r := by
  have key := countA_succ hS hT hA hAE hr
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set M := m * (m + 1) / 2
  have hc : (countA p (r + 1) S T : ℝ) = (p : ℝ) ^ ((n : ℤ) * m - M) * countA p r S T := by
    have hk : (countA p r S T : ℝ) * (p : ℝ) ^ (n * m) = (p : ℝ) ^ M * countA p (r + 1) S T := by
      exact_mod_cast key
    rw [zpow_sub₀ hpR, ← Nat.cast_mul, zpow_natCast, zpow_natCast]
    field_simp
    linarith
  rw [normA_eq, normA_eq, hc, ← mul_assoc, ← zpow_add₀ hpR]
  congr 2
  rw [Nat.cast_add_one]
  ring

/-- Kitaoka's integer $h$ gives stability from $h + 1$ on: $(p^r)^{m(m+1)/2-mn}\#A_{p^r}(T, S)$ is constant for
$r \ge h + 1$. -/
theorem normA_eq_of_le {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) : normA p S T r = normA p S T (h + 1) := by
  induction r, hr using Nat.le_induction with
  | base => rfl
  | succ r hr ih => rw [lemma561 hS hT hA hAE hr, ih]

/-- **Kitaoka 1993, Proposition 5.6.1 (i)** (p. 99), case $e = 0$: for integral symmetric $S$, $T$ and $h$ with
$p^hT^{-1} \in E_m$, $\beta_p(M, N) = (p^r)^{m(m+1)/2-mn}\#A_{p^r}(T, S)$ for every $r \ge h + 1$ (the book:
$r > h + \max(e, 1)$). -/
@[kb "kitaoka1993" "§5.6, Prop. 5.6.1 (i), p. 99"]
theorem betaP_eq {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) : betaP p S T = normA p S T r := by
  have ht : Tendsto (normA p S T) atTop (nhds (normA p S T (h + 1))) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨h + 1, fun r hr =>
      (normA_eq_of_le hS hT hA hAE hr).symm⟩)
  rw [betaP_eq_limUnder, ht.limUnder_eq, normA_eq_of_le hS hT hA hAE hr]

/-- **The limit defining $\beta_p(M, N)$ exists** for every integral symmetric $S$ and every integral symmetric
regular $T$ (Kitaoka, p. 98: "the following definition of the local density is well-defined"); the sequence is
eventually constant. -/
@[kb "kitaoka1993" "§5.6, p. 98 (β_p well-defined)"]
theorem tendsto_normA {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) : Tendsto (normA p S T) atTop (nhds (betaP p S T)) := by
  obtain ⟨h, A, hA, hAE⟩ := exists_h hT hdet
  rw [betaP_eq hS hT hA hAE le_rfl]
  exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨h + 1, fun r hr =>
    (normA_eq_of_le hS hT hA hAE hr).symm⟩)

/-! ### Lemma 5.6.2, Proposition 5.6.1 (iii) and Theorem 5.6.4 (a): scaling -/

/-- **Kitaoka 1993, Lemma 5.6.2** (p. 95), case $e = 0$: $\#A_{p^{r+a}}(p^aT, p^aS) = p^{ast}\#A_{p^r}(T, S)$ for
$r \ge 1$ (degrees $s = n$, $t = m$; the book: $r > h + \max(e, 1)$). -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.2, p. 95"]
theorem countA_scale {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {r : ℕ} (hr : 1 ≤ r) (a : ℕ) :
    countA p (r + a) ((p : ℤ_[p]) ^ a • S) ((p : ℤ_[p]) ^ a • T) = countA p r S T * (p ^ a) ^ (n * m) := by
  rw [countA_eq_card (by rw [transpose_smul, hS]) (by rw [transpose_smul, hT]), countA_eq_card hS hT,
    ← card_lift hS hr a]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun X => ?_)
  simp only [GoodA]
  rw [show (liftRes p (r + a) X)ᵀ * ((p : ℤ_[p]) ^ a • S) * liftRes p (r + a) X - (p : ℤ_[p]) ^ a • T =
      (p : ℤ_[p]) ^ a • ((liftRes p (r + a) X)ᵀ * S * liftRes p (r + a) X - T) by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]]
  exact ⟨ModE.of_smul_pow, fun h => h.smul_pow a⟩

/-- **Kitaoka 1993, Proposition 5.6.1 (iii)** (p. 99): $\beta_p(M(p^a), N(p^a)) = p^{am(m+1)/2}\beta_p(M, N)$ for
integral $S$, $T$ ($M(p^a)$, $N(p^a)$ have Gram matrices $p^aT$, $p^aS$), $T$ regular. -/
@[kb "kitaoka1993" "§5.6, Prop. 5.6.1 (iii), p. 99"]
theorem betaP_scale {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) (a : ℕ) :
    betaP p ((p : ℤ_[p]) ^ a • S) ((p : ℤ_[p]) ^ a • T) = (p : ℝ) ^ (a * (m * (m + 1) / 2)) * betaP p S T := by
  obtain ⟨h, A, hA, hAE⟩ := exists_h hT hdet
  have hA' : ((p : ℤ_[p]) ^ a • T) * A = (p : ℤ_[p]) ^ (h + a) • 1 := by
    rw [Matrix.smul_mul, hA, smul_smul, ← pow_add, add_comm a]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [betaP_eq (by rw [transpose_smul, hS]) (by rw [transpose_smul, hT]) hA' hAE (r := h + 1 + a) (by omega),
    betaP_eq hS hT hA hAE (le_refl (h + 1)), normA_eq, normA_eq, countA_scale hS hT (by omega)]
  set c : ℝ := (countA p (h + 1) S T : ℝ)
  set M : ℕ := m * (m + 1) / 2
  have e1 : (((countA p (h + 1) S T * (p ^ a) ^ (n * m) : ℕ)) : ℝ) =
      (p : ℝ) ^ (((a * (n * m) : ℕ)) : ℤ) * c := by
    rw [zpow_natCast, pow_mul]; push_cast; ring
  have key : ∀ x y : ℤ, (p : ℝ) ^ x * ((p : ℝ) ^ y * c) = (p : ℝ) ^ (x + y) * c := fun x y => by
    rw [zpow_add₀ hpR, mul_assoc]
  rw [e1, ← zpow_natCast (p : ℝ) (a * M), key, key]
  congr 2
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

/-- **Kitaoka 1993, Theorem 5.6.4 (a)** (p. 115), *proved*: $\beta_p(p^rM, p^rN) = p^{r(m+1)m}\beta_p(M, N)$ for
regular lattices ($p^rM$, $p^rN$ have Gram matrices $p^{2r}T$, $p^{2r}S$). This is Proposition 5.6.1 (iii) with
$a = 2r$; the hypotheses $m \le n$ and $\det S \ne 0$ of the statement are not needed. -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.4 (a), p. 115"]
theorem theorem564a : Theorem564a := by
  intro p _ m n r T S _ hT hS
  rw [betaP_scale hS.1 hT.1 hT.2 (2 * r)]
  congr 2
  have : 2 * (m * (m + 1) / 2) = m * (m + 1) := Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
  rw [mul_comm 2 r, mul_assoc, this]
  ring

end QuadFormsKB.Kitaoka.Density
