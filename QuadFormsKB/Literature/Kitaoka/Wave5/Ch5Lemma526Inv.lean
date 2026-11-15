/-
# Kitaoka 1993, Lemma 5.2.6: the invariants $dL$, $S(FL)$ and $Q(L)$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.2, Lemma 5.2.6, p. 77 (printed page).

**Book statement.** Let $p = 2$ and $L$ a binary unimodular lattice with $\mathfrak n(L) = (2)$. If $L$ is isotropic,
then $L \cong \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, $dL = -1$, $S(FL) = -1$ and $Q(L) = (2)$. If $L$ is
anisotropic, then $L \cong \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$, $dL = 3$, $S(FL) = 1$ and
$Q(L) = \{0\} \cup \{x \in R \mid \operatorname{ord}_2 x \equiv 1 \bmod 2\}$.

**Encoding.** As in `Ch5Lemma526.lean` (which proves the classification part, `Kitaoka.Padic.lemma526`): the lattice
is given by its Gram matrix $S = (B(v_i, v_j))$ over $R = \mathbb Z_2$ (symmetric, $\det S \in \mathbb Z_2^\times$,
even diagonal), and $L$ is isotropic when `gramQ S` has a nontrivial zero over $\mathbb Q_2$.
* $dL$ is $\det S$ modulo $(\mathbb Z_2^\times)^2$: "$dL = c$" is written $\det S = c\,u^2$ with $u \in \mathbb Z_2^\times$.
* $S(FL)$ is Kitaoka's Hasse invariant $\prod_{i \le j}(a_i, a_j)_2$ (`Kitaoka.Hasse.hasseK`) of an orthogonal basis
  of $FL$ with $Q$-values $a_0, a_1$. The statement is made for **every** orthogonal basis: for every invertible
  $P$ over $\mathbb Q_2$ and $a_0, a_1 \in \mathbb Q_2^\times$ with $Q_S(P(x, y)) = a_0x^2 + a_1y^2$.
* $Q(L) = \{Q(x) \mid x \in L\}$ is the set of values $S_{00}x^2 + 2S_{01}xy + S_{11}y^2$, $x, y \in \mathbb Z_2$
  (`gramQZ`); $\operatorname{ord}_2$ is `PadicInt.valuation`.

**Proves** (unconditional): `lemma526_isotropic`, `lemma526_anisotropic`.

**Proof.** By `lemma526` it suffices to treat the two normal forms; $\det$ changes by $(\det P)^2$, values over
$\mathbb Z_2$ are preserved by $P \in \mathrm{GL}_2(\mathbb Z_2)$, and $FL$ is isometric to
$\langle 1\rangle \perp \langle -1\rangle$ (resp. $\langle 2\rangle \perp \langle 6\rangle$), so by Theorem 3.5.2
(`Kitaoka.Theorem351.theorem352`) every orthogonal basis has the Hasse invariant of that one, computed by the dyadic
Hilbert symbol formula. For the values: $2xy$ takes exactly the values in $(2)$; $x^2 + xy + y^2$ is odd when $x$ or
$y$ is odd, so its nonzero values have even order, and every unit $u$ is a value ($x^2 + x + 1 - u$ has a root by
Hensel's lemma).
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch5Lemma526
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch3Theorem351
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Padic

/-- The value $Q(xv_0 + yv_1) = S_{00}x^2 + 2S_{01}xy + S_{11}y^2$ of the lattice with Gram matrix $S$ at a lattice
vector ($x, y \in \mathbb Z_2$). -/
def gramQZ (S : Matrix (Fin 2) (Fin 2) ℤ_[2]) (x y : ℤ_[2]) : ℤ_[2] :=
  S 0 0 * x ^ 2 + 2 * S 0 1 * x * y + S 1 1 * y ^ 2

/-- $S(FL)$ for every orthogonal basis: for every invertible $P$ over $\mathbb Q_2$ and $a_0, a_1 \ne 0$ with
$Q_S(P(x, y)) = a_0x^2 + a_1y^2$, Kitaoka's Hasse invariant $\prod_{i \le j}(a_i, a_j)_2$ equals `s`. -/
def HasseOfGram (S : Matrix (Fin 2) (Fin 2) ℤ_[2]) (s : ℤ) : Prop :=
  ∀ (a : Fin 2 → ℚ_[2]) (P : Matrix (Fin 2) (Fin 2) ℚ_[2]), (∀ i, a i ≠ 0) → IsUnit P.det →
    (∀ x y : ℚ_[2], gramQ S (P 0 0 * x + P 0 1 * y) (P 1 0 * x + P 1 1 * y) = a 0 * x ^ 2 + a 1 * y ^ 2) →
    Hasse.hasseK a = s

/-- Helper: a $2$-adic unit has valuation $0$. -/
theorem val_unit {u : ℤ_[2]} (hu : IsUnit u) : u.valuation = 0 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h := PadicInt.valuation_mul (p := 2) hu.ne_zero (right_ne_zero_of_mul_eq_one hv)
  rw [hv] at h
  simp at h
  omega

/-- Helper: $x^2 + xy + y^2$ is a unit if $x$ or $y$ is odd. -/
theorem isUnit_ani_of_odd (x y : ℤ_[2]) (h : ¬ ((∃ a, x = 2 * a) ∧ (∃ b, y = 2 * b))) :
    IsUnit (x ^ 2 + x * y + y ^ 2) := by
  rcases parity x with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;> rcases parity y with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact absurd ⟨⟨m, rfl⟩, ⟨k, rfl⟩⟩ h
  · have := isUnit_two_mul_add_one (2 * m ^ 2 + 2 * m * k + m + 2 * k ^ 2 + 2 * k)
    convert this using 1; ring
  · have := isUnit_two_mul_add_one (2 * m ^ 2 + 2 * m + 2 * m * k + k + 2 * k ^ 2)
    convert this using 1; ring
  · have := isUnit_two_mul_add_one (2 * m ^ 2 + 2 * m + 2 * m * k + m + k + 2 * k ^ 2 + 2 * k + 1)
    convert this using 1; ring

/-- Helper: $\operatorname{ord}_2 2 = 1$. -/
theorem val_two : (2 : ℤ_[2]).valuation = 1 := by simpa using PadicInt.valuation_p (p := 2)

/-- Helper: $\operatorname{ord}_2(2a) = 1 + \operatorname{ord}_2 a$ for $a \ne 0$. -/
theorem val_two_mul {a : ℤ_[2]} (h : a ≠ 0) : (2 * a).valuation = 1 + a.valuation := by
  rw [PadicInt.valuation_mul (p := 2) (by norm_num) h, val_two]

/-- Helper: the nonzero values of $x^2 + xy + y^2$ over $\mathbb Z_2$ have even valuation. -/
theorem val_ani_even : ∀ (N : ℕ) (x y : ℤ_[2]), x.valuation + y.valuation = N →
    x ^ 2 + x * y + y ^ 2 ≠ 0 → Even (x ^ 2 + x * y + y ^ 2).valuation := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x y hN hne
    by_cases h : (∃ a, x = 2 * a) ∧ (∃ b, y = 2 * b)
    · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
      have e : (2 * a) ^ 2 + 2 * a * (2 * b) + (2 * b) ^ 2 = 2 ^ 2 * (a ^ 2 + a * b + b ^ 2) := by ring
      have hm : a ^ 2 + a * b + b ^ 2 ≠ 0 := by
        intro h0; apply hne; rw [e, h0, mul_zero]
      have hab : a ≠ 0 ∨ b ≠ 0 := by
        by_contra hc
        rw [not_or, not_not, not_not] at hc
        apply hm; rw [hc.1, hc.2]; ring
      have hlt : a.valuation + b.valuation < N := by
        rw [← hN]
        by_cases ha : a = 0 <;> by_cases hb : b = 0
        · exact absurd ha (by simpa [hb] using hab)
        · rw [val_two_mul hb]; simp [ha]
        · rw [val_two_mul ha]; simp [hb]
        · rw [val_two_mul ha, val_two_mul hb]; omega
      have := ih _ hlt a b rfl hm
      rw [e, PadicInt.valuation_mul (by norm_num) hm, PadicInt.valuation_pow, val_two]
      obtain ⟨r, hr⟩ := this
      exact ⟨r + 1, by omega⟩
    · rw [val_unit (isUnit_ani_of_odd x y h)]; exact ⟨0, rfl⟩

/-- Helper: values of $\langle$ hyperbolic plane $\rangle$. -/
theorem gramQZ_hyp (x y : ℤ_[2]) : gramQZ !![0, 1; 1, 0] x y = 2 * (x * y) := by
  simp [gramQZ]; ring

/-- Helper: values of the anisotropic plane. -/
theorem gramQZ_ani (x y : ℤ_[2]) : gramQZ !![2, 1; 1, 2] x y = 2 * (x ^ 2 + x * y + y ^ 2) := by
  simp [gramQZ]; ring

/-- Helper: the values of the anisotropic plane. -/
theorem values_ani : {t | ∃ x y, gramQZ !![2, 1; 1, 2] x y = t} = {t : ℤ_[2] | t = 0 ∨ Odd t.valuation} := by
  ext t
  simp only [Set.mem_setOf_eq, gramQZ_ani]
  constructor
  · rintro ⟨x, y, rfl⟩
    by_cases h : x ^ 2 + x * y + y ^ 2 = 0
    · left; rw [h, mul_zero]
    · right
      have := val_ani_even _ x y rfl h
      rw [PadicInt.valuation_mul (by norm_num) h]
      have h2 : (2 : ℤ_[2]).valuation = 1 := by simpa using PadicInt.valuation_p (p := 2)
      rw [h2]
      obtain ⟨r, hr⟩ := this
      exact ⟨r, by omega⟩
  · rintro (rfl | ⟨k, hk⟩)
    · exact ⟨0, 0, by simp⟩
    · have ht : t ≠ 0 := by
        intro h0; rw [h0] at hk; simp at hk
      have hs := PadicInt.unitCoeff_spec ht
      set u := (PadicInt.unitCoeff ht : ℤ_[2]) with hu
      have huu : IsUnit u := Units.isUnit _
      have hdvd : (2 : ℤ_[2]) ∣ 1 - u := by
        rcases parity u with ⟨m, hm⟩ | ⟨m, hm⟩
        · exact absurd huu (by rw [isUnit_iff_not_dvd]; exact not_not.mpr ⟨m, hm⟩)
        · exact ⟨-m, by rw [hm]; ring⟩
      obtain ⟨x0, hx0⟩ := hensel_quad 1 1 (1 - u) isUnit_one hdvd
      refine ⟨2 ^ k * x0, 2 ^ k, ?_⟩
      have hv : t.valuation = 2 * k + 1 := hk
      rw [hv] at hs
      have h2 : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
      rw [h2] at hs
      rw [hs]
      have : u = x0 ^ 2 + x0 + 1 := by linear_combination -hx0
      rw [this]; ring

/-- Helper: `gramQZ` transforms under a change of basis (over $\mathbb Z_2$). -/
theorem gramQZ_congr (S T P : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hS : S 1 0 = S 0 1) (h : Pᵀ * S * P = T)
    (x y : ℤ_[2]) :
    gramQZ T x y = gramQZ S (P 0 0 * x + P 0 1 * y) (P 1 0 * x + P 1 1 * y) := by
  subst h
  simp only [gramQZ, Matrix.mul_apply, Fin.sum_univ_two, transpose_apply, hS]
  ring

/-- Helper: the value set of $T = {}^tPSP$ is contained in that of $S$. -/
theorem values_sub (S T P : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hS : S 1 0 = S 0 1) (h : Pᵀ * S * P = T) :
    {t | ∃ x y, gramQZ T x y = t} ⊆ {t | ∃ x y, gramQZ S x y = t} := by
  rintro t ⟨x, y, rfl⟩
  exact ⟨_, _, (gramQZ_congr S T P hS h x y).symm⟩

/-- Helper: isometric symmetric Gram matrices over $\mathbb Z_2$ have the same value sets. -/
theorem values_eq_of_iso (S T : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hS : S 1 0 = S 0 1) (hT : T 1 0 = T 0 1)
    (h : Iso S T) : {t | ∃ x y, gramQZ S x y = t} = {t | ∃ x y, gramQZ T x y = t} := by
  obtain ⟨P, hPu, hP⟩ := h
  obtain ⟨R, -, hR⟩ := Iso.symm ⟨P, hPu, hP⟩
  exact Set.Subset.antisymm (values_sub T S R hT hR) (values_sub S T P hS hP)

/-- Helper: determinant of an isometric Gram matrix changes by a square of a unit. -/
theorem det_of_iso (S N P : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hP : IsUnit P.det) (h : Pᵀ * S * P = N) :
    ∃ w : ℤ_[2], IsUnit w ∧ S.det = N.det * w ^ 2 := by
  obtain ⟨w, hw⟩ := hP.exists_right_inv
  refine ⟨w, isUnit_iff_exists_inv.mpr ⟨P.det, by rw [mul_comm]; exact hw⟩, ?_⟩
  rw [← h, det_mul, det_mul, det_transpose]
  linear_combination (-(S.det) * (P.det * w + 1)) * hw

/-- Helper: the evaluation of a binary diagonal form over $\mathbb Q_2$. -/
theorem eval_diag2 (a : Fin 2 → ℚ_[2]) (v : Fin 2 → ℚ_[2]) :
    (QuadForm.diag a).evalIn ℚ_[2] v = a 0 * v 0 ^ 2 + a 1 * v 1 ^ 2 := by
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal_apply]
  ring

/-- Helper: if $Q_S$ is isometric (over $\mathbb Z_2$, via $N = {}^tPSP$) to a form $N$ which in turn is modelled
by the diagonal form $\langle b_0, b_1\rangle$ (via an invertible $D$ over $\mathbb Q_2$), then every orthogonal
basis of $FL$ has the Hasse invariant of $b$. -/
theorem hasse_of_model (S N P : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hS : S 1 0 = S 0 1) (hP : IsUnit P.det)
    (hPN : Pᵀ * S * P = N) (b : Fin 2 → ℚ_[2]) (hb : ∀ i, b i ≠ 0) (D : Matrix (Fin 2) (Fin 2) ℚ_[2])
    (hD : IsUnit D.det)
    (hmod : ∀ x y, b 0 * x ^ 2 + b 1 * y ^ 2 = gramQ N (D 0 0 * x + D 0 1 * y) (D 1 0 * x + D 1 1 * y))
    (s : ℤ) (hs : Hasse.hasseK b = s) : HasseOfGram S s := by
  intro a P' ha hP' hQ
  set Pq : Matrix (Fin 2) (Fin 2) ℚ_[2] := P.map (fun z : ℤ_[2] => (z : ℚ_[2])) with hPq
  have hPqd : IsUnit Pq.det := by
    have : Pq.det = ((P.det : ℤ_[2]) : ℚ_[2]) := by
      rw [hPq]; exact (RingHom.map_det (PadicInt.Coe.ringHom) P).symm
    rw [this]
    exact isUnit_iff_ne_zero.mpr (fun h => hP.ne_zero (PadicInt.coe_eq_zero.mp h))
  have hM : IsUnit (P'⁻¹ * Pq * D).det := by
    rw [det_mul, det_mul, det_nonsing_inv]
    exact ((Ring.inverse_unit hP'.unit ▸ hP'.unit⁻¹.isUnit).mul hPqd).mul hD
  have key : (QuadForm.diag a).IsometricIn ℚ_[2] (QuadForm.diag b) := by
    refine ⟨P'⁻¹ * Pq * D, hM, fun x => ?_⟩
    rw [eval_diag2, eval_diag2]
    set v : Fin 2 → ℚ_[2] := (P'⁻¹ * Pq * D) *ᵥ x with hv
    have hmv : P' *ᵥ v = (Pq * D) *ᵥ x := by
      rw [hv, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mul_assoc P', Matrix.mul_nonsing_inv _ hP',
        Matrix.one_mul]
    have h0 := congrFun hmv 0
    have h1 := congrFun hmv 1
    have e1 := hQ (v 0) (v 1)
    have e2 := gramQ_congr S N P hS hPN ((D *ᵥ x) 0) ((D *ᵥ x) 1)
    have e3 := hmod (x 0) (x 1)
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, hPq, Matrix.map_apply] at h0 h1 e2 e3 ⊢
    rw [← e1, h0, h1, e3, e2]
    congr 1 <;> ring
  have := ((Kitaoka.Theorem351.theorem352 2 a b ha hb).mp key).2
  rw [this, hs]

/-- Helper: the dyadic Hilbert symbol formula for $2^\alpha u,\ 2^\beta v$ with $u, v \in \mathbb Z_2$ units. -/
theorem hs2 (α β : ℕ) (u v : ℤ_[2]) (hu : IsUnit u) (hv : IsUnit v) :
    hilbertSymbol ℚ_[2] ((2 : ℚ_[2]) ^ α * (u : ℚ_[2])) ((2 : ℚ_[2]) ^ β * (v : ℚ_[2])) =
      (-1) ^ (HilbertLocal.twoEps (PadicInt.toZModPow 3 u) * HilbertLocal.twoEps (PadicInt.toZModPow 3 v)
        + α * HilbertLocal.twoOmega (PadicInt.toZModPow 3 v)
        + β * HilbertLocal.twoOmega (PadicInt.toZModPow 3 u)) := by
  have := HilbertLocal.hilbertSymbol_two_formula α β hu.unit hv.unit
  simpa using this

/-- Helper: $(1,-1)_2 = 1$. -/
theorem hs_1_m1 : hilbertSymbol ℚ_[2] 1 (-1) = 1 := by
  have := hs2 0 0 1 (-1) isUnit_one (by simp)
  simp at this
  rw [this]
  simp [HilbertLocal.twoEps, HilbertLocal.twoOmega]

/-- Helper: $(1,1)_2 = 1$. -/
theorem hs_1_1 : hilbertSymbol ℚ_[2] 1 1 = 1 := by
  have := hs2 0 0 1 1 isUnit_one isUnit_one
  simp at this
  rw [this]
  simp [HilbertLocal.twoEps, HilbertLocal.twoOmega]

/-- Helper: $(-1,-1)_2 = -1$. -/
theorem hs_m1_m1 : hilbertSymbol ℚ_[2] (-1) (-1) = -1 := by
  have := hs2 0 0 (-1) (-1) (by simp) (by simp)
  simp at this
  rw [this]
  have h7 : (-1 : ZMod (2 ^ 3)) = 7 := by decide
  simp [HilbertLocal.twoEps, HilbertLocal.twoOmega, h7]
  decide

/-- Helper: $3$ is a unit of $\mathbb Z_2$. -/
theorem isUnit_three : IsUnit (3 : ℤ_[2]) := by
  have h : (3 : ℤ_[2]) = 2 * 1 + 1 := by norm_num
  rw [h]; exact isUnit_two_mul_add_one 1

/-- Helper: $2^1 \cdot 3 = 6$ in $\mathbb Q_2$ (via $\mathbb Z_2$). -/
theorem h6q : (2 : ℚ_[2]) ^ 1 * ((3 : ℤ_[2]) : ℚ_[2]) = 6 := by
  have : ((3 : ℤ_[2]) : ℚ_[2]) = 3 := by norm_cast
  rw [this]; norm_num

/-- Helper: $2^1 \cdot 1 = 2$ in $\mathbb Q_2$ (via $\mathbb Z_2$). -/
theorem h2q : (2 : ℚ_[2]) ^ 1 * ((1 : ℤ_[2]) : ℚ_[2]) = 2 := by simp

/-- Helper: $(2,2)_2 = 1$. -/
theorem hs_2_2 : hilbertSymbol ℚ_[2] 2 2 = 1 := by
  have := hs2 1 1 1 1 isUnit_one isUnit_one
  simp at this
  rw [this]
  simp [HilbertLocal.twoEps, HilbertLocal.twoOmega]

/-- Helper: $(2,6)_2 = -1$. -/
theorem hs_2_6 : hilbertSymbol ℚ_[2] 2 6 = -1 := by
  have := hs2 1 1 1 3 isUnit_one isUnit_three
  rw [h6q, h2q] at this
  rw [this]
  have h3 : PadicInt.toZModPow 3 (3 : ℤ_[2]) = (3 : ZMod (2 ^ 3)) := map_ofNat _ 3
  simp [HilbertLocal.twoEps, HilbertLocal.twoOmega, h3]
  decide

/-- Helper: $(6,6)_2 = -1$. -/
theorem hs_6_6 : hilbertSymbol ℚ_[2] 6 6 = -1 := by
  have := hs2 1 1 3 3 isUnit_three isUnit_three
  rw [h6q] at this
  rw [this]
  have h3 : PadicInt.toZModPow 3 (3 : ℤ_[2]) = (3 : ZMod (2 ^ 3)) := map_ofNat _ 3
  simp [HilbertLocal.twoEps, HilbertLocal.twoOmega, h3]
  decide

/-- Helper: $S(\langle 1\rangle \perp \langle -1\rangle) = -1$. -/
theorem hasseK_hyp : Hasse.hasseK (![1, -1] : Fin 2 → ℚ_[2]) = -1 := by
  simp [Hasse.hasseK, Fin.prod_univ_two, hs_1_1, hs_1_m1, hs_m1_m1]

/-- Helper: $S(\langle 2\rangle \perp \langle 6\rangle) = 1$. -/
theorem hasseK_ani : Hasse.hasseK (![2, 6] : Fin 2 → ℚ_[2]) = 1 := by
  simp [Hasse.hasseK, Fin.prod_univ_two, hs_2_2, hs_2_6, hs_6_6]

/-- **Kitaoka 1993, Lemma 5.2.6, isotropic case** (p. 77). Let $S$ be the Gram matrix of a binary unimodular lattice
$L$ over $\mathbb Z_2$ with $\mathfrak n(L) = (2)$ (symmetric, $\det S$ a unit, even diagonal), and suppose $FL$ is
isotropic. Then $L \cong \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, $dL = -1$ ($\det S = -u^2$ with $u$ a
unit), $S(FL) = -1$ (for every orthogonal basis of $FL$) and $Q(L) = (2) = 2\mathbb Z_2$. Unconditional. -/
@[kb "kitaoka1993" "§5.2, Lemma 5.2.6, p. 77 (isotropic case)"]
theorem lemma526_isotropic (S : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hS : Sᵀ = S) (hu : IsUnit S.det)
    (h0 : 2 ∣ S 0 0) (h1 : 2 ∣ S 1 1) (hiso : ∃ x y : ℚ_[2], (x, y) ≠ 0 ∧ gramQ S x y = 0) :
    (∃ P : Matrix (Fin 2) (Fin 2) ℤ_[2], IsUnit P.det ∧ Pᵀ * S * P = !![0, 1; 1, 0]) ∧
    (∃ u : ℤ_[2], IsUnit u ∧ S.det = -u ^ 2) ∧
    HasseOfGram S (-1) ∧
    {t | ∃ x y, gramQZ S x y = t} = {t | ∃ s, t = 2 * s} := by
  have hsym : S 1 0 = S 0 1 := by
    have := congrFun (congrFun hS 0) 1
    simpa [transpose_apply] using this
  obtain ⟨P, hP, hPS⟩ := (lemma526 S hS hu h0 h1).1 hiso
  refine ⟨⟨P, hP, hPS⟩, ?_, ?_, ?_⟩
  · obtain ⟨w, hw, hd⟩ := det_of_iso S _ P hP hPS
    exact ⟨w, hw, by rw [hd, det_fin_two_of]; ring⟩
  · refine hasse_of_model S _ P hsym hP hPS ![1, -1] (by intro i; fin_cases i <;> simp)
      !![1, 1; 1/2, -1/2] (by rw [det_fin_two_of]; exact isUnit_iff_ne_zero.mpr (by norm_num))
      (fun x y => by simp [gramQ]; ring) _ hasseK_hyp
  · rw [values_eq_of_iso S _ hsym (by simp) ⟨P, hP, hPS⟩]
    ext t
    simp only [Set.mem_setOf_eq, gramQZ_hyp]
    constructor
    · rintro ⟨x, y, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨s, rfl⟩; exact ⟨s, 1, by ring⟩

/-- **Kitaoka 1993, Lemma 5.2.6, anisotropic case** (p. 77). Let $S$ be the Gram matrix of a binary unimodular
lattice $L$ over $\mathbb Z_2$ with $\mathfrak n(L) = (2)$, and suppose $FL$ is anisotropic. Then
$L \cong \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$, $dL = 3$ ($\det S = 3u^2$ with $u$ a unit), $S(FL) = 1$
(for every orthogonal basis of $FL$) and $Q(L) = \{0\} \cup \{t \mid \operatorname{ord}_2 t \text{ odd}\}$.
Unconditional. -/
@[kb "kitaoka1993" "§5.2, Lemma 5.2.6, p. 77 (anisotropic case)"]
theorem lemma526_anisotropic (S : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hS : Sᵀ = S) (hu : IsUnit S.det)
    (h0 : 2 ∣ S 0 0) (h1 : 2 ∣ S 1 1) (haniso : ¬ ∃ x y : ℚ_[2], (x, y) ≠ 0 ∧ gramQ S x y = 0) :
    (∃ P : Matrix (Fin 2) (Fin 2) ℤ_[2], IsUnit P.det ∧ Pᵀ * S * P = !![2, 1; 1, 2]) ∧
    (∃ u : ℤ_[2], IsUnit u ∧ S.det = 3 * u ^ 2) ∧
    HasseOfGram S 1 ∧
    {t | ∃ x y, gramQZ S x y = t} = {t | t = 0 ∨ Odd t.valuation} := by
  have hsym : S 1 0 = S 0 1 := by
    have := congrFun (congrFun hS 0) 1
    simpa [transpose_apply] using this
  obtain ⟨P, hP, hPS⟩ := (lemma526 S hS hu h0 h1).2 haniso
  refine ⟨⟨P, hP, hPS⟩, ?_, ?_, ?_⟩
  · obtain ⟨w, hw, hd⟩ := det_of_iso S _ P hP hPS
    exact ⟨w, hw, by rw [hd, det_fin_two_of]; ring⟩
  · refine hasse_of_model S _ P hsym hP hPS ![2, 6] (by intro i; fin_cases i <;> simp)
      !![1, -1; 0, 2] (by rw [det_fin_two_of]; exact isUnit_iff_ne_zero.mpr (by norm_num))
      (fun x y => by
        have h2 : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by norm_cast
        simp [gramQ, h2]; ring) _ hasseK_ani
  · rw [values_eq_of_iso S _ hsym (by simp) ⟨P, hP, hPS⟩]
    exact values_ani

end QuadFormsKB.Kitaoka.Padic
