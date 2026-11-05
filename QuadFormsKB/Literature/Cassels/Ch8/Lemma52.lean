import QuadFormsKB.Literature.Cassels.Ch8.CongruentDet
import QuadFormsKB.Literature.Cassels.Ch9Sec4LocalPadic
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

/-!
# Cassels, Chapter 8, Lemma 5.2 for every prime $p$, and the Note deriving Lemma 5.1 from it

**Setting** (Cassels, Ch. 8, §5, p. 123, read from the page image on 2026-10-30): $d \in \mathbb Z_p$, $d \ne 0$,
$\lvert d\rvert = p^{-\delta}$ (so $\delta = v_p(d)$); $\lambda = 1$ if $p = 2$ and $\lambda = 0$ otherwise ((5.1));
$f$ is a classically integral form with $d(f) = d$ ((5.2)–(5.4)) and $g$ is another integral form. Forms are given by
their symmetric matrices $F, G$ over $\mathbb Z_p$; $d(f) = \det F$, and "$g_{ij} \equiv f_{ij} \pmod{p^k}$" is entrywise
divisibility of $G - F$ by $p^k$. $\mathbb Z_p$-equivalence is $T^{t}FT = G$ with $T \in \mathrm{GL}_n(\mathbb Z_p)$.

**Proves.**
- `exists_equiv_of_congr_det_all` (**Lemma 5.2**, every $p$, including $p = 2$): if $d(g) = du^{2}$ for a unit $u$
  ((5.6)) and $g_{ij} \equiv f_{ij} \pmod{p^{\delta + 2\lambda}}$ ((5.7)), then $f$ and $g$ are $\mathbb Z_p$-equivalent.
  The printed precision (5.7) is $p^{\delta + 2\lambda}$ (page image); `exists_equiv_of_congr_det` (`Ch8/CongruentDet.lean`)
  is the case $p \ne 2$, where (5.7) reads $p^{\delta}$. Cassels proves the lemma only for $p \ne 2$ ("somewhat more
  difficult for $p = 2$"); here both cases come from the library's local form of Ch. 9, Lemma 4.3,
  `Siegel.CongrLocal.meq_of_congr` (congruence modulo $4c$ with $\det F \mid c$), applied with $c = p^{\delta}$: then
  $4c = p^{\delta + 2\lambda}$ up to a unit.
- `det_sq_of_congr` and `lemma51_of_lemma52` (**the Note after Lemma 5.2**, p. 123): congruence (5.5),
  $g_{ij} \equiv f_{ij} \pmod{p^{\delta + 2\lambda + 1}}$, implies $d(g) \equiv d(f) \pmod{p^{\delta + 2\lambda + 1}}$ and
  hence (5.6); so Lemma 5.1 follows from Lemma 5.2.
-/

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

variable (p) in
/-- Cassels' $\lambda$ of (5.1), Ch. 8, p. 123: $\lambda = 1$ if $p = 2$ and $\lambda = 0$ otherwise. -/
@[kb "cassels1978" "Ch. 8, §5, (5.1), p. 123 (λ = 1 if p = 2, 0 otherwise)"]
def casselsLambda : ℕ := if p = 2 then 1 else 0

/-- Helper: $\det F$ divides $p^{v_p(\det F)}$ in $\mathbb Z_p$. -/
theorem det_dvd_pow_valuation {x : ℤ_[p]} (hx : x ≠ 0) : x ∣ (p : ℤ_[p]) ^ x.valuation := by
  set u := PadicInt.unitCoeff hx
  have h : x = (u : ℤ_[p]) * (p : ℤ_[p]) ^ x.valuation := PadicInt.unitCoeff_spec hx
  refine ⟨((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
  calc (p : ℤ_[p]) ^ x.valuation = ((u * u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ x.valuation := by simp
    _ = (u : ℤ_[p]) * (p : ℤ_[p]) ^ x.valuation * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by push_cast; ring
    _ = x * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by rw [← h]

/-- Helper: $4p^{\delta} \mid x$ whenever $p^{\delta + 2\lambda} \mid x$ ($4 = p^{2\lambda}$ up to a unit). -/
theorem four_mul_dvd_of_pow_dvd {δ : ℕ} {x : ℤ_[p]} (h : (p : ℤ_[p]) ^ (δ + 2 * casselsLambda p) ∣ x) :
    4 * (p : ℤ_[p]) ^ δ ∣ x := by
  unfold casselsLambda at h
  split_ifs at h with h2
  · subst h2
    refine (dvd_of_eq ?_).trans h
    push_cast; ring
  · have h4 : IsUnit (4 : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, show (4 : ℤ_[p]) = ((2 : ℕ) : ℤ_[p]) ^ 2 by norm_num, norm_pow,
        PadicInt.norm_natCast_eq_one_iff.2 ?_, one_pow]
      exact (Nat.coprime_primes hp.out Nat.prime_two).2 h2
    simp only [mul_zero, add_zero] at h
    exact h4.mul_left_dvd.2 h

/-- **Cassels, Ch. 8, Lemma 5.2** (p. 123; every prime $p$, including $p = 2$): *let $f$ be a classically integral
form with $d(f) = d \ne 0$, $\lvert d\rvert = p^{-\delta}$, and $g$ another integral form. Suppose that $d(g) = du^{2}$
for some unit $u$ (5.6) and that $g_{ij} \equiv f_{ij} \pmod{p^{\delta + 2\lambda}}$ (5.7). Then $f$ and $g$ are
$\mathbb Z_p$-equivalent.* Here $F, G$ are the symmetric matrices of $f, g$ over $\mathbb Z_p$, $\delta$ is
`F.det.valuation`, $\lambda$ is `casselsLambda p`, and the conclusion is $T^{t}FT = G$ with
$T \in \mathrm{GL}_n(\mathbb Z_p)$. *Update:* Cassels proves only $p \ne 2$; the case $p = 2$ holds as stated (proof via
`Siegel.CongrLocal.meq_of_congr`). -/
@[kb "cassels1978" "Ch. 8, Lemma 5.2, p. 123"]
theorem exists_equiv_of_congr_det_all (F G : Matrix (Fin n) (Fin n) ℤ_[p]) (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hdet : F.det ≠ 0) {u : ℤ_[p]} (hu : IsUnit u) (hd : G.det = F.det * u ^ 2)
    (hcong : ∀ i j, (p : ℤ_[p]) ^ (F.det.valuation + 2 * casselsLambda p) ∣ G i j - F i j) :
    ∃ T : GL (Fin n) ℤ_[p], (T.val)ᵀ * F * T.val = G := by
  obtain ⟨T, hT, hTe⟩ := Siegel.CongrLocal.meq_of_congr (p := p) (Fin n) F G ((p : ℤ_[p]) ^ F.det.valuation) hF hG
    hdet (det_dvd_pow_valuation hdet) (fun i j => by
      rw [Matrix.sub_apply]; exact four_mul_dvd_of_pow_dvd (hcong i j))
    ⟨u, hu, by rw [hd]; ring⟩
  exact ⟨((Matrix.isUnit_iff_isUnit_det T).2 hT).unit, by simpa using hTe⟩

/-- Helper: entrywise congruence modulo $m$ gives congruence of determinants modulo $m$. -/
theorem dvd_det_sub_det {R : Type*} [CommRing R] (m : R) (F G : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, m ∣ G i j - F i j) : m ∣ G.det - F.det := by
  set π := Ideal.Quotient.mk (Ideal.span {m})
  have hmap : G.map π = F.map π := by
    ext i j
    simp only [Matrix.map_apply]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (h i j))
  have e1 := RingHom.map_det π G
  have e2 := RingHom.map_det π F
  rw [RingHom.mapMatrix_apply] at e1 e2
  have : π G.det = π F.det := by rw [e1, e2, hmap]
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 this)

/-- Helper: an element of $\mathbb Z_p$ congruent to $1$ modulo $p^{2\lambda + 1}$ is the square of a unit. -/
theorem exists_unit_sq_of_dvd_sub_one {x : ℤ_[p]} (hx : (p : ℤ_[p]) ^ (2 * casselsLambda p + 1) ∣ x - 1) :
    ∃ w : ℤ_[p], IsUnit w ∧ x = w ^ 2 := by
  have hp1 : (p : ℤ_[p]) ∣ x - 1 := (dvd_pow_self _ (by omega)).trans hx
  have hxu : IsUnit x := Siegel.CongrLocal.isUnit_of_dvd_sub' isUnit_one hp1
  suffices h : ∃ w : ℤ_[p], x = w ^ 2 by
    obtain ⟨w, hw⟩ := h
    exact ⟨w, isUnit_of_mul_isUnit_left (x := w) (y := w) (by rw [← sq, ← hw]; exact hxu), hw⟩
  unfold casselsLambda at hx
  split_ifs at hx with h2
  · subst h2
    have hred : PadicInt.toZModPow 3 (hxu.unit : ℤ_[2]) = 1 := by
      have : PadicInt.toZModPow 3 (x - 1) = 0 := by
        rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
        simpa using hx
      rw [map_sub, sub_eq_zero] at this
      simpa using this
    obtain ⟨r, hr⟩ := (HilbertLocal.isSquare_two_adic_unit_iff hxu.unit).2 hred
    simp only [IsUnit.unit_spec] at hr
    have hr1 : ‖r‖ ≤ 1 := by
      have h1 : ‖r‖ * ‖r‖ = 1 := by
        rw [← norm_mul, ← hr, PadicInt.norm_coe]; exact PadicInt.isUnit_iff.1 hxu
      nlinarith [norm_nonneg r]
    set z : ℤ_[2] := ⟨r, hr1⟩
    have hz : (z : ℚ_[2]) = r := rfl
    refine ⟨z, ?_⟩
    have : ((x : ℤ_[2]) : ℚ_[2]) = ((z ^ 2 : ℤ_[2]) : ℚ_[2]) := by rw [PadicInt.coe_pow, hz, hr, sq]
    exact PadicInt.ext this
  · have h1 : PadicInt.toZMod x = (1 : ZMod p) ^ 2 := by
      have : PadicInt.toZMod (x - 1) = 0 := by
        rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
          Ideal.mem_span_singleton]
        simpa using hx
      rw [map_sub, sub_eq_zero] at this
      simpa using this
    obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod h2 x one_ne_zero h1
    exact ⟨z, hz.symm⟩

/-- **Cassels, Ch. 8, Note after Lemma 5.2** (p. 123), first half: *(5.5) implies
$d(g) \equiv d(f) \pmod{p^{\delta + 2\lambda + 1}}$ and hence (5.6)*, that is, $d(g) = d(f)u^{2}$ for a unit $u$. -/
@[kb "cassels1978" "Ch. 8, §5, Note after Lemma 5.2, p. 123 ((5.5) implies (5.6))"]
theorem det_sq_of_congr (F G : Matrix (Fin n) (Fin n) ℤ_[p]) (hdet : F.det ≠ 0)
    (hcong : ∀ i j, (p : ℤ_[p]) ^ (F.det.valuation + 2 * casselsLambda p + 1) ∣ G i j - F i j) :
    (p : ℤ_[p]) ^ (F.det.valuation + 2 * casselsLambda p + 1) ∣ G.det - F.det ∧
      ∃ u : ℤ_[p], IsUnit u ∧ G.det = F.det * u ^ 2 := by
  have hD := dvd_det_sub_det _ F G hcong
  refine ⟨hD, ?_⟩
  set δ := F.det.valuation
  set v := (PadicInt.unitCoeff hdet : ℤ_[p])
  have hFv : F.det = v * (p : ℤ_[p]) ^ δ := PadicInt.unitCoeff_spec hdet
  obtain ⟨m, hm⟩ := hD
  have hvi : v * ((PadicInt.unitCoeff hdet)⁻¹ : ℤ_[p]ˣ) = 1 := Units.mul_inv _
  set x : ℤ_[p] := 1 + (p : ℤ_[p]) ^ (2 * casselsLambda p + 1) * m * ((PadicInt.unitCoeff hdet)⁻¹ : ℤ_[p]ˣ)
  have hx : (p : ℤ_[p]) ^ (2 * casselsLambda p + 1) ∣ x - 1 := ⟨m * ((PadicInt.unitCoeff hdet)⁻¹ : ℤ_[p]ˣ), by
    simp only [x]; ring⟩
  obtain ⟨w, hw, hxw⟩ := exists_unit_sq_of_dvd_sub_one hx
  refine ⟨w, hw, ?_⟩
  rw [← hxw]
  have hG : G.det = F.det + (p : ℤ_[p]) ^ (δ + 2 * casselsLambda p + 1) * m := by rw [← hm]; ring
  rw [hG, hFv]
  simp only [x]
  linear_combination (-(p : ℤ_[p]) ^ (δ + 2 * casselsLambda p + 1) * m) * hvi

/-- **Cassels, Ch. 8, Note after Lemma 5.2** (p. 123): *Lemma 5.1 follows from Lemma 5.2.* If $f$ is classically
integral with $d(f) \ne 0$ and $g_{ij} \equiv f_{ij} \pmod{p^{\delta + 2\lambda + 1}}$ (5.5), then (5.6) and (5.7) hold
(`det_sq_of_congr`), so `exists_equiv_of_congr_det_all` gives the $\mathbb Z_p$-equivalence of $f$ and $g$. (The
library's direct proof of Lemma 5.1 is `exists_equiv_of_congruent`.) -/
@[kb "cassels1978" "Ch. 8, §5, Note after Lemma 5.2, p. 123 (Lemma 5.1 follows from Lemma 5.2)"]
theorem lemma51_of_lemma52 (F G : Matrix (Fin n) (Fin n) ℤ_[p]) (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hdet : F.det ≠ 0)
    (hcong : ∀ i j, (p : ℤ_[p]) ^ (F.det.valuation + 2 * casselsLambda p + 1) ∣ G i j - F i j) :
    ∃ T : GL (Fin n) ℤ_[p], (T.val)ᵀ * F * T.val = G := by
  obtain ⟨-, u, hu, hd⟩ := det_sq_of_congr F G hdet hcong
  exact exists_equiv_of_congr_det_all F G hF hG hdet hu hd fun i j =>
    (pow_dvd_pow _ (Nat.le_succ _)).trans (hcong i j)

end QuadFormsKB.Cassels
