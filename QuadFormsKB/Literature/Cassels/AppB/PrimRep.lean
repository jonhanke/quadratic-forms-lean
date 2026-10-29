/-
# Cassels, Appendix B, Lemma 2.2: the necessary condition for primitive representations

**Setting.** Integral binary forms $f = [a,b,c] = ax^2+bxy+cy^2$ (`BinQF`), discriminant $D = b^2 - 4ac$. A primitive
representation of $m$ is $m = f(x, y)$ with $\gcd(x, y) = 1$.

**Proves** (Cassels, *Rational Quadratic Forms*, App. B, Lemma 2.2, p. 372, first sentence): if $f$ represents $m$
primitively then $D \equiv u^2 \pmod{4m}$ for some $u$ (`exists_sq_mod_of_primRep`: this is the correspondence
used in Cassels' proof, $f \sim [m, u, v]$ with $u^2 - 4mv = D$); consequently every odd prime $p \mid m$ with
$p \nmid D$ has $(D/p) = +1$ (`legendreSym_eq_one_of_primRep`) and, if $2 \mid m$ and $D$ is odd,
$D \equiv 1 \pmod 8$, i.e. the Kronecker symbol $(D/2) = +1$ (`disc_mod_eight_of_primRep`). The count $2^\mu$ of
orbits of primitive representations (second sentence of the Lemma) is not formalized.

**Proof.** Move the primitive representation to the first coefficient (`Binary.exists_subst_a_eq`): $f \sim
[m, u, v]$, so $D = u^2 - 4mv$.
-/
import QuadFormsKB.Binary.GenusCharacters

namespace QuadFormsKB.Cassels

open QuadFormsKB.Binary BinQF

/-- **Cassels, App. B, proof of Lemma 2.2, p. 372.** If $\gcd(x, y) = 1$ and $m = f(x, y)$, then
$4m \mid u^2 - D$ for some integer $u$ ($D$ the discriminant of $f$). -/
@[kb "cassels1978" "App. B, proof of Lemma 2.2, p. 372 (f ~ [m, u, v], u² − 4mv = D)"]
theorem exists_sq_mod_of_primRep (f : BinQF) {x y : ℤ} (hxy : IsCoprime x y) :
    ∃ u : ℤ, 4 * f.eval x y ∣ u ^ 2 - f.disc := by
  obtain ⟨r, s, hdet, ha⟩ := exists_subst_a_eq f hxy
  have hd := disc_subst_of_det x r y s f (by rw [hdet]; norm_num)
  refine ⟨(subst x r y s f).b, ⟨(subst x r y s f).c, ?_⟩⟩
  rw [← hd, ← ha, disc]; ring

/-- **Cassels, App. B, Lemma 2.2, p. 372 (necessity, odd primes).** If $f$ represents $m = f(x,y)$ primitively and
$p$ is an odd prime with $p \mid m$, $p \nmid D$, then the Legendre symbol $(D/p) = +1$. -/
@[kb "cassels1978" "App. B, Lemma 2.2, p. 372 (special case: the necessary condition (D/p) = +1, p odd)"]
theorem legendreSym_eq_one_of_primRep (f : BinQF) {x y : ℤ} (hxy : IsCoprime x y) {p : ℕ}
    [Fact p.Prime] (hpm : (p : ℤ) ∣ f.eval x y) (hpD : ¬ (p : ℤ) ∣ f.disc) :
    legendreSym p f.disc = 1 := by
  obtain ⟨u, hu⟩ := exists_sq_mod_of_primRep f hxy
  have h1 : (p : ℤ) ∣ u ^ 2 - f.disc := (hpm.mul_left 4).trans hu
  have hne : (f.disc : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [legendreSym.eq_one_iff p hne]
  refine ⟨(u : ZMod p), ?_⟩
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h1
  push_cast at this
  rw [← sq]; exact (sub_eq_zero.1 this).symm

/-- **Cassels, App. B, Lemma 2.2, p. 372 (necessity, $p = 2$).** If $f$ represents an even $m = f(x,y)$ primitively
and $D$ is odd, then $D \equiv 1 \pmod 8$, i.e. the Kronecker symbol $(D/2) = +1$. -/
@[kb "cassels1978" "App. B, Lemma 2.2, p. 372 (special case: the necessary condition (D/2) = +1)"]
theorem disc_mod_eight_of_primRep (f : BinQF) {x y : ℤ} (hxy : IsCoprime x y)
    (h2m : (2 : ℤ) ∣ f.eval x y) (hD : ¬ (2 : ℤ) ∣ f.disc) : f.disc % 8 = 1 := by
  obtain ⟨u, k, hk⟩ := exists_sq_mod_of_primRep f hxy
  obtain ⟨m, hm⟩ := h2m
  rw [hm] at hk
  have hu : ¬ 2 ∣ u := by
    rintro ⟨v, rfl⟩; apply hD; exact ⟨2 * v ^ 2 - 4 * m * k, by linear_combination -hk⟩
  obtain ⟨v, rfl⟩ : Odd u := by
    rcases Int.emod_two_eq_zero_or_one u with h | h
    · exact absurd (Int.dvd_of_emod_eq_zero h) hu
    · exact Int.odd_iff.2 h
  obtain ⟨w, hw⟩ := Int.even_mul_succ_self v
  have : f.disc = 8 * (w - m * k) + 1 := by linear_combination -hk + 4 * hw
  rw [this]
  generalize w - m * k = z
  omega
end QuadFormsKB.Cassels
