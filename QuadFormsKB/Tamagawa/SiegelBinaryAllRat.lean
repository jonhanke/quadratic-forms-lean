import QuadFormsKB.Tamagawa.SiegelBinaryTotallyReal
import QuadFormsKB.Tamagawa.BinaryTauRat
import QuadFormsKB.Binary.SiegelNonPrimitive
import QuadFormsKB.Binary.SiegelBinaryChecks

/-!
# The classical binary Siegel formula over ℚ for every positive definite form

**Layer:** binary integral quadratic forms $f = ax^2 + bxy + cy^2$ (`BinQF`, $b$ not required even), positive definite, of
**any** discriminant $D = b^2 - 4ac < 0$, primitive or not. Write $D = k^2D_0$ with $D_0$ the fundamental discriminant of
$\mathbb Q(\sqrt D)$ and $k \ge 1$ (`exists_fundamental_decomp`; $k$ = content $\times$ conductor).

**Statement** (`siegelFormula_binary_all`): for every $m \ge 1$,
$$r_{\mathrm{gen}}(f, m) = \tfrac12\,\beta_\infty(f, m)\cdot L(1,\chi_{D_0})^{-1}\prod_{p \mid k\,m\,D_0}\frac{\beta_p(f, m)}{1-\chi_{D_0}(p)/p}$$
(`Siegel.genusRepAvg f m = (1/2) * Siegel.aEWith f m (binaryEulerValueNP f D₀ k m)`), the finite product being exactly the
product over all primes of $\beta_p(f,m)(1-\chi_{D_0}(p)/p)^{-1}$ (all other factors are $1$, `localDensity_good_gen`).

**Conventions.**
* $r_{\mathrm{gen}}(f, m)$ = `Siegel.genusRepAvg f m` $= \bigl(\sum_{[g]} r_g(m)/|\mathrm{Aut}(g)|\bigr)/\bigl(\sum_{[g]} 1/|\mathrm{Aut}(g)|\bigr)$,
  $[g]$ ranging over the $\mathrm{GL}_2(\mathbb Z)$-classes of integral forms $g$ in the genus of $f$ (`Siegel.genusClasses`:
  $g$ equivalent to $f$ over $\mathbb Z_p$ for every $p$ and over $\mathbb R$; this forces $\mathrm{disc}\,g = D$ and the same content),
  $\mathrm{Aut}(g) \subseteq \mathrm{GL}_2(\mathbb Z)$ including improper automorphisms. **Not** Gauss's $\mathrm{SL}_2(\mathbb Z)$ (proper) classes;
  the average is the same number in both conventions only after reweighting, which is not done here.
* $\beta_p(f, m)$ = `LocalDensity.localDensity f p m` $= \lim_k p^{-k}\#\{x \in (\mathbb Z/p^k)^2 : f(x) \equiv m\}$, at every prime
  $p$, $p \mid 2kD_0$ included, not evaluated in closed form at $p \mid k$; $\beta_\infty$ = `Siegel.betaInf` ($= 2\pi/\sqrt{|D|}$).
* $\chi_{D_0}$ = `kronR D₀` (Kronecker symbol $(D_0/\cdot)$), $L(1,\chi_{D_0})$ = `Binary.LOne D₀` (Mathlib's Dirichlet $L$-function).

**Proof** (no new number theory): `siegelFormulaAt2_nf` at $F = \mathbb Q$ (binary-F) for $f\otimes\mathcal O_\mathbb Q$, then
* lattice genus $\leftrightarrow$ the genus of forms: `RatBridge.mass_rat`, `RatBridge.repMass_rat` (every lattice class in
  the genus of $\mathbb Z^2$ is free; weights $1/|O(M)| = 1/|\mathrm{Aut}(g)|$ with $\mathrm{Aut}\subseteq\mathrm{GL}_2(\mathbb Z)$);
* $\chi_Q = \chi_{D_0}$ off a finite set (`chiP_up_eq_kronChi`): both $1-\chi(p)/p$ equal $\beta_p(f,m)$ at almost all $p$
  (`localDensity_eq_one_sub_chiP`, and `localDensity_good_gen`: the good-prime density
  $\beta_p(f,m) = (1-\chi_{D_0}(p)/p)\sum_{j\le v_p(m)}\chi_{D_0}(p)^j$ for $p \nmid D$, extended from fundamental $D$ to $D = k^2D_0$ —
  only the value $\chi_D(p) = \chi_{D_0}(p)$ for $p \nmid k$ changes);
* the regularized product is then the finite product above (`regProd_up_eq_binaryEulerValueNP`, the $D = k^2D_0$ extension of
  `regProd_up_eq_binaryEulerValue`); for $m$ not represented over $\mathbb Q$ both sides vanish.

**Consistency with the earlier binary results.** `siegelFormula_binary_all_posForms` (primitive, $D$
fundamental, $k = 1$) is
`siegelFormula_binary`; for $f = c\,g$ with $g$ primitive of fundamental discriminant ($k = c$) the right side is literally that of
`siegelFormula_binary_posDef` (`siegelFormula_binary_all_smul`). New: every form whose primitive part has
non-fundamental discriminant (the gap
`BinarySiegelNonFundamental`), e.g. `siegelFormula_x2_add_4y2` ($D = -16$) and `siegelFormula_x2_add_3y2`
($D = -12$). $\chi_Q = \chi_{D_0}$ off a finite set: `chiP_up_eq_kronChi`.

Source: Siegel 1935, Hauptsatz ($n = 2$, $\varepsilon = \tfrac12$) [unverified locator]; Hanke 2004, (4.5), (5.3)–(5.5).
-/

open NumberField IsDedekindDomain Matrix Filter Topology
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryAllRat

open QuadFormsKB.Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular RatBridge
open QuadFormsKB.Binary BinaryTauRat

/-! ### 1. $D = k^2D_0$ -/

/-- **Every negative discriminant is $k^2$ times a fundamental one:** for $D < 0$ with $D \equiv 0, 1 \pmod 4$ there are a
fundamental discriminant $D_0 < 0$ (`IsQuadDisc D₀`) and $k \ge 1$ with $D = k^2D_0$ (write $-D = b^2a$, $a$ squarefree; $D_0 = -a$
if $-a \equiv 1 \pmod 4$, else $b$ is even and $D_0 = -4a$, $k = b/2$). -/
theorem exists_fundamental_decomp {D : ℤ} (hD : D < 0) (h4 : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ D₀ : ℤ, IsQuadDisc D₀ ∧ D₀ < 0 ∧ ∃ k : ℕ, k ≠ 0 ∧ D = (k : ℤ) ^ 2 * D₀ := by
  obtain ⟨b, a, hba, hsq⟩ := exists_sq_mul_squarefree (-D).toNat
  have hD' : (((-D).toNat : ℕ) : ℤ) = -D := Int.toNat_of_nonneg (by omega)
  have hDz : D = -((b : ℤ) ^ 2 * a) := by rw [← hba] at hD'; push_cast at hD'; linarith
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast hsq.ne_zero
  have hb0 : (b : ℤ) ≠ 0 := by rintro h; rw [h] at hDz; omega
  have ha1 : (1 : ℤ) ≤ a := by have := hsq.ne_zero; omega
  have hsqZ : Squarefree (-(a : ℤ)) := Int.squarefree_natAbs.mp (by simpa using hsq)
  have h4a : ¬ (4 : ℤ) ∣ a := by
    intro h
    have h4' : (2 * 2 : ℕ) ∣ a := by exact_mod_cast h
    exact absurd (Nat.isUnit_iff.mp (hsq 2 h4')) (by norm_num)
  have hb1 : (1 : ℤ) ≤ b := by omega
  by_cases h : (-(a : ℤ)) % 4 = 1
  · refine ⟨-(a : ℤ), ⟨Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨h, hsqZ⟩), by omega⟩, by omega,
      b, by exact_mod_cast hb0, by rw [hDz]; ring⟩
  · rcases Nat.even_or_odd b with ⟨t, ht⟩ | ⟨t, ht⟩
    · have e : -4 * (a : ℤ) / 4 = -(a : ℤ) := by omega
      have ht0 : t ≠ 0 := by rintro rfl; simp at ht; exact hb0 (by exact_mod_cast ht)
      refine ⟨-4 * (a : ℤ), ⟨Int.isFundamentalDiscr_iff_squarefree.mpr
        (Or.inr ⟨by omega, by rwa [e], by omega⟩), by omega⟩, by omega, t, ht0, ?_⟩
      rw [hDz, ht]; push_cast; ring
    · exfalso
      have e : D = -(4 * (((t : ℤ) ^ 2 + t) * a) + a) := by rw [hDz, ht]; push_cast; ring
      generalize ((t : ℤ) ^ 2 + t) * a = s at e
      omega

/-- The discriminant decomposition of a positive definite binary form. -/
theorem exists_fundamental_decomp_of_posDef {f : BinQF} (hf : f.PosDef') :
    ∃ D₀ : ℤ, IsQuadDisc D₀ ∧ D₀ < 0 ∧ ∃ k : ℕ, k ≠ 0 ∧ f.disc = (k : ℤ) ^ 2 * D₀ :=
  exists_fundamental_decomp hf.2 (BinQF.disc_mod_four f)

/-! ### 2. Good-prime densities for $D = k^2D_0$ -/

section Good

variable {D₀ : ℤ} [IsQuadDisc D₀]

theorem not_dvd_D₀ {f : BinQF} {k : ℤ} (hD : f.disc = k ^ 2 * D₀) {p : ℤ} (hpD : ¬ p ∣ f.disc) : ¬ p ∣ D₀ :=
  fun h => hpD (hD ▸ h.mul_left _)

theorem not_dvd_k {f : BinQF} {k : ℤ} (hD : f.disc = k ^ 2 * D₀) {p : ℤ} (hpD : ¬ p ∣ f.disc) : ¬ p ∣ k :=
  fun h => hpD (hD ▸ (Dvd.dvd.mul_right (dvd_pow h two_ne_zero) _))

theorem D₀_mod_four_of_odd {f : BinQF} {k : ℤ} (hD : f.disc = k ^ 2 * D₀) (hpD : ¬ (2 : ℤ) ∣ f.disc) : D₀ % 4 = 1 := by
  have h2 := not_dvd_D₀ hD hpD
  rcases fund_cases (D := D₀) with h | h | h | h | h
  · exact h
  all_goals exact absurd (by omega : (2 : ℤ) ∣ D₀) h2

/-- For odd $D = k^2D_0$: $D \equiv D_0 \pmod 8$ ($k$ odd, $k^2 \equiv 1$). -/
theorem disc_mod_eight {f : BinQF} {k : ℤ} (hD : f.disc = k ^ 2 * D₀) (hpD : ¬ (2 : ℤ) ∣ f.disc) :
    f.disc % 8 = D₀ % 8 := by
  have hk := not_dvd_k hD hpD
  have hk2 : k % 2 = 1 := by omega
  have hk8 : k ^ 2 % 8 = 1 := by
    have : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by omega
    rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
  rw [hD, Int.mul_emod, hk8, one_mul, Int.emod_emod_of_dvd _ (by norm_num)]

/-- **Counts mod $p$ for $p \nmid D$, $D = k^2D_0$** (extension of `repCount_one_good` from fundamental $D$): with
$\chi = \chi_{D_0}(p) = \pm1$, $r_p(m) = p + \chi(p-1)$ if $p \mid m$ and $p - \chi$ otherwise. -/
theorem repCount_one_good_gen (f : BinQF) {k : ℤ} (hD : f.disc = k ^ 2 * D₀) (p : ℕ) [Fact p.Prime]
    (hpD : ¬ (p : ℤ) ∣ f.disc) (m : ℤ) :
    (LocalDensity.repCount f p 1 m : ℤ) = if (p : ℤ) ∣ m then p + kronZ D₀ (p : ZMod D₀.natAbs) * (p - 1)
      else p - kronZ D₀ (p : ZMod D₀.natAbs) := by
  have hpp : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst hp2
    have hpD2 : ¬ (2 : ℤ) ∣ f.disc := by exact_mod_cast hpD
    have hD1 := D₀_mod_four_of_odd hD hpD2
    have h8 := disc_mod_eight hD hpD2
    have hbodd : ¬ (2 : ℤ) ∣ f.b := fun h => hpD2 (by
      rw [BinQF.disc]; obtain ⟨t, ht⟩ := h
      exact ⟨2 * t ^ 2 - 2 * f.a * f.c, by rw [ht]; ring⟩)
    have hb : ((f.b : ℤ) : ZMod 2) = 1 := by
      rw [intCast_zmod_two, ite_eq_right]
      intro h0; exact hbodd (Int.dvd_of_emod_eq_zero h0)
    simp only [Nat.cast_ofNat]
    rw [kronZ_two, ite_eq_left hD1, repCount_eq_card f 2 1 2 (by norm_num) m, hb,
      card2_aux (fun w => (f.a : ZMod 2) * w.1 ^ 2 + 1 * w.1 * w.2 + (f.c : ZMod 2) * w.2 ^ 2 = (m : ZMod 2)),
      kron_two_values]
    have hm2 : ((m : ℤ) : ZMod 2) = 0 ↔ (2 : ℤ) ∣ m := ZMod.intCast_zmod_eq_zero_iff_dvd m 2
    have hac : (f.a : ZMod 2) * (f.c : ZMod 2) = 0 ↔ D₀ % 8 = 1 := by
      rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd, ← h8]
      have : f.disc = f.b ^ 2 - 4 * (f.a * f.c) := by rw [BinQF.disc]; ring
      have hbo : f.b % 2 = 1 := by omega
      have hb8 : f.b ^ 2 % 8 = 1 := by
        have : f.b % 8 = 1 ∨ f.b % 8 = 3 ∨ f.b % 8 = 5 ∨ f.b % 8 = 7 := by omega
        rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
      constructor
      · rintro ⟨t, ht⟩; rw [this, ht]; omega
      · intro h8'
        rw [this] at h8'
        have : (f.a * f.c) % 2 = 0 := by omega
        exact Int.dvd_of_emod_eq_zero this
    simp only [hm2, hac]
    split_ifs <;> norm_num
  · obtain ⟨a, ha, hcount, u, hu, hdet⟩ := Siegel.exists_diag_unimodular_same_counts_det f p hp2
      (by rw [hessian_det_eq_neg_disc]; intro h; exact hpD ((dvd_neg).mp h))
    have hL : legendreSym p ((-1) ^ (2 / 2) * ∏ i, a i) = kronZ D₀ (p : ZMod D₀.natAbs) := by
      rw [kronZ_odd_prime p hp2]
      rw [hessian_det_eq_neg_disc, hD] at hdet
      have hk := not_dvd_k hD hpD
      have hu' : ((u * k : ℤ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
        intro h
        rcases (Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd h with h | h
        · exact hu h
        · exact hk h
      have h2' : ((2 : ℤ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
        intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (by exact_mod_cast h))
      have e : (2 ^ 2) * ((-1) ^ (2 / 2) * ∏ i, a i) = (u * k) ^ 2 * D₀ := by
        simp only [show (2 : ℕ) / 2 = 1 from rfl, pow_one]; linear_combination (-1 : ℤ) * hdet
      have := congrArg (legendreSym p) e
      rw [legendreSym.mul p (2 ^ 2), legendreSym.mul p ((u * k) ^ 2), legendreSym.sq_one' p h2',
        legendreSym.sq_one' p hu', one_mul, one_mul] at this
      exact this
    have hcd := (card_diag_mod_p a p hp2 ha (by norm_num) 1 (by
      intro h; exact hpp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h))).1 even_two
    rw [hL] at hcd
    split_ifs with hm
    · rw [repCount_congr_dvd f p 1 (m' := 0) (by simpa using hm), hcount, hcd.1]
      simp
    · have hcd' := (card_diag_mod_p a p hp2 ha (by norm_num) m hm).1 even_two
      rw [hL] at hcd'
      rw [hcount, hcd'.2]
      simp

/-- **$\beta_p(f, m)$ at a prime $p \nmid D$, $D = k^2D_0$** (extension of `localDensity_good_binary` from fundamental $D$;
$p = 2$ allowed, $m \ne 0$): $\beta_p(f,m) = (1-\chi_{D_0}(p)/p)\sum_{j=0}^{v_p(m)}\chi_{D_0}(p)^j$. -/
@[kb "yang1998" "binary case, p ∤ D, D = k²D₀ [unverified locator]"]
theorem localDensity_good_gen (f : BinQF) {k : ℤ} (hD : f.disc = k ^ 2 * D₀) (p : ℕ) [Fact p.Prime]
    (hpD : ¬ (p : ℤ) ∣ f.disc) (m : ℤ) (hm : m ≠ 0) :
    localDensity f p m = goodFactor (kronZ D₀ (p : ZMod D₀.natAbs)) p (m.natAbs.factorization p) := by
  have hχ : kronZ D₀ (p : ZMod D₀.natAbs) = 1 ∨ kronZ D₀ (p : ZMod D₀.natAbs) = -1 := by
    by_cases hp2 : p = 2
    · subst hp2
      have hD1 := D₀_mod_four_of_odd hD (by exact_mod_cast hpD)
      simp only [Nat.cast_ofNat]
      rw [kronZ_two, ite_eq_left hD1]; split_ifs <;> simp
    · rw [kronZ_odd_prime p hp2]
      exact legendreSym.eq_one_or_neg_one p (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_D₀ hD hpD)
  have hdet : ¬ (p : ℤ) ∣ f.hessian.det := by rw [hessian_det_eq_neg_disc, dvd_neg]; exact hpD
  have := eventually_repCount_good f p hdet _ hχ (repCount_one_good_gen f hD p hpD) _ m rfl hm
  apply limUnder_eq_of_eventually
  filter_upwards [this] with k hk
  rw [show k * (2 - 1) = k by omega]; exact hk

/-- **The good densities on $\mathcal O_\mathbb Q$:** at $\mathfrak p = (p)$, $p \nmid m\,D$,
$\beta_\mathfrak p(f\otimes\mathcal O_\mathbb Q, m) = 1 - \chi_{D_0}(p)/p$. -/
theorem localDensity_up_good_gen {f : BinQF} {k : ℤ} (hD : f.disc = k ^ 2 * D₀) {m : ℤ} (hm : m ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ (Rat.HeightOneSpectrum.natGenerator v : ℤ) ∣ m * f.disc) :
    NF.localDensity v (up f) (m : 𝓞 ℚ) = 1 - kronChi D₀ v / (normP v : ℝ) := by
  set p := Rat.HeightOneSpectrum.natGenerator v
  have : Fact p.Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hpD : ¬ (p : ℤ) ∣ f.disc := fun h => hv (dvd_mul_of_dvd_right h m)
  have hpm : ¬ p ∣ m.natAbs := fun h => hv (dvd_mul_of_dvd_left (Int.natCast_dvd.mpr h) _)
  rw [NF.localDensity_rat, localDensity_good_gen f hD p hpD m hm,
    Nat.factorization_eq_zero_of_not_dvd hpm, goodFactor_zero, normP_rat]
  rfl

theorem dvd_kmD₀ {p : ℕ} (hp : p.Prime) {k m : ℤ} (h : (p : ℤ) ∣ m * (k ^ 2 * D₀)) : (p : ℤ) ∣ k * m * D₀ := by
  have hp' := Nat.prime_iff_prime_int.mp hp
  rcases hp'.dvd_or_dvd h with h1 | h2
  · exact (h1.mul_left k).mul_right D₀
  · rcases hp'.dvd_or_dvd h2 with h3 | h4
    · exact ((hp'.dvd_of_dvd_pow h3).mul_right m).mul_right D₀
    · exact h4.mul_left _

end Good

/-! ### 3. The regularized product for $D = k^2D_0$ -/

section Bridge

variable {D₀ : ℤ} [IsQuadDisc D₀]

/-- **$\chi_Q = \chi_{D_0}$ off a finite set** (for $Q = f\otimes\mathcal O_\mathbb Q$, $f$ positive definite of discriminant
$k^2D_0$): the `chiP · up f` agrees with the Kronecker character `kronChi D₀` outside a finite set of primes (both
$1-\chi(p)/p$ equal $\beta_p(f,m)$ at almost all $p$, for any $m$ represented by $f$ over $\mathbb Q$). -/
theorem chiP_up_eq_kronChi_of_rep {f : BinQF} {k : ℤ} (hD : f.disc = k ^ 2 * D₀) (hk : k ≠ 0)
    (hpd : IsTotallyPosDef (formF (up f))) {m : ℤ} (hm : 1 ≤ m)
    (hrep : ∃ ξ, (formF (up f)).eval ξ = algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v ∉ S, chiP v (up f) = kronChi D₀ v := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hD0 : D₀ ≠ 0 := by have := three_le_natAbs (D := D₀); omega
  have hN : (k * m * D₀).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mul_ne_zero (mul_ne_zero hk hm0) hD0)
  set T := (finite_natGenerator_dvd hN).toFinset
  have hT : ∀ v, v ∉ T → ¬ (Rat.HeightOneSpectrum.natGenerator v : ℤ) ∣ m * f.disc := fun v hv h => by
    rw [hD] at h
    exact hv ((Set.Finite.mem_toFinset _).mpr
      (Int.natCast_dvd.mp (dvd_kmD₀ (Rat.HeightOneSpectrum.prime_natGenerator v) h)))
  obtain ⟨S, hS⟩ := localDensity_eq_one_sub_chiP (up f) hpd (realEmb_intCast_pos hm) hrep
  have hNpos : ∀ v : HeightOneSpectrum (𝓞 ℚ), (normP v : ℝ) ≠ 0 := fun v => by
    have := two_le_normP v; positivity
  refine ⟨S ∪ T, fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  have h1 := (hS v hv.1).symm.trans (localDensity_up_good_gen hD hm0 v (hT v hv.2))
  have h2 : chiP v (up f) / (normP v : ℝ) = kronChi D₀ v / (normP v : ℝ) := by linarith
  rwa [div_left_inj' (hNpos v)] at h2

/-- **$\chi_Q = \chi_{D_0}$ off a finite set, unconditionally** (for every positive definite $f$ of discriminant $k^2D_0$): the
character `chiP · up f` of $\mathbb Q(\sqrt{-\det(H_f/2)}) = \mathbb Q(\sqrt{D_0})$ agrees with the Kronecker character `kronChi D₀`
outside a finite set of primes (`chiP_up_eq_kronChi_of_rep` at $m = a = f(1, 0)$). -/
theorem chiP_up_eq_kronChi {f : BinQF} (hf : f.PosDef') {k : ℤ} (hD : f.disc = k ^ 2 * D₀) (hk : k ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v ∉ S, chiP v (up f) = kronChi D₀ v := by
  have hf' : IntQF.PosDef f := (intQF_posDef_iff _).mpr ((BinQF.posDef_iff_posDef' _).mpr hf)
  refine chiP_up_eq_kronChi_of_rep hD hk ((isTotallyPosDef_up_iff f).mpr hf') (m := f.a) hf.1 ⟨![1, 0], ?_⟩
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.map, Fin.sum_univ_two, BinQF.a]

/-- **The regularized binary product over $\mathbb Q$ for every discriminant** (extension of the
`regProd_up_eq_binaryEulerValue` from fundamental $D$ to $D = k^2D_0$): for $f\otimes\mathcal O_\mathbb Q$ positive definite and an
integer $m \ge 1$ represented by $f$ over $\mathbb Q$,
$$L(1,\chi_f)^{-1}\prod_p\beta_p(f,m)\Bigl(1-\frac{\chi_f(p)}p\Bigr)^{-1} = L(1,\chi_{D_0})^{-1}\prod_{p\mid kmD_0}\frac{\beta_p(f, m)}{1-\chi_{D_0}(p)/p}
\quad(=\texttt{binaryEulerValueNP}\ f\ D_0\ k\ m).$$ -/
@[kb "siegel1935" "§§1–2 (n = 2, regularized product over ℚ, every discriminant) [unverified locator]"]
theorem regProd_up_eq_binaryEulerValueNP {f : BinQF} {k : ℕ} (hk : k ≠ 0) (hD : f.disc = (k : ℤ) ^ 2 * D₀)
    (hpd : IsTotallyPosDef (formF (up f))) {m : ℤ} (hm : 1 ≤ m)
    (hrep : ∃ ξ, (formF (up f)).eval ξ = algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) :
    regProd (fun v => chiP v (up f)) (-1) (fun v => NF.localDensity v (up f) (m : 𝓞 ℚ)) =
      binaryEulerValueNP f D₀ k m := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk
  have hD0 : D₀ ≠ 0 := by have := three_le_natAbs (D := D₀); omega
  have hN : ((k : ℤ) * m * D₀).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mul_ne_zero (mul_ne_zero hk0 hm0) hD0)
  set T := (finite_natGenerator_dvd hN).toFinset
  have hT : ∀ v, v ∉ T → ¬ (Rat.HeightOneSpectrum.natGenerator v : ℤ) ∣ m * f.disc := fun v hv h => by
    rw [hD] at h
    exact hv ((Set.Finite.mem_toFinset _).mpr
      (Int.natCast_dvd.mp (dvd_kmD₀ (Rat.HeightOneSpectrum.prime_natGenerator v) h)))
  obtain ⟨S, hchi⟩ := chiP_up_eq_kronChi_of_rep hD hk0 hpd hm hrep
  set β : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun v => NF.localDensity v (up f) (m : 𝓞 ℚ)
  have hone : ∀ v ∉ T, β v * (1 - kronChi D₀ v / (normP v : ℝ)) ^ (-1 : ℤ) = 1 := fun v hv => by
    simp only [β]
    rw [localDensity_up_good_gen hD hm0 v (hT v hv), _root_.zpow_neg_one,
      mul_inv_cancel₀ (one_sub_div_pos (abs_kronChi_le v) v).ne']
  have hmul : Multipliable fun v => β v * (1 - kronChi D₀ v / (normP v : ℝ)) ^ (-1 : ℤ) :=
    multipliable_of_ne_finset_one hone
  have hL := (hasLOne_kronChi (D := D₀))
  rw [regProd_congr_finite (fun v => abs_chiP_le (up f) v) (fun v => abs_kronChi_le v) S hchi
    (by rw [hL.lOne_eq]; exact hL) (-1) β hmul]
  unfold regProd
  rw [hL.lOne_eq, tprod_eq_prod hone, _root_.zpow_neg_one, binaryEulerValueNP]
  congr 1
  unfold binaryEulerCorrNP
  refine Finset.prod_bij' (fun v _ => Rat.HeightOneSpectrum.natGenerator v)
    (fun p hp => (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨p, Nat.prime_of_mem_primeFactors hp⟩ : Nat.Primes))
    (fun v hv => ?_) (fun p hp => ?_) (fun v _ => ?_) (fun p hp => ?_) (fun v _ => ?_)
  · exact Nat.mem_primeFactors.mpr ⟨Rat.HeightOneSpectrum.prime_natGenerator v,
      (Set.Finite.mem_toFinset (finite_natGenerator_dvd hN)).mp hv, hN⟩
  · refine (Set.Finite.mem_toFinset _).mpr ?_
    show Rat.HeightOneSpectrum.natGenerator _ ∣ _
    rw [natGenerator_primesEquiv_symm (⟨p, Nat.prime_of_mem_primeFactors hp⟩ : Nat.Primes)]
    exact Nat.dvd_of_mem_primeFactors hp
  · exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v
  · exact natGenerator_primesEquiv_symm _
  · simp only [β]
    rw [NF.localDensity_rat, normP_rat, _root_.zpow_neg_one, ← div_eq_mul_inv]
    rfl

/-- **Numbers not represented over $\mathbb Q$:** the classical finite correction vanishes (the zero local density of
`exists_localDensity_eq_zero_of_not_rep` sits at a prime $p \mid mD$, since $\beta_p = 1-\chi_{D_0}(p)/p \ne 0$ at $p \nmid mD$). -/
theorem binaryEulerCorrNP_eq_zero_of_not_rep {f : BinQF} {k : ℕ} (hk : k ≠ 0) (hD : f.disc = (k : ℤ) ^ 2 * D₀)
    (hpd : IsTotallyPosDef (formF (up f))) {m : ℤ} (hm : 1 ≤ m)
    (hrep : ¬ ∃ ξ, (formF (up f)).eval ξ = algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) :
    binaryEulerCorrNP f D₀ k m = 0 := by
  have hm0 : m ≠ 0 := by omega
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk
  have hD0 : D₀ ≠ 0 := by have := three_le_natAbs (D := D₀); omega
  obtain ⟨v, h0⟩ := exists_localDensity_eq_zero_of_not_rep (up f) hpd (realEmb_intCast_pos hm) hrep
  set p := Rat.HeightOneSpectrum.natGenerator v
  have hpv : (p : ℤ) ∣ m * f.disc := by
    by_contra h
    rw [localDensity_up_good_gen hD hm0 v h] at h0
    exact (one_sub_div_pos (abs_kronChi_le v) v).ne' h0
  rw [hD] at hpv
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  have hmem : p ∈ ((k : ℤ) * m * D₀).natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp (dvd_kmD₀ hp hpv),
      Int.natAbs_ne_zero.mpr (mul_ne_zero (mul_ne_zero hk0 hm0) hD0)⟩
  unfold binaryEulerCorrNP
  refine Finset.prod_eq_zero hmem ?_
  rw [NF.localDensity_rat] at h0
  rw [h0, zero_div]

end Bridge

/-! ### 4. The theorem -/

section Main

variable {D₀ : ℤ} [IsQuadDisc D₀]

/-- **The classical binary Siegel formula over $\mathbb Q$ for every positive definite binary form** (unconditional). Let
$f = ax^2+bxy+cy^2$ be a positive definite integral binary form (`f.PosDef'`: $a > 0$, $D = b^2-4ac < 0$), **primitive or not,
of any discriminant**, and write $D = k^2D_0$ with $D_0$ a fundamental discriminant (`IsQuadDisc D₀`) and $k \ge 1$ (such a
decomposition always exists, `exists_fundamental_decomp_of_posDef`). Then for every integer $m \ge 1$
$$r_{\mathrm{gen}}(f, m) = \tfrac12\,\beta_\infty(f, m)\cdot L(1,\chi_{D_0})^{-1}\prod_{p \mid k\,m\,D_0}\frac{\beta_p(f, m)}{1-\chi_{D_0}(p)/p}.$$
* $r_{\mathrm{gen}}(f,m)$ = `Siegel.genusRepAvg f m`: the average of $r_g(m)$ over the $\mathrm{GL}_2(\mathbb Z)$-classes $[g]$ in the genus of
  $f$, weighted by $1/|\mathrm{Aut}(g)|$, $\mathrm{Aut}(g)\subseteq\mathrm{GL}_2(\mathbb Z)$ (improper automorphisms included);
* $\beta_p$ = `LocalDensity.localDensity` at every prime (including $p \mid k$), $\beta_\infty$ = `Siegel.betaInf`, $\chi_{D_0}$ = `kronR D₀`,
  $L(1,\chi_{D_0})$ = `Binary.LOne D₀`;
* the product over $p \mid kmD_0$ is the full product $\prod_p\beta_p(f,m)(1-\chi_{D_0}(p)/p)^{-1}$ (the other factors are $1$).
From `siegelFormulaAt2_nf` at $F = \mathbb Q$; see the module docstring. -/
@[kb "siegel1935" "Hauptsatz, n = 2, over ℚ, every positive definite binary form [unverified locator]"]
theorem siegelFormula_binary_all (f : BinQF) (hf : f.PosDef') {k : ℕ} (hk : k ≠ 0)
    (hD : f.disc = (k : ℤ) ^ 2 * D₀) {m : ℕ} (hm : m ≠ 0) :
    Siegel.genusRepAvg f m = (1 / 2 : ℝ) * Siegel.aEWith f m (binaryEulerValueNP f D₀ k m) := by
  have hf' : IntQF.PosDef f := (intQF_posDef_iff _).mpr ((BinQF.posDef_iff_posDef' _).mpr hf)
  have hpd := (isTotallyPosDef_up_iff f).mpr hf'
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hmass : 0 < Lattices.mass (formF (up f)) (stdLat ℚ 2) := mass_pos hpd _ (isIntegral_stdLat _)
  have H := (siegelFormulaAt2_nf (up f) hpd (realEmb_intCast_pos hm1)).repMass_eq
  have hS : siegelProduct2Reg (up f) ((m : ℤ) : 𝓞 ℚ) = Siegel.aEWith f m
      (regProd (fun v => chiP v (up f)) (-1) (fun v => NF.localDensity v (up f) ((m : ℤ) : 𝓞 ℚ))) := by
    rw [siegelProduct2Reg, siegelProductWith_eq_discr_mul_aEWithNF (isTotPosGram_Q₀ hpd) (by norm_num)
      (realEmb_intCast_pos hm1), discrFactor_rat, one_mul]
    exact Siegel.aEWithNF_rat f m _
  rw [hS, map_intCast] at H
  rw [Siegel.genusRepAvg, mass_rat f hf', repMass_rat f hf', H]
  by_cases hrep : ∃ ξ, (formF (up f)).eval ξ = algebraMap (𝓞 ℚ) ℚ ((m : ℤ) : 𝓞 ℚ)
  · rw [regProd_up_eq_binaryEulerValueNP hk hD hpd hm1 hrep]
    field_simp
  · have h0 := repMass_eq_zero_of_not_rep _ (stdLat ℚ 2) hrep
    rw [map_intCast] at h0
    rw [← H, h0, binaryEulerValueNP, binaryEulerCorrNP_eq_zero_of_not_rep hk hD hpd hm1 hrep, mul_zero,
      Siegel.aEWith, mul_zero, mul_zero, zero_div]

/-- **The same, with the decomposition $D = k^2D_0$ produced** (unconditional): every positive definite binary form $f$ has a
fundamental discriminant $D_0 < 0$ and $k \ge 1$ with $\mathrm{disc}(f) = k^2D_0$, and for all of them and every $m \ge 1$ the
formula of `siegelFormula_binary_all` holds. -/
@[kb "siegel1935" "Hauptsatz, n = 2, over ℚ, every positive definite binary form [unverified locator]"]
theorem siegelFormula_binary_all' (f : BinQF) (hf : f.PosDef') :
    ∃ (D₀ : ℤ) (_ : IsQuadDisc D₀) (k : ℕ), D₀ < 0 ∧ k ≠ 0 ∧ f.disc = (k : ℤ) ^ 2 * D₀ ∧
      ∀ {m : ℕ}, m ≠ 0 →
        Siegel.genusRepAvg f m = (1 / 2 : ℝ) * Siegel.aEWith f m (binaryEulerValueNP f D₀ k m) := by
  obtain ⟨D₀, hQ, hneg, k, hk, hD⟩ := exists_fundamental_decomp_of_posDef hf
  exact ⟨D₀, hQ, k, hneg, hk, hD, fun hm => siegelFormula_binary_all f hf hk hD hm⟩

/-- **Consistency with the earlier binary results (fundamental, primitive):** for $f$ primitive positive definite of
fundamental discriminant $D$
(`PosForms D`), `siegelFormula_binary_all` with $k = 1$ is `siegelFormula_binary` (same right-hand side,
`binaryEulerValueNP_one`). -/
theorem siegelFormula_binary_all_posForms {D : ℤ} [IsQuadDisc D] (f : PosForms D) {m : ℕ} (hm : m ≠ 0) :
    Siegel.genusRepAvg f.1 m = (1 / 2 : ℝ) * Siegel.aEWith f.1 m (binaryEulerValue f.1 D m) := by
  have h := siegelFormula_binary_all f.1 f.2.2.2 (D₀ := D) one_ne_zero (by rw [f.2.2.1]; ring) hm
  rwa [Nat.cast_one, binaryEulerValueNP_one] at h

/-- **Consistency with the earlier binary results (scaled forms):** for $f = c\,g$ with $g$ primitive positive
definite of fundamental discriminant $D$,
`siegelFormula_binary_all` with $k = c$, $D_0 = D$ gives exactly `siegelFormula_binary_nonprim` /
`siegelFormula_binary_posDef` right-hand side `aEWith f m (binaryEulerValueNP f D c m)`. -/
theorem siegelFormula_binary_all_smul {D : ℤ} [IsQuadDisc D] (g : PosForms D) {c : ℕ} (hc : c ≠ 0) {m : ℕ}
    (hm : m ≠ 0) :
    Siegel.genusRepAvg ((c : ℤ) • g.1) m =
      (1 / 2 : ℝ) * Siegel.aEWith ((c : ℤ) • g.1) m (binaryEulerValueNP ((c : ℤ) • g.1) D c m) := by
  have hcpos : (0 : ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hf : ((c : ℤ) • g.1).PosDef' := by
    refine ⟨?_, ?_⟩
    · rw [a_smul]; exact mul_pos hcpos g.2.2.2.1
    · rw [disc_smul]; exact mul_neg_of_pos_of_neg (by positivity) g.2.2.2.2
  exact siegelFormula_binary_all _ hf hc (by rw [disc_smul, g.2.2.1]) hm

end Main

/-! ### 5. Non-fundamental examples: $x^2 + 4y^2$ and $x^2 + 3y^2$ -/

section Examples

/-- $-3$ is a fundamental discriminant. -/
instance isQuadDisc_neg_three : IsQuadDisc (-3) where
  fund := Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨by norm_num, Int.prime_three.neg.squarefree⟩)
  ne_one := by norm_num

/-- **$x^2 + 4y^2$** (discriminant $-16 = 2^2\cdot(-4)$, not fundamental; outside `siegelFormula_binary_posDef`): for every
$m \ge 1$, $r_{\mathrm{gen}}(x^2+4y^2, m) = \tfrac12\beta_\infty\,L(1,\chi_{-4})^{-1}\prod_{p\mid 2m}\beta_p(m)/(1-\chi_{-4}(p)/p)$. -/
theorem siegelFormula_x2_add_4y2 {m : ℕ} (hm : m ≠ 0) :
    Siegel.genusRepAvg (BinQF.mk 1 0 4) m =
      (1 / 2 : ℝ) * Siegel.aEWith (BinQF.mk 1 0 4) m (binaryEulerValueNP (BinQF.mk 1 0 4) (-4) 2 m) :=
  siegelFormula_binary_all _ ⟨by simp, by simp [BinQF.disc]⟩ two_ne_zero (by simp [BinQF.disc]) hm

/-- **$x^2 + 3y^2$** (discriminant $-12 = 2^2\cdot(-3)$, not fundamental): for every $m \ge 1$,
$r_{\mathrm{gen}}(x^2+3y^2, m) = \tfrac12\beta_\infty\,L(1,\chi_{-3})^{-1}\prod_{p\mid 6m}\beta_p(m)/(1-\chi_{-3}(p)/p)$. -/
theorem siegelFormula_x2_add_3y2 {m : ℕ} (hm : m ≠ 0) :
    Siegel.genusRepAvg (BinQF.mk 1 0 3) m =
      (1 / 2 : ℝ) * Siegel.aEWith (BinQF.mk 1 0 3) m (binaryEulerValueNP (BinQF.mk 1 0 3) (-3) 2 m) :=
  siegelFormula_binary_all _ ⟨by simp, by simp [BinQF.disc]⟩ two_ne_zero (by simp [BinQF.disc]) hm

end Examples

end QuadFormsKB.Tamagawa.BinaryAllRat
