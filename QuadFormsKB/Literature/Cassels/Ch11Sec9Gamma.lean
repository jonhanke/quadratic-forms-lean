/-
# Cassels, Chapter 11, §9: property $(\gamma)$ of the proof of Theorem 1.6 for $n \ge 5$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Theorem 1.6 for $n \ge 5$,
p. 240 (the choice of the special prime $q$, (9.19), and the derivation of $(\gamma)$ from Theorem 8.3). Companion to
`Ch11Sec9Steps.lean`, which has the properties $(\alpha)$–$(\delta)$ (`FamilyProps`) and the named statement
`Thm16MainStep`.

**Conventions.** As in `Ch11Sec9Steps.lean`: $n = m + 2$, the form $h = h^\psi$ has $m \ge 3$ variables; Cassels'
$d(h)$ enters only through "$q \nmid d(h)$", read as $q \nmid \det H_h$ for the Hessian $H_h$ (the same condition for
$q \ne 2$). The genus of $h$ "consists of one spinor genus" is read for the standard lattice $\mathbb Z^m$ on
$(\mathbb Q^m, h)$ with *proper* spinor genera (`GenusOneSpinorGenus`), as in `Lattices.exists_pow_represents_of_isotropic`.

**Proves.**
* `exists_gammaHolds`: Cassels' derivation of $(\gamma)$ (p. 240): if $h$ is positive definite in $m \ge 3$ variables,
  $q$ is an odd prime with $q \nmid \det H_h$, and (only when $m = 3$) the genus of $h$ is one spinor genus, then there
  is $k_0$ such that $(\gamma)$ holds for $h$, $q$ and every exponent $k \ge k_0$ (and every finite $P \not\ni q$).
  *Update (as for the Corollary to Theorem 8.3):* the Corollary as printed is not quite
  what its proof gives; here it is applied to $b = c/q^{2k_0}$, which is represented over $\mathbb Z_q$ because $h$ is
  unimodular at $q$ of rank $\ge 3$ (Cassels' (ε): $h$ represents all of $\mathbb Z_q$), so the printed $(\gamma)$ holds.
  For $m \ge 4$ no spinor genus hypothesis is needed (`Lattices.exists_pow_represents_of_isotropic_four`).
* `thm16MainStep_of_familyStep`: the named statement `Thm16MainStep` follows from the smaller named statement
  `Thm16FamilyStep`, which no longer contains $(\gamma)$; and Theorem 1.6 for $n \ge 5$ from it
  (`tartakowskyAt_of_familyStep`).

**Named statement (not proved).** `Thm16FamilyStep`: the construction of pp. 237–241 of the family $\Psi$ with
(9.3)–(9.5), $(\alpha)$, $(\beta)$, the special prime $q$ of (9.19) and $(\delta)$ for every exponent, plus (for $m = 3$
only) the one-spinor-genus property that Cassels obtains from (9.11) and Lemma 3.6, Corollary.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec9Steps
import QuadFormsKB.Literature.Cassels.Ch11Sec8Rep
import QuadFormsKB.Literature.Cassels.Ch9Sec5

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Sec9Gamma

open QuadFormsKB.Cassels QuadFormsKB.Cassels.Ch11Sec9Steps QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **"The genus of $h$ consists of one (proper) spinor genus"** (Cassels, Ch. 11, p. 240, from (9.11) and Lemma 3.6,
Corollary): every lattice of the genus of the standard lattice $\mathbb Z^m$ on $(\mathbb Q^m, h)$ is in its proper spinor
genus. Argument: `h` the integer form. -/
def GenusOneSpinorGenus {m : ℕ} (h : QuadForm ℤ m) : Prop :=
  ∀ M : Lat ℚ m, SameGenus (h.map (Int.castRingHom ℚ)) (stdLat : Lat ℚ m).1 M.1 →
    SameProperSpinorGenus (h.map (Int.castRingHom ℚ)) stdLat M

/-- Helper: evaluation over a ring is evaluation of the base change. -/
theorem evalIn_eq_map_eval {m : ℕ} (h : QuadForm ℤ m) {A : Type*} [CommRing A] (x : Fin m → A) :
    h.evalIn A x = (h.map (Int.castRingHom A)).eval x := by
  simp [QuadForm.evalIn, QuadForm.map, QuadForm.eval]

/-- **Helper: dividing a local representation by a square of a unit power.** If $q^{2k}b$ is represented by $h$ over
$\mathbb Z_p$ for every $p$, $q$ is an odd prime with $q \nmid \det H_h$ and $h$ has $m \ge 3$ variables, then $b$ is
represented by $h$ over every $\mathbb Z_p$: for $p \ne q$ divide by the unit $q^k$; for $p = q$ use that $h$ is unimodular
at $q$ (`Lattices.exists_primitive_padic_of_unimodular`). Arguments: `h` the form, `q` the prime, `k` the exponent,
`b` the integer. -/
theorem padic_rep_of_pow_mul {m : ℕ} (h : QuadForm ℤ m) (hm : 3 ≤ m) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (hdet : ¬ (q : ℤ) ∣ h.hessian.det) (k : ℕ) (b : ℤ) (hc : RepZpAll h ((q : ℤ) ^ (2 * k) * b))
    (p : ℕ) [Fact p.Prime] : ∃ x : Fin m → ℤ_[p], (h.map (Int.castRingHom ℤ_[p])).eval x = b := by
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨x, -, hx⟩ := exists_primitive_padic_of_unimodular p hq2 h hdet hm b
    exact ⟨x, hx⟩
  · obtain ⟨x, hx⟩ := hc p
    have hqu : IsUnit ((q : ℤ_[p])) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) ?_
      by_contra hlt
      push Not at hlt
      have h1 : ‖((q : ℤ) : ℤ_[p])‖ < 1 := by exact_mod_cast hlt
      have h2 := (PadicInt.norm_int_lt_one_iff_dvd (q : ℤ)).mp h1
      have h3 : p ∣ q := by exact_mod_cast h2
      exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h3)
    obtain ⟨u, hu⟩ := hqu
    refine ⟨fun j => ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ k * x j, ?_⟩
    rw [← evalIn_eq_map_eval, LocalDensity.evalIn_const_mul, hx]
    have e : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ k) ^ 2 * ((q : ℤ_[p])) ^ (2 * k) = 1 := by
      rw [← hu]
      have hg : ((u⁻¹ ^ k) ^ 2 * u ^ (2 * k) : ℤ_[p]ˣ) = 1 := by group
      have h1 := congrArg Units.val hg
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        Units.val_one] at h1
      rw [pow_mul] at h1 ⊢
      exact h1
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [← mul_assoc, e, one_mul]

/-- **Helper: a positive definite form represents every positive integer over $\mathbb R$.** Arguments: `h` the form,
`hm` $m \ge 1$, `b` the integer. -/
theorem exists_real_rep {m : ℕ} (h : QuadForm ℤ m) (hpd : IntQF.PosDef h) (hm : 1 ≤ m) (b : ℤ) (hb : 0 < b) :
    ∃ x : Fin m → ℝ, h.evalIn ℝ x = b := by
  set e : Fin m → ℤ := Pi.single ⟨0, hm⟩ 1 with he
  have he0 : e ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hm⟩
    simp [he] at this
  have ha : 0 < h.eval e := hpd e he0
  have haR : (0 : ℝ) < (h.eval e : ℝ) := by exact_mod_cast ha
  refine ⟨Real.sqrt ((b : ℝ) / (h.eval e : ℝ)) • (fun i => ((e i : ℤ) : ℝ)), ?_⟩
  rw [Siegel.Kneser.evalIn_smul_gen, Siegel.evalIn_intCast, Real.sq_sqrt (by positivity)]
  field_simp

/-- Helper: the rational base change of `h` evaluated on an integer vector. -/
theorem evalIn_rat_intCast {m : ℕ} (h : QuadForm ℤ m) (w : Fin m → ℤ) :
    (h.map (Int.castRingHom ℚ)).evalIn ℚ (fun i => (w i : ℚ)) = (h.eval w : ℚ) := by
  rw [evalIn_castHom_rat, ← evalIn_eq_map_eval, Siegel.evalIn_intCast]

/-- **Property $(\gamma)$ from Theorem 8.3** (Cassels, Ch. 11, p. 240: "Hence by Theorem 8.3 there is an integer $m > 0$
with the following property: if $c \in \mathbb Z$, $c \ne 0$ is divisible by $q^{2m}$ and it representable by $h$ over every
$\mathbb Z_p$ (including $\mathbb Z_\infty = \mathbb R$) then $c$ is representable by $h$ over $\mathbb Z$"). Let $h$ be a
positive definite integral form in $m \ge 3$ variables and $q$ an odd prime with $q \nmid \det H_h$; if $m = 3$ assume
that the genus of $h$ is one spinor genus. Then there is $k_0$ such that `GammaHolds P h q k` for every $k \ge k_0$ and every
finite set $P$ of primes not containing $q$. (Positivity of $c$ replaces representability over $\mathbb R$.) Arguments:
`h` the form, `q` the prime, `hspn` the spinor genus hypothesis for $m = 3$. -/
@[kb "cassels1978" "Ch. 11, proof of Thm. 1.6 (n ≥ 5), (γ) from Thm. 8.3, p. 240"]
theorem exists_gammaHolds {m : ℕ} (h : QuadForm ℤ m) (hpd : IntQF.PosDef h) (hm : 3 ≤ m) (q : ℕ) (hq : q.Prime)
    (hq2 : q ≠ 2) (hdet : ¬ (q : ℤ) ∣ h.hessian.det) (hspn : m = 3 → GenusOneSpinorGenus h) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ P : Finset ℕ, q ∉ P → GammaHolds P h q k := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  set Qh := h.map (Int.castRingHom ℚ) with hQh
  have hQ : Qh.Nondegenerate := nondegenerate_map_of_det_ne_zero h (IntQF.PosDef.nondegenerate hpd)
  set qv : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩ with hqv
  have hgen : (Rat.HeightOneSpectrum.primesEquiv qv : ℕ) = q := by
    exact congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨q, hq⟩)
  have hgen' : Rat.HeightOneSpectrum.natGenerator qv = q := hgen
  -- isotropy at q
  have hiso : Qh.IsotropicIn (qv.adicCompletion ℚ) := by
    obtain ⟨x, ⟨i, hi⟩, hx⟩ := exists_primitive_padic_of_unimodular q hq2 h hdet hm 0
    refine isotropicIn_adicCompletion_of_padic Qh qv q hgen.symm ⟨fun j => (x j : ℚ_[q]), ?_, ?_⟩
    · intro h0
      have h1 := congrFun h0 i
      simp only [Pi.zero_apply, PadicInt.coe_eq_zero] at h1
      exact hi.ne_zero h1
    · rw [evalIn_castHom_rat]
      have := hom_eval_castHom h PadicInt.Coe.ringHom x
      rw [hx] at this
      simpa using this.symm
  -- Theorem 8.3, Corollary
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ∀ c : ℚ, c ≠ 0 → (∃ x : Fin m → ℚ, Qh.evalIn ℚ x = c) →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ y ∈ loc v (stdLat : Lat ℚ m).1,
        Qh.evalIn (v.adicCompletion ℚ) y = algebraMap ℚ (v.adicCompletion ℚ) c) →
      ∃ z ∈ (stdLat : Lat ℚ m).1, Qh.evalIn ℚ z = (Rat.HeightOneSpectrum.natGenerator qv : ℚ) ^ (2 * k₀) * c := by
    by_cases hm3 : m = 3
    · exact exists_pow_represents_of_isotropic Qh hQ hm qv hiso stdLat (hspn hm3)
    · exact exists_pow_represents_of_isotropic_four Qh hQ (by omega) qv hiso stdLat
  refine ⟨k₀, fun k hk P _ => ⟨hq, by assumption, fun c hc hdvd hrep => ?_⟩⟩
  have hdvd₀ : (q : ℤ) ^ (2 * k₀) ∣ c := (pow_dvd_pow _ (by omega)).trans hdvd
  obtain ⟨b, rfl⟩ := hdvd₀
  have hqpos : (0 : ℤ) < (q : ℤ) ^ (2 * k₀) := by have := hq.pos; positivity
  have hb : 0 < b := pos_of_mul_pos_right hc hqpos.le
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hlocb := padic_rep_of_pow_mul h hm q hq2 hdet k₀ b hrep
  have hloc' : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ y ∈ loc v (stdLat : Lat ℚ m).1,
      Qh.evalIn (v.adicCompletion ℚ) y = algebraMap ℚ (v.adicCompletion ℚ) (b : ℚ) := by
    intro v
    obtain ⟨p, hpdef⟩ : ∃ p : ℕ, (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := ⟨_, rfl⟩
    have : Fact p.Prime := ⟨hpdef ▸ (Rat.HeightOneSpectrum.primesEquiv v).2⟩
    obtain ⟨y, hy, h'⟩ := exists_mem_std_of_padic h v p hpdef (hlocb p)
    refine ⟨y, ?_, h'⟩
    change y ∈ loc v intVec
    rw [loc_intVec]
    exact hy
  have hrat : Qh.RepresentsIn ℚ (b : ℚ) := by
    rw [represents_iff_everywhere_nf _ hQ _ hb0]
    intro w
    cases w with
    | infinite w =>
      exact representsIn_congr_alg _ _ _ _
        (representsIn_inf_of_real h (exists_real_rep h hpd (by omega) b hb) w)
    | finite v =>
      obtain ⟨y, -, hy⟩ := hloc' v
      exact ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hrat
  obtain ⟨z, hz, hzc⟩ := hk₀ b hb0 ⟨x, by simpa using hx⟩ hloc'
  obtain ⟨y, rfl⟩ := mem_intVec_iff_exists.mp hz
  refine ⟨fun i => Tamagawa.RatBridge.eZ (y i), ?_⟩
  have hcast : (fun i => ((Tamagawa.RatBridge.eZ (y i) : ℤ) : ℚ)) = intCoe y := by
    funext i
    exact eZ_cast_eq (y i)
  have := evalIn_rat_intCast h (fun i => Tamagawa.RatBridge.eZ (y i))
  rw [hcast, hzc, hgen'] at this
  exact_mod_cast this.symm

/-! ### The smaller named statement -/

/-- **The properties of the family $\Psi$ other than $(\gamma)$** (Cassels, Ch. 11, pp. 236–240), for the form `f` in
$m + 2$ variables and the finite set `P` of primes. Fields: `split` (9.3)–(9.5); `alpha` $(\alpha)$; `beta` $(\beta)$;
`special`: for each $\psi \in \Psi$ a prime $q \notin P$ with $q \nmid \det H_{h^\psi}$ ((9.19)), with the genus of
$h^\psi$ one spinor genus when $m = 3$ (Cassels: by (9.11) and Lemma 3.6, Corollary), and $(\delta)$ for every
exponent $k$ (Cassels' construction of $B$, p. 240–241, works for any $k$: condition $C_4$ uses only (9.20)). -/
structure FamilyPropsABD {m : ℕ} (f : QuadForm ℤ (m + 2)) (P : Finset ℕ) (Ψ : Finset (Subst m)) : Prop where
  /-- (9.3)–(9.5) for every member of the family. -/
  split : ∀ ψ ∈ Ψ, IsSplitting f ψ
  /-- Property $(\alpha)$. -/
  alpha : ∀ a : ℤ, PrimRepZpOn P f a → ∃ ψ ∈ Ψ, PrimRepZpOn P ψ.g a
  /-- Property $(\beta)$. -/
  beta : ∀ ψ ∈ Ψ, ∀ (b₀ b₁ : ℤ) (z : Fin m → ℤ), Int.gcd b₀ b₁ = 1 →
    Finset.univ.gcd (ψ.S *ᵥ joinVec b₀ b₁ z) = 1
  /-- The special prime (9.19), one spinor genus for $m = 3$, and $(\delta)$ for every exponent. -/
  special : ∀ ψ ∈ Ψ, ∃ q : ℕ, q.Prime ∧ q ∉ P ∧ ¬ (q : ℤ) ∣ ψ.h.hessian.det ∧
    (m = 3 → GenusOneSpinorGenus ψ.h) ∧ ∀ k : ℕ, DeltaHolds P ψ q k

/-- **The construction of the proof of Theorem 1.6 for $n \ge 5$ without $(\gamma)$** (Cassels, Ch. 11, pp. 237–241), named
statement: for every positive definite integral form $f$ in $n = m + 2 \ge 5$ variables and every finite set $P$ of primes
with $2 \in P$ containing every prime dividing $\det H_f$, there is a finite family $\Psi$ with `FamilyPropsABD`. It is
`Thm16MainStep` with $(\gamma)$ replaced by its hypotheses ((9.19) and, for $m = 3$, one spinor genus); $(\gamma)$ itself
is proved (`exists_gammaHolds`). *Not proved:* the local discussion at $p \in P$, the lattice $\Gamma$ with prescribed
localizations (Chapter 9, Theorem 1.1; Lemma 3.6, Corollary), the choice of $q$, and the compactness covering for
$(\delta)$. -/
@[kb "cassels1978" "Ch. 11, proof of Thm. 1.6 for n ≥ 5, construction of Ψ: (α), (β), (δ), (9.19), (9.11), pp. 237–241"]
structure Thm16FamilyStep : Prop where
  /-- The family of substitutions exists. -/
  holds : ∀ m : ℕ, 3 ≤ m → ∀ f : QuadForm ℤ (m + 2), IntQF.PosDef f → ∀ P : Finset ℕ,
    (∀ p ∈ P, p.Prime) → 2 ∈ P → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ f.hessian.det → p ∈ P) →
    ∃ Ψ : Finset (Subst m), FamilyPropsABD f P Ψ

/-- Helper: the form $h^\psi$ of a splitting of a positive definite form is positive definite ($h^\psi(z) = f(\psi(0, 0, z))$,
$\psi$ injective). -/
theorem posDef_h_of_split {m : ℕ} {f : QuadForm ℤ (m + 2)} (hpd : IntQF.PosDef f) {ψ : Subst m}
    (hs : IsSplitting f ψ) : IntQF.PosDef ψ.h := by
  intro z hz
  have e := hs.2 0 0 z
  have hg0 : ψ.g.eval ![0, 0] = 0 := by
    simp [QuadForm.eval, QuadForm.evalIn]
  rw [hg0, zero_add] at e
  rw [← e]
  refine hpd _ fun h0 => hz ?_
  have := Matrix.eq_zero_of_mulVec_eq_zero hs.1 h0
  funext i
  have hi := congrFun this i.succ.succ
  simpa [joinVec] using hi

/-- **`Thm16MainStep` from the smaller named statement** (Cassels, Ch. 11, p. 240): property $(\gamma)$ is supplied by
`exists_gammaHolds` (the exponent $k_0$ it gives, with $(\delta)$ at that exponent). Argument: `H` the named statement. -/
@[kb "cassels1978" "Ch. 11, proof of Thm. 1.6 for n ≥ 5, (γ) via Thm. 8.3, p. 240"]
theorem thm16MainStep_of_familyStep (H : Thm16FamilyStep) : Thm16MainStep := by
  refine ⟨fun m hm f hpd P hPp hP2 hPd => ?_⟩
  obtain ⟨Ψ, hΨ⟩ := H.holds m hm f hpd P hPp hP2 hPd
  refine ⟨Ψ, hΨ.split, hΨ.alpha, hΨ.beta, fun ψ hψ => ?_⟩
  obtain ⟨q, hq, hqP, hdet, hspn, hδ⟩ := hΨ.special ψ hψ
  have hq2 : q ≠ 2 := fun h2 => hqP (h2 ▸ hP2)
  obtain ⟨k₀, hk₀⟩ := exists_gammaHolds ψ.h (posDef_h_of_split hpd (hΨ.split ψ hψ)) hm q hq hq2 hdet hspn
  exact ⟨q, k₀, hk₀ k₀ le_rfl P hqP, hδ k₀⟩

/-- **Theorem 1.6 for every $n \ge 5$ from the smaller named statement** (Cassels, Ch. 11, pp. 236–241). Arguments: `H` the
named statement, `n` the dimension, `hn` the bound $5 \le n$. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.6 for n ≥ 5, pp. 236–241"]
theorem tartakowskyAt_of_familyStep (H : Thm16FamilyStep) (n : ℕ) (hn : 5 ≤ n) : TartakowskyAt n :=
  tartakowskyAt_of_main_step' (thm16MainStep_of_familyStep H) n hn

end QuadFormsKB.Cassels.Ch11Sec9Gamma
