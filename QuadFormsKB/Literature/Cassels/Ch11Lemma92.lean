/-
# Cassels, Chapter 11, Lemma 9.2: the final stage of the proof

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Lemma 9.2 (pp. 245–249), final
stage (p. 248: "Now let $a \in \mathbb Z$ be given … one then completes the proof of Lemma 9.2 by showing that a finite
set of $b$ will cover all values of $a$").

**Conventions.** $f$ is a positive definite quaternary form `QuadForm ℤ 4`, $q$ an odd prime. Indices are 0-based. A vector
$x \in \mathbb Z^m$ is *primitive at $p$* (`PrimAt p x`) when not all coordinates are divisible by $p$; it is primitive
(greatest common divisor $1$) iff it is primitive at every prime (`gcd_eq_one_iff_forall_primAt`). `placeOf p` is the place
of $\mathbb Q$ over the prime $p$.

**The data of the final stage** (`L92Datum f q`): Cassels' vector $\mathbf u$ (the $1$-dimensional form
$g(y) = f(\mathbf u)y^2$), a $4 \times 3$ integer matrix $W$ (coordinates on $V^{(2)} = \mathbf u^\perp$, in practice a basis
of $\mathbb Z^4 \cap \mathbf u^\perp$), the ternary form $h(z) = f(Wz)$, and Cassels' lattice $\Gamma$ as a lattice `L` on
$(\mathbb Q^3, h)$ contained in $\mathbb Z^3$, with:
* `split`: $f(b\mathbf u + Wz) = f(\mathbf u)b^2 + h(z)$ (so $\Gamma \perp \mathbf u$);
* `spn`: the genus of $\Gamma$ consists of one proper spinor genus (Cassels (9.60) and Lemma 3.6, Corollary);
* `iso_q`, `rep_q`: $\Gamma_q$ is isotropic and represents every integer (Cassels' case (d) for $p = q$);
* a finite set $S$ of primes (Cassels' $P^* = P \cup \{q, \pi, p(0)\}$) outside which $\Gamma_p$ primitively represents
  every integer (`rep_out`) and $b\mathbf u + Wz$ is primitive whenever $z$ is primitive in $\Gamma_p$ (`prim_out`,
  Cassels' (9.44) in case (d)).

**Proves.**
* `exists_rep_primitive_lat`: the Corollary of Theorem 8.3 for $\Gamma$, with primitivity at a given set of places
  (`Lattices.exists_pow_represents_primitive` for integers).
* `exists_bound_of_family`: Cassels' final stage. Given a finite family of data such that for every exponent $k$ and every
  $a$ (prime to $q$, primitively represented by $f$ over every $\mathbb Z_p$) one of finitely many $b$ makes
  $c = a - f(\mathbf u)b^2$ divisible by $q^{2k}$, represented by $\Gamma_p$ for $p \in S$, and such that one of
  $b\mathbf u \pm Wz$ is primitive at the primes of $S$ whenever $z \in \Gamma$, $h(z) = c$ (`LocalOK`; the sign is
  Cassels' "on replacing $\mathbf c$ by $-\mathbf c$ if need be" at $p = p(0)$), $\mathcal R(f, a)$ holds for all $a > N$
  with $q \nmid a$.
* `lemma92_of_family`: Lemma 9.2 from the named statement `Lemma92FamilyStatement` (the existence of such a family).

**Named statement (not proved here).** `Lemma92FamilyStatement`: the construction of pp. 245–248 (local vectors, the
auxiliary primes $\pi$ and $p(0)$, the vector $\mathbf u$ by Theorem 8.1, the lattice $\Gamma$ by its localizations in the
cases (a)–(d), and the choice of $b$).
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92Prim
import QuadFormsKB.Literature.Cassels.Ch11Sec9Gamma
import QuadFormsKB.Literature.Cassels.Ch11Sec4Local
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm
import QuadFormsKB.Literature.Cassels.Ch11Sec7Lemma

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

open QuadFormsKB.Cassels QuadFormsKB.Lattices QuadFormsKB.Cassels.Ch11Sec9Gamma

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-! ### Primitivity at a prime -/

/-- **$x \in \mathbb Z^m$ is primitive at the prime $p$:** not every coordinate is divisible by $p$. Arguments: `p` the
prime, `x` the vector. -/
def PrimAt {m : ℕ} (p : ℕ) (x : Fin m → ℤ) : Prop := ¬ ∀ i, (p : ℤ) ∣ x i

/-- **A vector has coprime coordinates iff it is primitive at every prime.** -/
theorem gcd_eq_one_iff_forall_primAt {m : ℕ} (x : Fin m → ℤ) :
    Finset.univ.gcd x = 1 ↔ ∀ p : ℕ, p.Prime → PrimAt p x := by
  rw [gcd_eq_one_iff_forall_dvd]
  constructor
  · intro h p hp hdiv
    have := h p hdiv
    rw [Int.isUnit_iff] at this
    rcases this with h1 | h1
    · exact hp.one_lt.ne' (by exact_mod_cast h1)
    · have : (0 : ℤ) ≤ p := by positivity
      omega
  · intro h e he
    by_contra hu
    have hne : e.natAbs ≠ 1 := by
      intro h1
      exact hu (Int.isUnit_iff_natAbs_eq.mpr h1)
    set p := e.natAbs.minFac
    have hp : p.Prime := Nat.minFac_prime hne
    apply h p hp
    intro i
    have h1 : (p : ℤ) ∣ e := Int.natCast_dvd.mpr (Nat.minFac_dvd _)
    exact h1.trans (he i)

theorem primAt_neg {m : ℕ} {p : ℕ} {x : Fin m → ℤ} : PrimAt p (-x) ↔ PrimAt p x := by
  unfold PrimAt
  simp only [Pi.neg_apply, dvd_neg]

/-- Helper: the place of $\mathcal O_{\mathbb Q}$ over the prime $p$. -/
def placeOf (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

theorem natGenerator_placeOf (p : ℕ) (hp : p.Prime) : Rat.HeightOneSpectrum.natGenerator (placeOf p hp) = p :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩)

theorem placeOf_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    placeOf (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v) = v :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v

/-- **A primitive vector of $(\mathbb Z^m)_v$ is primitive at $p$:** if the integer vector $w$ is primitive in
$\mathfrak o_v^m$ ($v$ the place over $p$), then not all coordinates of $w$ are divisible by $p$. -/
theorem primAt_of_locPrimitive {m : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) (w : Fin m → ℤ)
    (h : LocPrimitive v (std v) (locVec v (fun i => (w i : ℚ)))) :
    PrimAt (Rat.HeightOneSpectrum.natGenerator v) w := by
  intro hdiv
  choose w' hw' using hdiv
  set p := Rat.HeightOneSpectrum.natGenerator v
  have hp0 : ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
    intro h0
    have := valued_natGenerator v
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hmem : ((p : v.adicCompletion ℚ))⁻¹ • locVec v (fun i => (w i : ℚ)) ∈ std v := by
    intro i
    have e : (((p : v.adicCompletion ℚ))⁻¹ • locVec v (fun i => (w i : ℚ))) i =
        ((w' i : ℤ) : v.adicCompletion ℚ) := by
      simp only [Pi.smul_apply, smul_eq_mul, locVec_apply, hw' i]
      push_cast
      field_simp
      simp
    rw [e]
    simpa using valued_intCast_le_one' v (w' i)
  have h1 := h.2 _ hmem
  rw [map_inv₀, valued_natGenerator v] at h1
  have : (1 : WithZero (Multiplicative ℤ)) < (WithZero.exp (-1 : ℤ))⁻¹ := by
    rw [← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  exact absurd h1 (not_le.mpr this)

/-! ### The Corollary of Theorem 8.3 for $\Gamma$, primitive at a set of places -/

/-- Helper: a vector of a lattice contained in $\mathbb Z^3$ is an integer vector. -/
theorem exists_int_of_mem {L : Lat ℚ 3} (hL : L.1 ≤ intVec) {z : Fin 3 → ℚ} (hz : z ∈ L.1) :
    ∃ zz : Fin 3 → ℤ, (fun i => (zz i : ℚ)) = z := by
  obtain ⟨yz, rfl⟩ := mem_intVec_iff_exists.mp (hL hz)
  exact ⟨fun i => Tamagawa.RatBridge.eZ (yz i), funext fun i => eZ_cast_eq (yz i)⟩

/-- Helper: scaling a local vector by the unit $q^{-k}$ ($v \ne q$). -/
theorem valued_pow_inv_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {q : ℕ} (hq : q.Prime)
    (hv : v ≠ placeOf q hq) (k : ℕ) : Valued.v (((q : v.adicCompletion ℚ) ^ k)⁻¹) = 1 := by
  have hnd : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ q ^ k := by
    intro hd
    have hpv := Rat.HeightOneSpectrum.prime_natGenerator v
    have h1 := (Nat.prime_dvd_prime_iff_eq hpv hq).mp (hpv.dvd_of_dvd_pow hd)
    apply hv
    rw [← placeOf_natGenerator v]
    congr 1
  have := valued_natCast_eq_one' (v := v) hnd
  rw [map_inv₀]
  push_cast at this
  rw [this, inv_one]

/-- **Cassels, Theorem 8.3, Corollary, for $\Gamma$, primitive at a set of places** (Ch. 11, p. 233, as used on p. 248).
Let $h$ be a positive definite integral ternary form, $L$ a lattice on $(\mathbb Q^3, h)$ contained in $\mathbb Z^3$ whose
genus is one proper spinor genus, and $q$ a prime at which $L_q$ is isotropic and represents every integer. Then there
is $k_0$ such that every $c > 0$ divisible by $q^{2k_0}$ and represented by $L_v$ at every place $v \ne q$ is $h(z)$ for some
$z \in L$, primitive in $L_v$ at every place $v$ of a given set $T \not\ni q$ at which $c$ is primitively represented by
$L_v$. -/
theorem exists_rep_primitive_lat (h : QuadForm ℤ 3) (hpd : IntQF.PosDef h) {q : ℕ} (hq : q.Prime)
    (L : Lat ℚ 3) (hL : L.1 ≤ intVec)
    (hspn : ∀ M : Lat ℚ 3, SameGenus (h.map (Int.castRingHom ℚ)) L.1 M.1 →
      SameProperSpinorGenus (h.map (Int.castRingHom ℚ)) L M)
    (hiso : (h.map (Int.castRingHom ℚ)).IsotropicIn ((placeOf q hq).adicCompletion ℚ))
    (hrepq : ∀ c : ℤ, ∃ y ∈ loc (placeOf q hq) L.1,
      (h.map (Int.castRingHom ℚ)).evalIn _ y = algebraMap ℚ _ (c : ℚ)) :
    ∃ k₀ : ℕ, ∀ c : ℤ, 0 < c → (q : ℤ) ^ (2 * k₀) ∣ c →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ placeOf q hq →
        ∃ y ∈ loc v L.1, (h.map (Int.castRingHom ℚ)).evalIn _ y = algebraMap ℚ _ (c : ℚ)) →
      ∀ T : HeightOneSpectrum (𝓞 ℚ) → Prop, (∀ v, T v → v ≠ placeOf q hq ∧
        ∃ y, LocPrimitive v (loc v L.1) y ∧ (h.map (Int.castRingHom ℚ)).evalIn _ y = algebraMap ℚ _ (c : ℚ)) →
      ∃ z : Fin 3 → ℤ, (fun i => (z i : ℚ)) ∈ L.1 ∧ h.eval z = c ∧
        ∀ v, T v → LocPrimitive v (loc v L.1) (locVec v (fun i => (z i : ℚ))) := by
  classical
  set Qh := h.map (Int.castRingHom ℚ) with hQh
  have hQ : Qh.Nondegenerate := nondegenerate_map_of_det_ne_zero h (IntQF.PosDef.nondegenerate hpd)
  set qv := placeOf q hq with hqv
  have hgen' : Rat.HeightOneSpectrum.natGenerator qv = q := natGenerator_placeOf q hq
  obtain ⟨k₀, hk₀⟩ := exists_pow_represents_primitive Qh hQ le_rfl qv hiso L hspn
  refine ⟨k₀, fun c hc hdvd hrep T hT => ?_⟩
  obtain ⟨b, rfl⟩ := hdvd
  have hqpos : (0 : ℤ) < (q : ℤ) ^ (2 * k₀) := by have := hq.pos; positivity
  have hb : 0 < b := pos_of_mul_pos_right hc hqpos.le
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  -- local representations of `b`
  have hlocb : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ y ∈ loc v L.1,
      Qh.evalIn (v.adicCompletion ℚ) y = algebraMap ℚ (v.adicCompletion ℚ) (b : ℚ) ∧
      (T v → LocPrimitive v (loc v L.1) y) := by
    intro v
    by_cases hvq : v = qv
    · subst hvq
      obtain ⟨y, hy, hyb⟩ := hrepq b
      exact ⟨y, hy, hyb, fun hTv => absurd rfl (hT _ hTv).1⟩
    · set t : v.adicCompletion ℚ := ((q : v.adicCompletion ℚ) ^ k₀)⁻¹ with ht
      have htv : Valued.v t = 1 := valued_pow_inv_eq_one hq hvq k₀
      have hval : ∀ y : Fin 3 → v.adicCompletion ℚ,
          Qh.evalIn (v.adicCompletion ℚ) y = algebraMap ℚ _ (((q : ℤ) ^ (2 * k₀) * b : ℤ) : ℚ) →
          Qh.evalIn (v.adicCompletion ℚ) (t • y) = algebraMap ℚ _ (b : ℚ) := by
        intro y hy
        rw [evalIn_smul', hy, ht]
        have hq0 : (q : v.adicCompletion ℚ) ≠ 0 := by
          intro h0
          have := valued_pow_inv_eq_one hq hvq 1
          rw [pow_one, h0, _root_.inv_zero, map_zero] at this
          exact zero_ne_one this
        push_cast
        field_simp
        ring
      by_cases hTv : T v
      · obtain ⟨-, y, hy, hyc⟩ := hT v hTv
        exact ⟨t • y, smul_mem_of_valued_le_one' hy.1 htv.le, hval y hyc, fun _ => hy.smul_unit htv⟩
      · obtain ⟨y, hy, hyc⟩ := hrep v hvq
        exact ⟨t • y, smul_mem_of_valued_le_one' hy htv.le, hval y hyc, fun h' => absurd h' hTv⟩
  choose y hyL hyb hyprim using hlocb
  -- `b` is represented over `ℚ` (Hasse–Minkowski)
  have hrat : Qh.RepresentsIn ℚ (b : ℚ) := by
    rw [represents_iff_everywhere_nf _ hQ _ hb0]
    intro w
    cases w with
    | infinite w =>
      exact representsIn_congr_alg _ _ _ _
        (representsIn_inf_of_real h (exists_real_rep h hpd (by omega) b hb) w)
    | finite v => exact ⟨y v, hyb v⟩
  obtain ⟨x, hx⟩ := hrat
  have hxb : Qh.eval x = (b : ℚ) := by simpa using hx
  obtain ⟨z, hz, hzc, hzprim⟩ := hk₀ x (by rw [hxb]; exact hb0) y hyL (fun v => by rw [hxb]; exact hyb v)
    T (fun v hv => ⟨(hT v hv).1, hyprim v hv⟩)
  obtain ⟨zz, rfl⟩ := exists_int_of_mem hL hz
  refine ⟨zz, hz, ?_, hzprim⟩
  have := evalIn_rat_intCast h zz
  change Qh.evalIn ℚ _ = _ at this
  rw [show Qh.evalIn ℚ (fun i => (zz i : ℚ)) = Qh.eval (fun i => (zz i : ℚ)) from rfl, hzc, hxb, hgen'] at this
  exact_mod_cast this.symm

/-! ### The data of the final stage and Cassels' deduction -/

/-- **The data of the final stage of Cassels' proof of Lemma 9.2** (Ch. 11, pp. 246–248), for the quaternary form `f`
and the prime `q`. Fields: `u` Cassels' vector $\mathbf u$ ((9.41)); `W` a $4 \times 3$ integer matrix (coordinates on
$V^{(2)} = \mathbf u^\perp$); `h` the ternary form $h(z) = f(Wz)$; `L` Cassels' lattice $\Gamma$, a lattice on
$(\mathbb Q^3, h)$; `S` a finite set of primes (Cassels' $P^*$); `split` $f(b\mathbf u + Wz) = f(\mathbf u)b^2 + h(z)$;
`posdef` $h$ is positive definite; `intL` $\Gamma \subseteq \mathbb Z^3$; `spn` the genus of $\Gamma$ is one proper spinor
genus ((9.60) with Lemma 3.6, Corollary); `qS` $q \in S$; `iso_q` $\Gamma_q$ is isotropic; `rep_q` $\Gamma_q$ represents
every integer; `rep_out` at the places over primes outside $S$, $\Gamma_p$ primitively represents every integer;
`prim_out` at those places $b\mathbf u + Wz$ is primitive at $p$ whenever $z \in \Gamma$ is primitive in $\Gamma_p$ ((9.44)
in case (d)). -/
structure L92Datum (f : QuadForm ℤ 4) (q : ℕ) (hq : q.Prime) where
  /-- Cassels' vector $\mathbf u$. -/
  u : Fin 4 → ℤ
  /-- Coordinates on $\mathbf u^\perp$: the columns of a $4 \times 3$ integer matrix. -/
  W : Matrix (Fin 4) (Fin 3) ℤ
  /-- The ternary form $h(z) = f(Wz)$. -/
  h : QuadForm ℤ 3
  /-- Cassels' lattice $\Gamma$ on $(\mathbb Q^3, h)$. -/
  L : Lat ℚ 3
  /-- The finite set $P^*$ of primes. -/
  S : Finset ℕ
  /-- $f(b\mathbf u + Wz) = f(\mathbf u)b^2 + h(z)$. -/
  split : ∀ (b : ℤ) (z : Fin 3 → ℤ), f.eval (b • u + W *ᵥ z) = b ^ 2 * f.eval u + h.eval z
  /-- $h$ is positive definite. -/
  posdef : IntQF.PosDef h
  /-- $\Gamma \subseteq \mathbb Z^3$. -/
  intL : L.1 ≤ intVec
  /-- The genus of $\Gamma$ consists of one proper spinor genus. -/
  spn : ∀ M : Lat ℚ 3, SameGenus (h.map (Int.castRingHom ℚ)) L.1 M.1 →
    SameProperSpinorGenus (h.map (Int.castRingHom ℚ)) L M
  /-- $q \in S$. -/
  qS : q ∈ S
  /-- $\Gamma_q$ is isotropic. -/
  iso_q : (h.map (Int.castRingHom ℚ)).IsotropicIn ((placeOf q hq).adicCompletion ℚ)
  /-- $\Gamma_q$ represents every integer. -/
  rep_q : ∀ c : ℤ, ∃ y ∈ loc (placeOf q hq) L.1,
    (h.map (Int.castRingHom ℚ)).evalIn _ y = algebraMap ℚ _ (c : ℚ)
  /-- Outside $S$, $\Gamma_p$ primitively represents every integer. -/
  rep_out : ∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∉ S → ∀ c : ℤ,
    ∃ y, LocPrimitive v (loc v L.1) y ∧ (h.map (Int.castRingHom ℚ)).evalIn _ y = algebraMap ℚ _ (c : ℚ)
  /-- Outside $S$, $b\mathbf u + Wz$ is primitive at $p$ when $z$ is primitive in $\Gamma_p$. -/
  prim_out : ∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∉ S →
    ∀ (b : ℤ) (z : Fin 3 → ℤ), LocPrimitive v (loc v L.1) (locVec v (fun i => (z i : ℚ))) →
      PrimAt (Rat.HeightOneSpectrum.natGenerator v) (b • u + W *ᵥ z)

/-- **The conditions on $b$ in the final stage** (Cassels, Ch. 11, p. 248), for the datum `D`, the exponent `k` (Cassels'
$m$ of Theorem 8.3, Corollary) and the integers `a`, `b`, with $c = a - f(\mathbf u)b^2$: (1) $q^{2k} \mid c$; (2) $c$ is
represented by $\Gamma_p$ for every prime $p \in S$, $p \ne q$ ("$c$ is representable by $f$ on all $\Gamma_p$
($p \in P^*$)"); (3) for every $z \in \Gamma$ with $h(z) = c$, one of $b\mathbf u + Wz$, $b\mathbf u - Wz$ is primitive at
every prime of $S$ (the discussion of the cases $p \in P^*$ on pp. 248–249; the sign is "on replacing $\mathbf c$ by
$-\mathbf c$ if need be" at $p = p(0)$). -/
def LocalOK {f : QuadForm ℤ 4} {q : ℕ} {hq : q.Prime} (D : L92Datum f q hq) (k : ℕ) (a b : ℤ) : Prop :=
  (q : ℤ) ^ (2 * k) ∣ a - b ^ 2 * f.eval D.u ∧
  (∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∈ D.S → v ≠ placeOf q hq →
    ∃ y ∈ loc v D.L.1, (D.h.map (Int.castRingHom ℚ)).evalIn _ y =
      algebraMap ℚ _ ((a - b ^ 2 * f.eval D.u : ℤ) : ℚ)) ∧
  ∀ z : Fin 3 → ℤ, (fun i => (z i : ℚ)) ∈ D.L.1 → D.h.eval z = a - b ^ 2 * f.eval D.u →
    (∀ p ∈ D.S, p.Prime → PrimAt p (b • D.u + D.W *ᵥ z)) ∨
      (∀ p ∈ D.S, p.Prime → PrimAt p (b • D.u - D.W *ᵥ z))

/-- **The family of data of Cassels' proof of Lemma 9.2** (Ch. 11, pp. 245–248): finitely many data `D i` such that
for every exponent $k$ there are finite sets $B_i$ of integers with: every $a$ prime to $q$ that is primitively
represented by $f$ over every $\mathbb Z_p$ satisfies `LocalOK (D i) k a b` for some $i$ and some $b \in B_i$. (Cassels:
the data correspond to the finitely many choices of the $k(p)$, $p \in P \cup \{q\}$; "a finite set of $b$ will cover
all values of $a$".) Arguments: `f` the form, `q` the prime. -/
def Lemma92Family (f : QuadForm ℤ 4) (q : ℕ) (hq : q.Prime) : Prop :=
  ∃ (m : ℕ) (D : Fin m → L92Datum f q hq), ∀ k : ℕ, ∃ B : Fin m → Finset ℤ, ∀ a : ℤ, ¬ (q : ℤ) ∣ a →
    (∀ (p : ℕ) [Fact p.Prime], PrimRepZp p f a) → ∃ i, ∃ b ∈ B i, LocalOK (D i) k a b

/-- Helper: a positive definite form is nonnegative. -/
theorem eval_nonneg_of_posDef {m : ℕ} {f : QuadForm ℤ m} (hf : IntQF.PosDef f) (x : Fin m → ℤ) : 0 ≤ f.eval x := by
  by_cases hx : x = 0
  · subst hx; simp [QuadForm.evalIn]
  · exact (hf x hx).le

/-- **Cassels' final stage** (Ch. 11, p. 248–249, "one then completes the proof of Lemma 9.2 by showing that a finite
set of $b$ will cover all values of $a$"): from a family of data as in `Lemma92Family`, $\mathcal R(f, a)$ holds for all
$a > N$ with $q \nmid a$, where $N = \sum_i \sum_{b \in B_i} f(\mathbf u_i)b^2$. *Proof:* $k$ is the largest of the
exponents of `exists_rep_primitive_lat` for the lattices $\Gamma_i$; for $a > N$ the number $c = a - f(\mathbf u_i)b^2$ is
positive, so $c = h_i(z)$ with $z \in \Gamma_i$ primitive outside $S_i$, and $x = b\mathbf u_i \pm W_iz$ is primitive with
$f(x) = a$. -/
theorem exists_bound_of_family {f : QuadForm ℤ 4} (hf : IntQF.PosDef f) {q : ℕ} (hq : q.Prime)
    (H : Lemma92Family f q hq) : ∃ N : ℤ, ∀ a : ℤ, N < a → ¬ (q : ℤ) ∣ a → LocGlobal f a := by
  classical
  obtain ⟨m, D, hD⟩ := H
  have hk := fun i => exists_rep_primitive_lat (D i).h (D i).posdef hq (D i).L (D i).intL (D i).spn
    (D i).iso_q (D i).rep_q
  choose k₀ hk₀ using hk
  set k := Finset.univ.sup k₀
  obtain ⟨B, hB⟩ := hD k
  set N : ℤ := ∑ i, ∑ b ∈ B i, b ^ 2 * f.eval (D i).u with hN
  refine ⟨N, fun a ha hqa hloc => ?_⟩
  obtain ⟨i, b, hb, h1, h2, h3⟩ := hB a hqa hloc
  have hterm : ∀ j, ∀ b' ∈ B j, 0 ≤ b' ^ 2 * f.eval (D j).u := fun j b' _ =>
    mul_nonneg (sq_nonneg _) (eval_nonneg_of_posDef hf _)
  have hle : b ^ 2 * f.eval (D i).u ≤ N := by
    have e1 : b ^ 2 * f.eval (D i).u ≤ ∑ b' ∈ B i, b' ^ 2 * f.eval (D i).u :=
      Finset.single_le_sum (f := fun b' => b' ^ 2 * f.eval (D i).u) (hterm i) hb
    have e2 : ∑ b' ∈ B i, b' ^ 2 * f.eval (D i).u ≤ N :=
      Finset.single_le_sum (f := fun j => ∑ b' ∈ B j, b' ^ 2 * f.eval (D j).u)
        (fun j _ => Finset.sum_nonneg (hterm j)) (Finset.mem_univ i)
    exact e1.trans e2
  set c := a - b ^ 2 * f.eval (D i).u with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hki : k₀ i ≤ k := Finset.le_sup (f := k₀) (Finset.mem_univ i)
  have hdvd : (q : ℤ) ^ (2 * k₀ i) ∣ c := (pow_dvd_pow _ (by omega)).trans h1
  obtain ⟨z, hzL, hz, hzp⟩ := hk₀ i c hcpos hdvd
    (fun v hvq => by
      by_cases hvS : Rat.HeightOneSpectrum.natGenerator v ∈ (D i).S
      · exact h2 v hvS hvq
      · obtain ⟨y, hy, hyc⟩ := (D i).rep_out v hvS c
        exact ⟨y, hy.1, hyc⟩)
    (fun v => Rat.HeightOneSpectrum.natGenerator v ∉ (D i).S)
    (fun v hvS => ⟨fun hvq => hvS (by rw [hvq, natGenerator_placeOf]; exact (D i).qS), (D i).rep_out v hvS c⟩)
  have hfin : ∀ z' : Fin 3 → ℤ, (D i).h.eval z' = c →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∉ (D i).S →
        LocPrimitive v (loc v (D i).L.1) (locVec v (fun j => (z' j : ℚ)))) →
      (∀ p ∈ (D i).S, p.Prime → PrimAt p (b • (D i).u + (D i).W *ᵥ z')) → PrimRepZ f a := by
    intro z' hz' hz'p hS
    refine ⟨b • (D i).u + (D i).W *ᵥ z', (gcd_eq_one_iff_forall_primAt _).mpr fun p hp => ?_, ?_⟩
    · by_cases hpS : p ∈ (D i).S
      · exact hS p hpS hp
      · have hv := (D i).prim_out (placeOf p hp) (by rw [natGenerator_placeOf]; exact hpS) b z'
          (hz'p _ (by rw [natGenerator_placeOf]; exact hpS))
        rwa [natGenerator_placeOf] at hv
    · rw [(D i).split, hz', hc]; ring
  rcases h3 z hzL hz with hS | hS
  · exact hfin z hz hzp hS
  · have hneg : (D i).h.eval (-z) = c := by
      have := LocalDensity.evalIn_const_mul (D i).h (-1) z
      rw [show (fun j => (-1 : ℤ) * z j) = -z by funext j; simp] at this
      change (D i).h.evalIn ℤ (-z) = c
      rw [this, ← hz]; ring
    refine hfin (-z) hneg (fun v hv => ?_) fun p hpS hp => ?_
    · have e : locVec v (fun j => (((-z) j : ℤ) : ℚ)) = (-1 : v.adicCompletion ℚ) • locVec v (fun j => (z j : ℚ)) := by
        funext j; simp [locVec_apply]
      rw [e]
      exact (hzp v hv).smul_unit (by simp)
    · rw [mulVec_neg, ← sub_eq_add_neg]
      exact hS p hpS hp

/-- **The construction of Cassels' proof of Lemma 9.2, named statement** (Ch. 11, pp. 245–248): for every positive
definite classically integral quaternary form $f$ and every odd prime $q$ with $d(f) \in U_q^2$ there is a family of data
as in `Lemma92Family`. *Proved* in `Ch11Lemma92Final.lean` (`lemma92FamilyStatement_holds`). Cassels' construction consists of
the local discussion at the primes of $P$ (Lemma 9.3 and its Corollary at the isotropic primes), the choice of $g_1$ and of the
auxiliary primes $\pi$, $p(0)$ (Dirichlet's theorem, (9.38)–(9.40)), the vector $\mathbf u$ by Theorem 8.1 ((9.41)), the lattice
$\Gamma$ by its localizations in the cases (a), (b), (c₁), (c₂), (d) with $\theta(\Gamma_p) \supseteq U_p$ ((9.60)), and the choice of
$b$ ("left to the reader", p. 248). -/
@[kb "cassels1978" "Ch. 11, proof of Lemma 9.2, pp. 245–248 (construction of u, Γ and the finite sets of b)"]
structure Lemma92FamilyStatement : Prop where
  /-- The family exists for every $f$ and $q$ as in Lemma 9.2. -/
  holds : ∀ f : QuadForm ℤ 4, IntQF.PosDef f → IsClassicallyIntegral f →
    ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → IsUnitSquareAt q (cassDet f) → Lemma92Family f q Fact.out

/-- **Cassels, Lemma 9.2, from the construction** (Ch. 11, pp. 242–249): the final stage `exists_bound_of_family`
applied to the family of `Lemma92FamilyStatement`. -/
@[kb "cassels1978" "Ch. 11, Lemma 9.2, p. 242 (final stage, p. 248, from the construction)"]
theorem lemma92_of_family (H : Lemma92FamilyStatement) : Lemma92 :=
  ⟨fun f hf hci q _ hq2 hsq => exists_bound_of_family hf Fact.out (H.holds f hf hci q hq2 hsq)⟩

end QuadFormsKB.Cassels.Ch11L92
