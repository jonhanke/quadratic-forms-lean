import QuadFormsKB.Binary.GenusAverage

/-!
# Gauss's duplication theorem: the principal genus is $\mathrm{Cl}^2$

For a fundamental discriminant $D < 0$ with $t$ prime factors:

* **Ambiguous forms** (`exists_sLEquiv_a_dvd_b`): a form with an improper automorphism ($\bar f \sim_{\mathrm{SL}} f$,
  i.e. $[\mathfrak a_f]^2 = 1$) is properly equivalent to a form $g$ with $g_a \mid g_b$. (An improper automorphism
  $\gamma$ has trace $0$, so it fixes a primitive vector $v$; in a proper basis $(v, u)$ it is
  $\begin{pmatrix} 1 & k\\ 0 & -1\end{pmatrix}$, whence $g_b = k g_a$.) Then $g_a \mid D$ and $\mathfrak a_g$ is the unique ideal
  of norm $g_a$.
* **Ramified classes** (`ramClass`): for $p \mid D$, the unique ideal $\mathfrak r_p$ of norm $p$ (the count) has
  $\mathfrak r_p^2 = (p)$; an ideal whose norm $n$ has all prime factors dividing $D$ is $\prod_p \mathfrak r_p^{v_p(n)}$
  (`mk0_eq_prod_ramClass`), and $(\sqrt D) = \prod_p \mathfrak r_p^{v_p(D)}$ gives one relation.
* **The 2-torsion** (`card_twoTorsion_le`): $|\mathrm{Cl}[2]| \le 2^{t-1}$, since $\mathrm{Cl}[2]$ lies in the image of
  $\Phi : \{\pm 1\}^t \to \mathrm{Cl}$, $e \mapsto \prod_{e_p = -1}[\mathfrak r_p]$, whose kernel is nontrivial.
* **Duplication** (`ker_genusHom_eq_range_sq`, `principalGenus_eq_sq`): $\ker\gamma = \mathrm{Cl}^2$ and
  $|\mathrm{Cl}[2]| = 2^{t-1}$ (`card_twoTorsion`).

Sources: Gauss, *Disq. Arith.* §§257–260 (ambiguous classes), §286 (duplication) [unverified]; Cox, §3.B, Thm. 3.15,
Cor. 3.14 and Exercises 3.8–3.10 [unverified locator]; Zagier, §11 [unverified locator].
-/

open QuadraticAlgebra NumberField
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF Siegel

variable {D : ℤ}

/-! ### Ambiguous forms -/

/-- **An improper automorphism has trace zero:** if $f \circ \gamma = f$ with $\gamma = \begin{pmatrix} P & Q\\ R & S\end{pmatrix}$,
$\det\gamma = -1$ and $a \ne 0$, then $S = -P$. (Polynomial identity:
$2a(P + S) = -2S(A - a) + R(B - b) + (2aP + bR)(PS - QR + 1)$ for $f \circ \gamma = [A, B, C]$.) -/
theorem improper_trace_zero {f : BinQF} (ha : f.a ≠ 0) {P Q R S : ℤ} (hdet : P * S - Q * R = -1)
    (h : BinQF.subst P Q R S f = f) : S = -P := by
  have e1 := congrArg BinQF.a h
  have e2 := congrArg BinQF.b h
  simp only [a_subst, b_subst] at e1 e2
  have h2 : 2 * f.a * (P + S) = 0 := by
    linear_combination (-2 * S) * e1 + R * e2 + (2 * f.a * P + f.b * R) * hdet
  have : P + S = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero ha)
    · exact h
  linarith

/-- A nonzero integer vector fixed by $\begin{pmatrix} p & q\\ r & s\end{pmatrix}$ gives a primitive fixed vector. -/
theorem exists_coprime_fixed {p q r s u₀ u₁ : ℤ} (hu : u₀ ≠ 0 ∨ u₁ ≠ 0) (h1 : p * u₀ + q * u₁ = u₀)
    (h2 : r * u₀ + s * u₁ = u₁) : ∃ x y : ℤ, IsCoprime x y ∧ p * x + q * y = x ∧ r * x + s * y = y := by
  have hg : 0 < Int.gcd u₀ u₁ := Int.gcd_pos_iff.mpr hu
  set d : ℤ := (Int.gcd u₀ u₁ : ℤ)
  have hd : d ≠ 0 := by simp only [d]; omega
  obtain ⟨x, hx⟩ : d ∣ u₀ := Int.gcd_dvd_left ..
  obtain ⟨y, hy⟩ : d ∣ u₁ := Int.gcd_dvd_right ..
  have hxy : IsCoprime x y := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h := Int.gcd_mul_left d x y
    rw [← hx, ← hy] at h
    have hdn : d.natAbs = Int.gcd u₀ u₁ := by simp [d]
    rw [hdn] at h
    exact Nat.eq_of_mul_eq_mul_left hg (h.symm.trans (mul_one _).symm)
  refine ⟨x, y, hxy, ?_, ?_⟩
  · have : d * (p * x + q * y - x) = 0 := by rw [hx, hy] at h1; linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hd
    · linarith
  · have : d * (r * x + s * y - y) = 0 := by rw [hx, hy] at h2; linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hd
    · linarith

/-- **Ambiguous forms** (Gauss, *Disq. Arith.* §§163, 257 [unverified]; Cox, Exercise 3.8 [unverified locator]): a
positive definite form $f$ with $\bar f \sim_{\mathrm{SL}} f$ (an improper automorphism) is properly equivalent to a form
$g$ with $g_a > 0$ and $g_a \mid g_b$. *Proof:* the improper automorphism $\gamma$ has trace $0$
(`improper_trace_zero`), so $\gamma^2 = 1$ and $\gamma$ fixes a primitive $v = (x, y)$; complete it to a proper basis
$(v, u)$; $\gamma u + u = k v$ (a fixed vector with $\det(v, \gamma u + u) = -1 + 1 = 0$); for $g = f \circ (v\ u)$,
$f(\gamma(v + u)) = f(v + u)$ and $f(\gamma u) = f(u)$ give $g(1 + k, -1) - g(k, -1) = g(1, 1) - g(0, 1)$, i.e.
$g_b = k g_a$. -/
@[kb "cox2013" "§3.B, Exercise 3.8 [unverified locator]"]
theorem exists_sLEquiv_a_dvd_b {f : BinQF} (hpos : f.PosDef) (hc : SLEquiv (conjForm f) f) :
    ∃ g : BinQF, SLEquiv f g ∧ 0 < g.a ∧ g.a ∣ g.b := by
  obtain ⟨p, q, r, s, hd, h⟩ := (sLEquiv_iff _ _).mp hc
  have haut : BinQF.subst p q (-r) (-s) f = f := by
    conv_rhs => rw [← h]
    refine ext_abc ?_ ?_ ?_ <;> simp [conjForm]
    ring
  have hdet : p * (-s) - q * (-r) = -1 := by linarith
  have ha : f.a ≠ 0 := ((posDef_iff_posDef' f).mp hpos).1.ne'
  have hsp : s = p := by have := improper_trace_zero ha hdet haut; linarith
  subst hsp
  have hinv : ∀ X Y : ℤ, f.eval (s * X + q * Y) (-r * X + -s * Y) = f.eval X Y := fun X Y => by
    rw [← eval_subst, haut]
  -- a primitive fixed vector `(x, y)`
  obtain ⟨x, y, hxy, hfx, hfy⟩ : ∃ x y : ℤ, IsCoprime x y ∧ s * x + q * y = x ∧ -r * x + -s * y = y := by
    by_cases h0 : q = 0 ∧ 1 - s = 0
    · refine exists_coprime_fixed (u₀ := 1 + s) (u₁ := -r) (Or.inl (by omega)) ?_ (by ring)
      linear_combination hd
    · exact exists_coprime_fixed (u₀ := q) (u₁ := 1 - s) (by tauto) (by ring) (by linear_combination hd)
  obtain ⟨r', s', hdet', -⟩ := exists_subst_a_eq f hxy
  -- `γ u + u = k v`
  set w₀ := s * r' + q * s' + r' with hw₀d
  set w₁ := -r * r' + -s * s' + s' with hw₁d
  have hβ : x * w₁ - y * w₀ = 0 := by
    rw [hw₀d, hw₁d]; linear_combination (-s') * hfx + r' * hfy
  set k := w₀ * s' - w₁ * r' with hkd
  have hw₀ : w₀ = k * x := by
    rw [hkd, hw₀d, hw₁d]
    linear_combination (-r' * s') * hfx + r' ^ 2 * hfy + (-q * s' - r' * s - r') * hdet'
  have hw₁ : w₁ = k * y := by
    rw [hkd, hw₀d, hw₁d]
    linear_combination (-s' ^ 2) * hfx + (r' * s') * hfy + (r * r' + s * s' - s') * hdet'
  have e1 := hinv (x + r') (y + s')
  have e2 := hinv r' s'
  rw [show s * (x + r') + q * (y + s') = (1 + k) * x - r' by linear_combination hfx + hw₀d.symm + hw₀,
    show -r * (x + r') + -s * (y + s') = (1 + k) * y - s' by linear_combination hfy + hw₁d.symm + hw₁] at e1
  rw [show s * r' + q * s' = k * x - r' by linear_combination hw₀d.symm + hw₀,
    show -r * r' + -s * s' = k * y - s' by linear_combination hw₁d.symm + hw₁] at e2
  simp only [eval_eq] at e1 e2
  refine ⟨BinQF.subst x r' y s' f, (sLEquiv_iff _ _).mpr ⟨x, r', y, s', hdet', rfl⟩, ?_, ?_⟩
  · rw [a_subst]
    have hxy0 : (x, y) ≠ (0, 0) := by
      rintro h0
      simp only [Prod.mk.injEq] at h0
      rw [h0.1, h0.2] at hxy
      exact not_isCoprime_zero_zero hxy
    have := hpos x y hxy0
    rw [eval_eq] at this
    linarith
  · refine ⟨k, ?_⟩
    have h2 : 2 * ((BinQF.subst x r' y s' f).b - (BinQF.subst x r' y s' f).a * k) = 0 := by
      rw [a_subst, b_subst]
      linear_combination e2 - e1
    have := (mul_eq_zero.mp h2).resolve_left two_ne_zero
    linarith

variable [IsQuadDisc D]

/-! ### Ideals whose norm has all prime factors dividing $D$ -/

/-- **There is exactly one ideal of norm $n$** when every prime factor of $n \ge 1$ divides $D$ (the count:
$\sum_{d \mid n}\chi_D(d) = 1$). -/
theorem existsUnique_ideal_absNorm {n : ℕ} (hn : n ≠ 0) (h : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ D.natAbs) :
    ∃ I : Ideal (QOrder D), Ideal.absNorm I = n ∧ ∀ J : Ideal (QOrder D), Ideal.absNorm J = n → J = I := by
  have h1 : Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = n} = 1 := by
    have := card_ideals_order_absNorm_eq (D := D) hn
    rw [sum_kronZ_of_dvd_D hn h] at this
    exact_mod_cast this
  obtain ⟨hsub, ⟨I⟩⟩ := Nat.card_eq_one_iff_unique.mp h1
  exact ⟨I.1, I.2, fun J hJ => congrArg Subtype.val (hsub.elim ⟨J, hJ⟩ I)⟩

/-- **The ramified prime above $p \mid D$:** the unique ideal $\mathfrak r_p$ of $\mathbb{Z}[\omega]$ of norm $p$. -/
noncomputable def ramIdeal (p : D.natAbs.primeFactors) : Ideal (QOrder D) :=
  (existsUnique_ideal_absNorm (D := D) (n := p.1) (Nat.prime_of_mem_primeFactors p.2).ne_zero
    fun q hq hqp => by
      rw [(Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors p.2)).mp hqp]
      exact Nat.dvd_of_mem_primeFactors p.2).choose

theorem absNorm_ramIdeal (p : D.natAbs.primeFactors) : Ideal.absNorm (ramIdeal p) = p.1 :=
  (existsUnique_ideal_absNorm (D := D) (n := p.1) (Nat.prime_of_mem_primeFactors p.2).ne_zero
    fun q hq hqp => by
      rw [(Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors p.2)).mp hqp]
      exact Nat.dvd_of_mem_primeFactors p.2).choose_spec.1

theorem ramIdeal_mem (p : D.natAbs.primeFactors) : ramIdeal p ∈ (Ideal (QOrder D))⁰ :=
  mem_nonZeroDivisors_of_absNorm (by rw [absNorm_ramIdeal]; exact (Nat.prime_of_mem_primeFactors p.2).ne_zero)

/-- **The class of the ramified prime** $[\mathfrak r_p] \in \mathrm{Cl}(\mathbb{Z}[\omega])$, $p \mid D$. -/
noncomputable def ramClass (p : D.natAbs.primeFactors) : ClassGroup (QOrder D) :=
  ClassGroup.mk0 ⟨ramIdeal p, ramIdeal_mem p⟩

/-- **A principal ideal $(z)$ has trivial class.** -/
theorem mk0_span_singleton {z : QOrder D} (h : Ideal.span {z} ∈ (Ideal (QOrder D))⁰) :
    ClassGroup.mk0 ⟨Ideal.span {z}, h⟩ = 1 :=
  (ClassGroup.mk0_eq_one_iff h).mpr ⟨⟨z, rfl⟩⟩

/-- **$[\mathfrak r_p]^2 = 1$**: $\mathfrak r_p^2$ and $(p)$ are ideals of norm $p^2$, so they are equal. -/
theorem ramClass_sq (hD : D < 0) (p : D.natAbs.primeFactors) : ramClass p ^ 2 = 1 := by
  have hp := Nat.prime_of_mem_primeFactors p.2
  have hpD := Nat.dvd_of_mem_primeFactors p.2
  set z : QOrder D := ⟨(p.1 : ℤ), 0⟩
  have hz : z ≠ 0 := fun h => hp.ne_zero (by
    have := congrArg QuadraticAlgebra.re h
    simp only [z, QuadraticAlgebra.re_zero] at this
    exact_mod_cast this)
  have hNz : Ideal.absNorm (Ideal.span {z}) = p.1 ^ 2 := by
    have := absNorm_span_singleton_eq hD hz
    rw [QuadraticAlgebra.norm_def] at this
    simp only [z, mul_zero, add_zero, sub_zero] at this
    have h' : ((Ideal.absNorm (Ideal.span {z}) : ℕ) : ℤ) = ((p.1 ^ 2 : ℕ) : ℤ) := by
      rw [this]; push_cast; ring
    exact_mod_cast h'
  have hN2 : Ideal.absNorm (ramIdeal p ^ 2) = p.1 ^ 2 := by rw [map_pow, absNorm_ramIdeal]
  obtain ⟨I, -, hI⟩ := existsUnique_ideal_absNorm (D := D) (n := p.1 ^ 2) (pow_ne_zero _ hp.ne_zero)
    fun q hq hqp => by rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqp)]; exact hpD
  have heq : ramIdeal p ^ 2 = Ideal.span {z} := (hI _ hN2).trans (hI _ hNz).symm
  have h0 : Ideal.span {z} ∈ (Ideal (QOrder D))⁰ := mem_nonZeroDivisors_of_absNorm (by rw [hNz]; exact pow_ne_zero _ hp.ne_zero)
  rw [ramClass, ← map_pow, ← mk0_span_singleton h0]
  congr 1
  exact Subtype.ext (by simp [heq])

/-- **An ideal whose norm $n$ has all prime factors dividing $D$ is $\prod_p \mathfrak r_p^{v_p(n)}$ in the class group:**
$[\mathfrak b] = \prod_{p \mid D}[\mathfrak r_p]^{v_p(n)}$ (induction on $n$; at each step $\mathfrak b = \mathfrak r_q\mathfrak b'$ by
uniqueness of the ideal of norm $n$). -/
theorem mk0_eq_prod_ramClass : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → q ∣ n → q ∣ D.natAbs) →
    ∀ (I : Ideal (QOrder D)) (hI : I ∈ (Ideal (QOrder D))⁰), Ideal.absNorm I = n →
      ClassGroup.mk0 ⟨I, hI⟩ = ∏ p : D.natAbs.primeFactors, ramClass p ^ (n.factorization p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hq I hI hN
    by_cases h1 : n = 1
    · subst h1
      have hI1 : I = ⊤ := Ideal.absNorm_eq_one_iff.mp hN
      subst hI1
      simp only [Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, pow_zero, Finset.prod_const_one]
      exact (ClassGroup.mk0_eq_one_iff hI).mpr ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩
    · obtain ⟨q, hqp, hqn⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨n', rfl⟩ := hqn
      have hn' : n' ≠ 0 := by rintro rfl; simp at hn
      have hqD : q ∈ D.natAbs.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqp, hq q hqp (dvd_mul_right _ _), by
          have := three_le_natAbs (D := D); omega⟩
      obtain ⟨J, hJN, -⟩ := existsUnique_ideal_absNorm (D := D) hn' fun r hr hrn =>
        hq r hr (Dvd.dvd.mul_left hrn q)
      have hJ0 : J ∈ (Ideal (QOrder D))⁰ := mem_nonZeroDivisors_of_absNorm (by rw [hJN]; exact hn')
      obtain ⟨K, -, hK⟩ := existsUnique_ideal_absNorm (D := D) hn hq
      have hIeq : I = ramIdeal ⟨q, hqD⟩ * J :=
        (hK I hN).trans (hK _ (by rw [map_mul, absNorm_ramIdeal, hJN])).symm
      subst hIeq
      rw [show (⟨ramIdeal ⟨q, hqD⟩ * J, hI⟩ : (Ideal (QOrder D))⁰) = ⟨ramIdeal ⟨q, hqD⟩, ramIdeal_mem _⟩ *
          ⟨J, hJ0⟩ from rfl, map_mul,
        ih n' (by have := hqp.two_le; nlinarith [Nat.pos_of_ne_zero hn']) hn'
          (fun r hr hrn => hq r hr (Dvd.dvd.mul_left hrn q)) J hJ0 hJN,
        Nat.factorization_mul hqp.ne_zero hn', hqp.factorization]
      simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single (⟨q, hqD⟩ : D.natAbs.primeFactors)]
      · simp [ramClass]
      · intro p _ hp
        rw [Finsupp.single_apply]
        simp [show ¬ (q = p.1) from fun h => hp (Subtype.ext h.symm)]
      · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The 2-torsion of the class group -/

omit [IsQuadDisc D] in
/-- The homomorphism $\{\pm 1\} \to G$, $-1 \mapsto c$, for $c^2 = 1$. -/
def signHom {G : Type*} [CommGroup G] (c : G) (hc : c ^ 2 = 1) : ℤˣ →* G where
  toFun u := if u = 1 then 1 else c
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [← sq, hc]

omit [IsQuadDisc D] in
theorem signHom_neg_one_pow {G : Type*} [CommGroup G] (c : G) (hc : c ^ 2 = 1) (k : ℕ) :
    signHom c hc ((-1) ^ k) = c ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, map_mul, ih, pow_succ]; simp [signHom]

/-- **The ramified-class map** $\Phi : \{\pm 1\}^t \to \mathrm{Cl}(\mathbb{Z}[\omega])$,
$e \mapsto \prod_{p : e_p = -1}[\mathfrak r_p]$ (a homomorphism since $[\mathfrak r_p]^2 = 1$). -/
noncomputable def ramHom (hD : D < 0) : (D.natAbs.primeFactors → ℤˣ) →* ClassGroup (QOrder D) where
  toFun e := ∏ p, signHom (ramClass p) (ramClass_sq hD p) (e p)
  map_one' := by simp
  map_mul' e e' := by simp [Finset.prod_mul_distrib]

/-- $\Phi((-1)^{v_p(n)})_p = [\mathfrak b]$ for an ideal $\mathfrak b$ whose norm $n$ has all prime factors dividing $D$. -/
theorem ramHom_eq_mk0 (hD : D < 0) {n : ℕ} (hn : n ≠ 0) (hq : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ D.natAbs)
    (I : Ideal (QOrder D)) (hI : I ∈ (Ideal (QOrder D))⁰) (hN : Ideal.absNorm I = n) :
    ramHom hD (fun p => (-1) ^ (n.factorization p)) = ClassGroup.mk0 ⟨I, hI⟩ := by
  rw [mk0_eq_prod_ramClass n hn hq I hI hN]
  change ∏ p, signHom (ramClass p) (ramClass_sq hD p) ((-1) ^ (n.factorization p)) = _
  exact Finset.prod_congr rfl fun p _ => signHom_neg_one_pow (ramClass p) (ramClass_sq hD p) _

/-- **Every ambiguous class is a product of ramified classes** ($D < 0$ fundamental): if $x^2 = 1$ in
$\mathrm{Cl}(\mathbb{Z}[\omega])$ then $x$ is in the image of $\Phi$ (`ramHom`). $x = [\mathfrak a_f]$ with $\bar f \sim_{\mathrm{SL}} f$
(`sLEquiv_conj_iff`), $f \sim_{\mathrm{SL}} g$ with $g_a \mid g_b$ (`exists_sLEquiv_a_dvd_b`), so $g_a \mid D$ and
$x = [\mathfrak a_g] = \Phi((-1)^{v_p(g_a)})_p$ (`ramHom_eq_mk0`). -/
theorem mem_range_ramHom_of_sq_eq_one (hD : D < 0) {x : ClassGroup (QOrder D)} (hx : x ^ 2 = 1) :
    x ∈ (ramHom hD).range := by
  obtain ⟨F, rfl⟩ := idealClass_surjective hD x
  have hc : SLEquiv (conjForm F.1) F.1 := (sLEquiv_conj_iff hD F).mpr hx
  obtain ⟨g, hFg, hga, hdvd⟩ := exists_sLEquiv_a_dvd_b F.2.2.1 hc
  have hgD : g.disc = D := by
    obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp hFg
    rw [disc_subst_of_det _ _ _ _ _ (by rw [hd]; norm_num)]
    exact F.2.1
  let G : PrimPosForm D := ⟨g, (mem_primPosForm_iff IsQuadDisc.fund hD g).mpr ⟨hgD, hga⟩⟩
  have hcls : idealClass F = idealClass G := idealClass_eq_of_sLEquiv (f := F) (g := G) hFg
  have hn : g.a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hga.ne'
  have haD : g.a ∣ D := by
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨g.a * k ^ 2 - 4 * g.c, by rw [← hgD, BinQF.disc, hk]; ring⟩
  have hq : ∀ q : ℕ, q.Prime → q ∣ g.a.natAbs → q ∣ D.natAbs :=
    fun q _ hqn => hqn.trans (Int.natAbs_dvd_natAbs.mpr haD)
  refine ⟨fun p => (-1) ^ (g.a.natAbs.factorization p), ?_⟩
  rw [hcls]
  exact ramHom_eq_mk0 hD hn hq _ _ (absNorm_formIdeal hgD hga.ne')

/-- For a fundamental $D \ne -4$, some prime $p \mid D$ divides $D$ to an odd power ($v_p(D) = 1$ for odd $p$, and
if $D = -2^k$ then $k = 3$). -/
theorem exists_odd_factorization (hD : D < 0) (h4 : D ≠ -4) :
    ∃ p ∈ D.natAbs.primeFactors, Odd (D.natAbs.factorization p) := by
  have h3 := three_le_natAbs (D := D)
  have hN : D.natAbs ≠ 0 := by omega
  by_cases hodd : ∃ p ∈ D.natAbs.primeFactors, p ≠ 2
  · obtain ⟨p, hp, hp2⟩ := hodd
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine ⟨p, hp, ?_⟩
    have h1 : 1 ≤ D.natAbs.factorization p :=
      (hpp.dvd_iff_one_le_factorization hN).mp (Nat.dvd_of_mem_primeFactors hp)
    have h2 : ¬ 2 ≤ D.natAbs.factorization p := by
      intro h
      have := (hpp.pow_dvd_iff_le_factorization hN).mpr h
      exact odd_prime_sq_not_dvd hpp hp2 (Int.natCast_dvd.mpr (by simpa using this))
    have : D.natAbs.factorization p = 1 := by omega
    rw [this]; exact odd_one
  · push Not at hodd
    obtain ⟨k, hk⟩ : ∃ k, D.natAbs = 2 ^ k := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hN fun {d} hd hdD =>
      hodd d (Nat.mem_primeFactors.mpr ⟨hd, hdD, hN⟩)⟩
    have hD' : D = -((2 : ℤ) ^ k) := by
      have : (D.natAbs : ℤ) = -D := by omega
      rw [hk] at this; push_cast at this; linarith
    rcases k with _ | _ | _ | _ | k
    · simp at hk; omega
    · simp at hk; omega
    · exact absurd (by rw [hD']; norm_num) h4
    · refine ⟨2, Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by rw [hk]; norm_num, hN⟩, ?_⟩
      rw [hk, Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self]
      decide
    · exfalso
      have h16 : (16 : ℤ) ∣ D := ⟨-(2 ^ k), by rw [hD']; ring⟩
      obtain ⟨c, hc⟩ := h16
      have := fund_cases (D := D)
      omega

/-- **The relation among the ramified classes:** $\Phi$ has a nontrivial kernel. For $D \ne -4$,
$(\sqrt D) = (2\omega - b_D)$ has norm $|D|$, so $\prod_p[\mathfrak r_p]^{v_p(D)} = 1$ with some $v_p(D)$ odd
(`exists_odd_factorization`); for $D = -4$, $\mathfrak r_2 = (1 + \omega)$ is principal. -/
theorem exists_ramHom_eq_one (hD : D < 0) : ∃ e, e ≠ 1 ∧ ramHom hD e = 1 := by
  have hu : ((-1 : ℤˣ)) ≠ 1 := by decide
  by_cases h4 : D = -4
  · -- `1 + ω` has norm `2`
    set z : QOrder D := ⟨1, 1⟩
    have hz : z ≠ 0 := fun h => one_ne_zero (congrArg QuadraticAlgebra.re h)
    have hn : QuadraticAlgebra.norm z = 2 := by
      rw [QuadraticAlgebra.norm_def]
      simp only [z, qa, qb, h4]
      norm_num
    have hNz : Ideal.absNorm (Ideal.span {z}) = 2 := by
      have := absNorm_span_singleton_eq hD hz
      rw [hn] at this
      exact_mod_cast this
    have h0 : Ideal.span {z} ∈ (Ideal (QOrder D))⁰ := mem_nonZeroDivisors_of_absNorm (by rw [hNz]; norm_num)
    have hq : ∀ q : ℕ, q.Prime → q ∣ 2 → q ∣ D.natAbs := fun q hq h2 => by
      rw [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2, h4]; norm_num
    have h2mem : 2 ∈ D.natAbs.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by rw [h4]; norm_num,
      by rw [h4]; norm_num⟩
    refine ⟨fun p => (-1) ^ (Nat.factorization 2 p), fun h => hu ?_, ?_⟩
    · have := congrFun h ⟨2, h2mem⟩
      simp [Nat.prime_two.factorization_self] at this
    · rw [ramHom_eq_mk0 hD two_ne_zero hq _ h0 hNz]
      exact mk0_span_singleton h0
  · -- `√D = 2ω - b_D` has norm `|D|`
    set z : QOrder D := ⟨-qb D, 2⟩
    have hz : z ≠ 0 := fun h => two_ne_zero (congrArg QuadraticAlgebra.im h)
    have hD4 := (IsQuadDisc.fund (D := D)).1
    have hNz : Ideal.absNorm (Ideal.span {z}) = D.natAbs := by
      have := absNorm_span_singleton_eq hD hz
      rw [QuadraticAlgebra.norm_def] at this
      simp only [z] at this
      have hqb : qb D * qb D = qb D := by rcases hD4 with h | h <;> simp [qb, h]
      have e : -qb D * -qb D + qb D * -qb D * 2 - qa D * 2 * 2 = -D := by
        have : 4 * (D / 4) + D % 4 = D := by omega
        linear_combination (-1 : ℤ) * hqb - this
      rw [e, ← Int.ofNat_natAbs_of_nonpos hD.le] at this
      exact_mod_cast this
    have hN : D.natAbs ≠ 0 := by have := three_le_natAbs (D := D); omega
    have h0 : Ideal.span {z} ∈ (Ideal (QOrder D))⁰ := mem_nonZeroDivisors_of_absNorm (by rw [hNz]; exact hN)
    obtain ⟨p, hp, hodd⟩ := exists_odd_factorization hD h4
    refine ⟨fun p => (-1) ^ (D.natAbs.factorization p), fun h => hu ?_, ?_⟩
    · have := congrFun h ⟨p, hp⟩
      simp [hodd.neg_one_pow] at this
    · rw [ramHom_eq_mk0 hD hN (fun q _ h => h) _ h0 hNz]
      exact mk0_span_singleton h0

/-- **$|\mathrm{Cl}(\mathbb{Z}[\omega])[2]| \le 2^{t-1}$** ($D < 0$ fundamental, $t$ prime factors): $\mathrm{Cl}[2]$ lies in the
image of $\Phi : \{\pm 1\}^t \to \mathrm{Cl}$ (`mem_range_ramHom_of_sq_eq_one`), and $\ker\Phi \ne 1$
(`exists_ramHom_eq_one`), so $|\mathrm{im}\,\Phi| = 2^t/|\ker\Phi| \le 2^{t-1}$. -/
theorem card_twoTorsion_order_le (hD : D < 0) :
    Nat.card {x : ClassGroup (QOrder D) // x ^ 2 = 1} ≤ 2 ^ (D.natAbs.primeFactors.card - 1) := by
  have : Finite (ClassGroup (QOrder D)) := Finite.of_equiv _ (classGroupEquiv D).toEquiv.symm
  set t := D.natAbs.primeFactors.card
  have ht : 1 ≤ t := Finset.card_pos.mpr
    (Nat.nonempty_primeFactors.mpr (by have := three_le_natAbs (D := D); omega))
  have hdom : Nat.card (D.natAbs.primeFactors → ℤˣ) = 2 ^ t := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int, Nat.card_eq_fintype_card,
      Fintype.card_coe]
  have hker : 2 ≤ Nat.card (ramHom hD).ker := by
    obtain ⟨e, he, he1⟩ := exists_ramHom_eq_one hD
    have : Nontrivial (ramHom hD).ker := ⟨⟨⟨e, he1⟩, 1, fun h => he (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  have hmul : Nat.card (ramHom hD).ker * Nat.card (ramHom hD).range = 2 ^ t := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hdom]
  have hrange : Nat.card {x : ClassGroup (QOrder D) // x ^ 2 = 1} ≤ Nat.card (ramHom hD).range :=
    Nat.card_le_card_of_injective (fun x => ⟨x.1, mem_range_ramHom_of_sq_eq_one hD x.2⟩)
      fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h)
  have h2t : 2 ^ t = 2 * 2 ^ (t - 1) := by rw [← pow_succ']; congr 1; omega
  have : Nat.card (ramHom hD).range ≤ 2 ^ (t - 1) := by
    have h1 : 2 * Nat.card (ramHom hD).range ≤ 2 * 2 ^ (t - 1) := by
      rw [← h2t, ← hmul]; exact Nat.mul_le_mul_right _ hker
    omega
  exact hrange.trans this

/-! ### Duplication -/

namespace IsFormClassGroup

variable {G : Type*} [CommGroup G] {cls : PosForms D → G} (C : IsFormClassGroup D G cls)
include C

omit [IsQuadDisc D] in
/-- The kernel of squaring is the 2-torsion, and $|G^2|\cdot|G[2]| = |G|$. -/
theorem card_range_sq_mul [Finite G] :
    Nat.card (powMonoidHom 2 : G →* G).range * Nat.card {x : G // x ^ 2 = 1} = Nat.card G := by
  rw [← Subgroup.index_ker, mul_comm, ← Subgroup.card_mul_index (powMonoidHom 2 : G →* G).ker]
  congr 1

/-- **Duplication from a bound on the 2-torsion:** if $|G[2]| \le 2^{t-1}$ then the principal genus
$\ker\gamma$ is exactly $G^2$ (always $G^2 \subseteq \ker\gamma$, `genusHom_sq`, and $|\ker\gamma| = |G|/2^{t-1}$). -/
theorem ker_genusHom_eq_range_sq [Finite G] (hD : D < 0)
    (h2 : Nat.card {x : G // x ^ 2 = 1} ≤ 2 ^ (D.natAbs.primeFactors.card - 1)) :
    C.genusHom.ker = (powMonoidHom 2 : G →* G).range := by
  have hle : (powMonoidHom 2 : G →* G).range ≤ C.genusHom.ker := by
    rintro _ ⟨y, rfl⟩
    exact C.genusHom_sq y
  have hkerγ : Nat.card C.genusHom.ker * 2 ^ (D.natAbs.primeFactors.card - 1) = Nat.card G := by
    rw [← C.card_range_genusHom hD, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hsq := C.card_range_sq_mul
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hpos : 0 < 2 ^ (D.natAbs.primeFactors.card - 1) := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [hkerγ, ← hsq]
  exact Nat.mul_le_mul_left _ h2

/-- **$|G[2]| \ge 2^{t-1}$** for any `IsFormClassGroup` (since $G^2 \subseteq \ker\gamma$ and $|G/\ker\gamma| = 2^{t-1}$). -/
theorem card_twoTorsion_ge [Finite G] (hD : D < 0) :
    2 ^ (D.natAbs.primeFactors.card - 1) ≤ Nat.card {x : G // x ^ 2 = 1} := by
  have hle : (powMonoidHom 2 : G →* G).range ≤ C.genusHom.ker := by
    rintro _ ⟨y, rfl⟩
    exact C.genusHom_sq y
  have hkerγ : Nat.card C.genusHom.ker * 2 ^ (D.natAbs.primeFactors.card - 1) = Nat.card G := by
    rw [← C.card_range_genusHom hD, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hsq := C.card_range_sq_mul
  have hcard := Subgroup.card_le_of_le hle
  have hpos : 0 < Nat.card (powMonoidHom 2 : G →* G).range := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  rw [hsq, ← hkerγ]
  exact Nat.mul_le_mul_right _ hcard

end IsFormClassGroup

/-- $|\mathrm{Cl}(\mathcal O_{K_D})[2]| = |\mathrm{Cl}(\mathbb{Z}[\omega])[2]|$. -/
theorem card_twoTorsion_congr :
    Nat.card {c : ClassGroup (𝓞 (QField D)) // c ^ 2 = 1} = Nat.card {x : ClassGroup (QOrder D) // x ^ 2 = 1} :=
  (Nat.card_congr ((classGroupEquiv D).toEquiv.subtypeEquiv fun c => by
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← map_pow, map_eq_one_iff _ (classGroupEquiv D).injective])).symm

/-- **The number of ambiguous classes** ($D < 0$ fundamental, $t$ prime factors of $D$; Gauss, *Disq. Arith.* §§257–260
[unverified]; Cox, Prop. 3.11 / Cor. 3.14 [unverified locator]):
$$|\mathrm{Cl}(\mathcal O_{K_D})[2]| = \#\{c : c^2 = 1\} = 2^{t-1}.$$
$\le$: `card_twoTorsion_order_le` (ambiguous forms and ramified primes); $\ge$: genus theory
(`IsFormClassGroup.card_twoTorsion_ge`). -/
@[kb "gauss1801" "§§257–260 [unverified]"]
theorem card_twoTorsion (hD : D < 0) :
    Nat.card {c : ClassGroup (𝓞 (QField D)) // c ^ 2 = 1} = 2 ^ (D.natAbs.primeFactors.card - 1) :=
  le_antisymm (card_twoTorsion_congr.trans_le (card_twoTorsion_order_le hD))
    ((isFormClassGroup hD).card_twoTorsion_ge hD)

/-- **Gauss's duplication theorem: the principal genus is $\mathrm{Cl}^2$** ($D < 0$ fundamental; Gauss, *Disq. Arith.*
§286 [unverified]; Cox, Thm. 3.15 and Cor. 3.14 [unverified locator]): the kernel of the genus homomorphism
$\gamma : \mathrm{Cl}(\mathcal O_{K_D}) \to \{\pm 1\}^t$, $[\mathfrak a_f] \mapsto (\chi_p(f))_{p \mid D}$, is the subgroup of squares:
$$\ker\gamma = \mathrm{Cl}(\mathcal O_{K_D})^2 .$$
So a form lies in the principal genus iff its class is a square, and each genus is a coset of $\mathrm{Cl}^2$. -/
@[kb "gauss1801" "§286 [unverified]"]
theorem principalGenus_eq_sq (hD : D < 0) :
    (isFormClassGroup hD).genusHom.ker = (powMonoidHom 2 : ClassGroup (𝓞 (QField D)) →* _).range :=
  (isFormClassGroup hD).ker_genusHom_eq_range_sq hD ((card_twoTorsion hD).le)

/-- **A class is in the principal genus iff it is a square** (`principalGenus_eq_sq`, elementwise). -/
theorem genusHom_eq_one_iff (hD : D < 0) (x : ClassGroup (𝓞 (QField D))) :
    (isFormClassGroup hD).genusHom x = 1 ↔ ∃ y, y ^ 2 = x := by
  rw [← MonoidHom.mem_ker, principalGenus_eq_sq hD]
  rfl

/-- **The number of $\mathrm{GL}_2(\mathbb{Z})$-classes** ($D < 0$ fundamental): with `two_mul_card_glClasses`,
$$2\,\#\{\mathrm{GL}_2(\mathbb{Z})\text{-classes of primitive positive definite forms of discriminant } D\} = h + 2^{t-1}.$$ -/
theorem two_mul_card_glClasses' (hD : D < 0) :
    2 * Nat.card (Quotient (glSetoid D)) = classNumber (QField D) + 2 ^ (D.natAbs.primeFactors.card - 1) := by
  rw [two_mul_card_glClasses hD, card_twoTorsion hD]

end QuadFormsKB.Binary
