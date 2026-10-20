import QuadFormsKB.Analysis.TraceLocalGlobal

/-!
# The global standard character of a number field

Notation: $e(t) = e^{2\pi i t}$ (`𝐞`), $\psi_p(x) = e(-\{x\}_p)$ on $\mathbb{Q}_p$ (`psiP`), and
$\psi_v = \psi_p \circ \operatorname{Tr}_{F_v/\mathbb{Q}_p}$ on $F_v$ (`psiV`), as in `LocalFourier.lean` and `LocalFourierNF.lean`.

* `fourierChar_mul_finprod_psiP`: **the product formula over $\mathbb{Q}$**, $e(r)\prod_p\psi_p(r) = 1$ for
  $r \in \mathbb{Q}$. Proof: $\Phi(r) = e(r)\prod_p\psi_p(r)$ is additive; it is $1$ on $\mathbb{Z}[1/p]$; and every
  $r$ is a sum of such pieces (Bezout on the denominator, strong induction).
* `finprod_psiV_eq`, `fourierChar_trace_mul_finprod_psiV`, `finprod_psiV_eq_fourierChar`: **the product
  formula over $F$**, $e(\operatorname{Tr}_{F/\mathbb{Q}}x)\prod_v\psi_v(x) = 1$ for $x \in F$, i.e. the character
  $\psi = \psi_\infty\otimes\bigotimes_v\psi_v$ of $\mathbb{A}_F$ with $\psi_\infty = e\circ\operatorname{Tr}$ is trivial on $F$.
  Proof: group the places by the prime below and use `prod_psiV_Sp`.
* `trace_int_iff_forall_mem_invDiffV`: $x \in F$ satisfies $\operatorname{Tr}(x\mathcal O_F) \subseteq \mathbb{Z}$ iff
  $x \in \mathfrak d_v^{-1}$ (= `invDiffV v`, the conductor of $\psi_v$) for every $v$. This links the local
  $d_v$ (`diffExp`) to the global inverse different.

Sources: Tate's thesis, Cassels–Fröhlich Ch. XV, §2.2 and §4.1 (Lemma 4.1.5) [unverified]; Weil, *Basic Number
Theory*, Ch. IV §2 and Ch. VIII §4 [unverified].
-/

open IsDedekindDomain NumberField WithZero
open scoped Real FourierTransform

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

/-- $p$ is prime for $p$ in `Nat.Primes`. -/
instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ### The product formula for $\psi$ over $\mathbb{Q}$ -/

lemma psiP_rat_eq_one_of_not_dvd {p : ℕ} [Fact p.Prime] {r : ℚ} (h : ¬p ∣ r.den) :
    psiP (r : ℚ_[p]) = 1 :=
  (psiP_eq_one_iff _).mpr (Padic.norm_rat_le_one h)

lemma hasFiniteMulSupport_psiP (r : ℚ) :
    Function.HasFiniteMulSupport fun p : Nat.Primes => psiP (p := p) (r : ℚ_[p]) := by
  refine (Set.Finite.preimage (f := fun p : Nat.Primes => (p : ℕ))
    (fun a _ b _ h => Subtype.ext h) (Set.finite_le_nat r.den)).subset fun p hp => ?_
  rw [Function.mem_mulSupport] at hp
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  by_contra h
  exact hp (psiP_rat_eq_one_of_not_dvd fun hd => h (Nat.le_of_dvd r.den_pos hd))

/-- $\Phi(r) = e(r)\prod_p \psi_p(r)$. -/
def phiQ (r : ℚ) : Circle := 𝐞 (r : ℝ) * ∏ᶠ p : Nat.Primes, psiP (p := p) (r : ℚ_[p])

lemma phiQ_add (r s : ℚ) : phiQ (r + s) = phiQ r * phiQ s := by
  unfold phiQ
  have h : (fun p : Nat.Primes => psiP (p := p) (((r + s : ℚ)) : ℚ_[p])) =
      fun p : Nat.Primes => psiP (p := p) (r : ℚ_[p]) * psiP (p := p) (s : ℚ_[p]) := by
    funext p; rw [Rat.cast_add, AddChar.map_add_eq_mul]
  rw [h, finprod_mul_distrib (hasFiniteMulSupport_psiP r) (hasFiniteMulSupport_psiP s),
    Rat.cast_add, AddChar.map_add_eq_mul]
  ac_rfl

lemma phiQ_pFrac {p : ℕ} [hp : Fact p.Prime] {r : ℚ} (hr : IsPFrac p r) : phiQ r = 1 := by
  unfold phiQ
  obtain ⟨n, k, rfl⟩ := hr
  rw [@finprod_eq_single _ Nat.Primes _ _ (⟨p, hp.out⟩ : Nat.Primes)]
  · change _ * psiP (p := p) _ = 1
    rw [psiP_pFrac ⟨n, k, rfl⟩, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  · intro ℓ hℓ
    refine psiP_rat_eq_one_of_not_dvd fun hd => hℓ (Subtype.ext ?_)
    have h1 : ((n : ℚ) / (p : ℚ) ^ k).den ∣ p ^ k := by
      have := Rat.den_dvd n ((p : ℤ) ^ k)
      rw [Rat.divInt_eq_div] at this
      push_cast at this
      exact_mod_cast this
    exact (Nat.prime_dvd_prime_iff_eq ℓ.2 hp.out).mp (ℓ.2.dvd_of_dvd_pow (hd.trans h1))

/-- **The product formula for the standard character of $\mathbb{Q}$:** $e(r)\prod_p\psi_p(r) = 1$ for $r \in \mathbb{Q}$
(only finitely many factors differ from $1$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.1, Lemma 4.1.5 [unverified]"]
theorem fourierChar_mul_finprod_psiP (r : ℚ) :
    𝐞 (r : ℝ) * ∏ᶠ p : Nat.Primes, psiP (p := p) (r : ℚ_[p]) = 1 := by
  change phiQ r = 1
  induction hn : r.den using Nat.strong_induction_on generalizing r with
  | _ n ih =>
  subst hn
  by_cases h1 : r.den = 1
  · have : r = (r.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den r]
      rw [h1]; simp
    rw [this]
    exact phiQ_pFrac (p := 2) ⟨r.num, 0, by simp⟩
  · set p := r.den.minFac
    have hp : p.Prime := Nat.minFac_prime h1
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, c, hpc, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd r.den_pos.ne' p hp.one_lt.ne'
    have he : e ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hden
      exact hpc (hden ▸ Nat.minFac_dvd r.den)
    have hcop : IsCoprime ((p ^ e : ℕ) : ℤ) (c : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpc)))
    obtain ⟨u, w, huw⟩ := hcop
    have hc0 : (c : ℚ) ≠ 0 := by
      have : c ≠ 0 := by rintro rfl; rw [mul_zero] at hden; exact r.den_pos.ne' hden
      exact_mod_cast this
    have hpe0 : ((p : ℚ) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    have hsplit : r = (r.num * w : ℤ) / (p : ℚ) ^ e + ((r.num * u : ℤ) : ℚ) / (c : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den r]
      rw [hden]
      have huw' : (u : ℚ) * ((p : ℚ) ^ e) + (w : ℚ) * c = 1 := by exact_mod_cast huw
      push_cast
      rw [div_add_div _ _ hpe0 hc0, div_eq_div_iff (mul_ne_zero hpe0 hc0) (mul_ne_zero hpe0 hc0)]
      linear_combination (-(r.num : ℚ) * ((p : ℚ) ^ e * c)) * huw'
    rw [hsplit, phiQ_add, phiQ_pFrac ⟨r.num * w, e, rfl⟩, one_mul]
    refine ih _ ?_ _ rfl
    have hdvd : (((r.num * u : ℤ) : ℚ) / (c : ℚ)).den ∣ c := by
      have := Rat.den_dvd (r.num * u) (c : ℤ)
      rw [Rat.divInt_eq_div] at this
      push_cast at this ⊢
      exact_mod_cast this
    have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; exact hc0 (by simp))
    calc _ ≤ c := Nat.le_of_dvd hcpos hdvd
      _ < p ^ e * c := by
          have : 1 < p ^ e := Nat.one_lt_pow he hp.one_lt
          nlinarith
      _ = r.den := hden.symm

/-! ### The product formula for $\psi$ over $F$ -/

variable {F : Type} [Field F] [NumberField F]

/-- The prime below $v$, as an element of `Nat.Primes`. -/
def primeBelow (v : HeightOneSpectrum (𝓞 F)) : Nat.Primes := ⟨resChar v, Fact.out⟩

lemma psiV_eq_one_of_not_mem_support (x : F) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ HeightOneSpectrum.Support (𝓞 F) x) : psiV v (algebraMap F (v.adicCompletion F) x) = 1 := by
  refine psiV_eq_one_of_le_one v ?_
  rw [HN.valued_algebraMap]
  simpa [HeightOneSpectrum.Support] using hv

lemma hasFiniteMulSupport_psiV (x : F) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      psiV v (algebraMap F (v.adicCompletion F) x) :=
  (HeightOneSpectrum.Support.finite (𝓞 F) x).subset fun v hv => by
    by_contra h
    exact hv (psiV_eq_one_of_not_mem_support x h)

/-- $\prod_v \psi_v(x) = \prod_p \psi_p(\operatorname{Tr}_{F/\mathbb{Q}}x)$ (grouping the places by the prime below). -/
theorem finprod_psiV_eq (x : F) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), psiV v (algebraMap F (v.adicCompletion F) x) =
      ∏ᶠ p : Nat.Primes, psiP (p := p) (((Algebra.trace ℚ F x : ℚ)) : ℚ_[p]) := by
  classical
  set f : HeightOneSpectrum (𝓞 F) → Circle := fun v => psiV v (algebraMap F (v.adicCompletion F) x)
  have hS := HeightOneSpectrum.Support.finite (𝓞 F) x
  set T : Finset Nat.Primes := hS.toFinset.image primeBelow
  -- all places above the primes in `T`
  have hfinT : ∀ p ∈ T, (Set.univ : Set (Sp F p)).Finite := fun p _ => Set.toFinite _
  set S' : Finset (HeightOneSpectrum (𝓞 F)) :=
    T.biUnion fun p => (Finset.univ : Finset (Sp F p)).map ⟨Subtype.val, Subtype.val_injective⟩
  have hmemS' : ∀ v, v ∈ S' ↔ primeBelow v ∈ T := by
    intro v
    simp only [S', Finset.mem_biUnion, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨p, hp, w, rfl⟩
      have : primeBelow w.1 = p := Subtype.ext w.2
      rwa [this]
    · intro h
      exact ⟨primeBelow v, h, ⟨v, rfl⟩, rfl⟩
  have hsuppS : Function.mulSupport f ⊆ S' := by
    intro v hv
    rw [Finset.mem_coe, hmemS']
    refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    by_contra h
    exact hv (psiV_eq_one_of_not_mem_support x h)
  have hg : ∀ p : Nat.Primes, ∏ w : Sp F p, f w.1 =
      psiP (p := p) (((Algebra.trace ℚ F x : ℚ)) : ℚ_[p]) := fun p => prod_psiV_Sp (p : ℕ) x
  rw [finprod_eq_prod_of_mulSupport_subset f hsuppS,
    finprod_eq_prod_of_mulSupport_subset (s := T) _ ?_]
  · rw [← Finset.prod_fiberwise_of_maps_to (g := primeBelow) (t := T)
      (fun v hv => (hmemS' v).mp hv)]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [← hg p]
    refine Finset.prod_bij' (fun v hv => ⟨v, congrArg Subtype.val (Finset.mem_filter.mp hv).2⟩)
      (fun w _ => w.1) (fun _ _ => Finset.mem_univ _) (fun w _ => ?_) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl)
    refine Finset.mem_filter.mpr ⟨(hmemS' w.1).mpr ?_, Subtype.ext w.2⟩
    have : primeBelow w.1 = p := Subtype.ext w.2
    rwa [this]
  · intro p hp
    rw [Function.mem_mulSupport, ← hg p] at hp
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_one_of_prod_ne_one hp
    have : w.1 ∈ S' := hsuppS hw
    rw [hmemS'] at this
    have h2 : primeBelow w.1 = p := Subtype.ext w.2
    rwa [h2] at this

/-- **The product formula for the standard character of $F$:** for $x \in F$,
$\psi_\infty(x)\prod_v\psi_v(x) = 1$, where $\psi_\infty(x) = e(\operatorname{Tr}_{F/\mathbb{Q}}x)$ and $v$ runs
over the finite places (only finitely many factors differ from $1$). Equivalently
$\prod_v \psi_v(x) = e(-\operatorname{Tr}_{F/\mathbb{Q}}x)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.1, Lemma 4.1.5 [unverified]"]
theorem fourierChar_trace_mul_finprod_psiV (x : F) :
    𝐞 ((Algebra.trace ℚ F x : ℚ) : ℝ) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), psiV v (algebraMap F (v.adicCompletion F) x) = 1 := by
  rw [finprod_psiV_eq]
  exact fourierChar_mul_finprod_psiP _

theorem finprod_psiV_eq_fourierChar (x : F) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), psiV v (algebraMap F (v.adicCompletion F) x) =
      𝐞 (-((Algebra.trace ℚ F x : ℚ) : ℝ)) := by
  have h := fourierChar_trace_mul_finprod_psiV x
  rw [AddChar.map_neg_eq_inv]
  exact eq_inv_of_mul_eq_one_right h

/-! ### The inverse different, locally and globally -/

/-- A rational $r$ with $\psi_p(r) = 1$ for every $p$ is an integer. -/
lemma rat_isInt_of_psiP (r : ℚ) (h : ∀ p : Nat.Primes, psiP (p := p) (r : ℚ_[p]) = 1) :
    ∃ m : ℤ, r = m := by
  have h1 := fourierChar_mul_finprod_psiP r
  rw [finprod_eq_one_of_forall_eq_one h, mul_one, fourierChar_eq_one_iff] at h1
  obtain ⟨m, hm⟩ := h1
  exact ⟨m, by exact_mod_cast hm⟩

/-- An element of $F_v$ has valuation $\le \exp(k)$ for some $k \in \mathbb{N}$. -/
lemma exists_valued_le_exp {v : HeightOneSpectrum (𝓞 F)} (y : v.adicCompletion F) :
    ∃ k : ℕ, Valued.v y ≤ exp (k : ℤ) := by
  by_cases h0 : y = 0
  · exact ⟨0, by rw [h0, map_zero]; exact zero_le⟩
  obtain ⟨k, hk⟩ := HN.exists_exp_eq v h0
  exact ⟨k.toNat, by rw [hk, exp_le_exp]; exact Int.self_le_toNat k⟩

/-- **The inverse different, locally:** $x \in F$ lies in $\mathfrak d_{F/\mathbb{Q}}^{-1} =
\{x : \operatorname{Tr}_{F/\mathbb{Q}}(x\mathcal O_F) \subseteq \mathbb{Z}\}$ iff $x \in \mathfrak d_v^{-1}$ = `invDiffV v` (i.e.
$v(x) \le \exp(d_v)$, `mem_invDiffV_iff`) at every finite place $v$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 and §4.1 [unverified]"]
theorem trace_int_iff_forall_mem_invDiffV (x : F) :
    (∀ a : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (x * a) = m) ↔
      ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) x ∈ invDiffV v := by
  constructor
  · intro h v
    set p := resChar v
    intro y hy
    -- bounds for `x` at the places above `p`
    choose k hk using fun w : Sp F p => exists_valued_le_exp (algebraMap F (w.1.adicCompletion F) x)
    set N := Finset.univ.sup k
    have hsmall : ∀ w : Sp F p, ∀ z : w.1.adicCompletion F, Valued.v z ≤ exp (-(N : ℤ)) →
        Valued.v (z * algebraMap F (w.1.adicCompletion F) x) ≤ 1 := by
      intro w z hz
      rw [map_mul]
      calc Valued.v z * Valued.v (algebraMap F (w.1.adicCompletion F) x)
          ≤ exp (-(N : ℤ)) * exp (k w : ℤ) := mul_le_mul' hz (hk w)
        _ ≤ 1 := by
          rw [← exp_add, ← exp_zero, exp_le_exp]
          have : k w ≤ N := Finset.le_sup (Finset.mem_univ w)
          omega
    let v' : Sp F p := ⟨v, rfl⟩
    classical
    let t : ∀ w : Sp F p, w.1.adicCompletion F := fun w =>
      if hw : w = v' then (hw ▸ y : w.1.adicCompletion F) else 0
    have ht : ∀ w, Valued.v (t w) ≤ 1 := by
      intro w
      by_cases hw : w = v'
      · subst hw; simp only [t, dite_true]; exact hy
      · simp only [t, hw, dite_false, map_zero]; exact zero_le
    obtain ⟨a, ha⟩ := exists_int_approx_Sp p t ht N
    -- `ψ_p(Tr(x a)) = 1`
    obtain ⟨m, hm⟩ := h a
    have h1 := prod_psiV_Sp (F := F) p (x * a)
    rw [hm, Rat.cast_intCast, (psiP_eq_one_iff _).mpr (Padic.norm_int_le_one m)] at h1
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v')] at h1
    have h2 : ∏ w ∈ Finset.univ.erase v', psiV w.1 (algebraMap F (w.1.adicCompletion F) (x * a)) = 1 := by
      refine Finset.prod_eq_one fun w hw => psiV_eq_one_of_le_one w.1 ?_
      have hwv : w ≠ v' := Finset.ne_of_mem_erase hw
      have := ha w
      simp only [t, hwv, dite_false, zero_sub, Valuation.map_neg] at this
      rw [map_mul, mul_comm]
      exact hsmall w _ this
    rw [h2, mul_one] at h1
    -- `ψ_v(y x) = ψ_v(a x) ψ_v((y - a) x) = 1`
    have hav := ha v'
    simp only [t, dite_true] at hav
    have e : y * algebraMap F (v.adicCompletion F) x =
        algebraMap F (v.adicCompletion F) (x * a) +
          (y - algebraMap F (v.adicCompletion F) (a : F)) * algebraMap F (v.adicCompletion F) x := by
      rw [map_mul]; ring
    rw [e, AddChar.map_add_eq_mul]
    change psiV v (algebraMap F (v.adicCompletion F) (x * a)) * _ = 1 at *
    rw [h1, one_mul]
    exact psiV_eq_one_of_le_one v (hsmall v' _ hav)
  · intro h a
    refine rat_isInt_of_psiP _ fun p => ?_
    rw [← prod_psiV_Sp]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [map_mul, mul_comm]
    refine h w.1 _ ?_
    rw [HN.valued_algebraMap]
    exact w.1.valuation_le_one (K := F) a

end

end QuadFormsKB.Analysis
