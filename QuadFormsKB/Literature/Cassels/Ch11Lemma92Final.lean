/-
# Cassels, Chapter 11, Lemma 9.2: the global construction and the proof

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Lemma 9.2, pp. 245–249: the choice
of $g_1$ and of the auxiliary primes $\pi$ and $p(0)$ ((9.38)–(9.40), with Dirichlet's theorem on primes in arithmetic
progressions, footnote p. 246), the vector $\mathbf u$ by Theorem 8.1 ((9.41)), and the lattice $\Gamma$.

**Proves.**
* `exists_dirichlet_prime`: for a finite set $T_0$ of primes, exponents $k_p$ and residues $R_p$ prime to $p$ there is a prime
  $p_0 > B$ with $\bigl(\prod_{p' \in T_0, p' \ne p} p'^{k_{p'}}\bigr)p_0 \equiv R_p \pmod{p^3}$ for every $p \in T_0$ (so that
  $g_1 = p_0\prod p^{k_p}$ lies in prescribed square classes, (9.39₁), (9.40)).
* `exists_g1`, `exists_approx_vector`, `exists_pow_mul_int`, `exists_u_of_targets`: the number $g_1 = p_0c$, the auxiliary
  primes $\pi$ ($d \in U_\pi^2$, no Dirichlet needed) and $p_0$, and the vector $\mathbf u = \pi^l\mathbf y$ with prescribed
  $p$-adic approximations ((9.38)–(9.41)).
* `exists_datum_of_targets`: for one choice of local targets ("type"), the datum of the final stage: the local lattices
  $\Gamma_p$ in the cases (a) (`pkgCaseA`), (b) (`pkgCaseB`), (c₁) $p = \pi$ (`pkgPi`), (c₂) $p = p(0)$ (`pkgP0`), the condition
  at $q$, glued by `exists_family_of_pkgs`.
* `exists_options`, `exists_options_q`: finitely many local targets at each prime of $P \cup \{q\}$ cover every $a$
  primitively represented over $\mathbb Z_p$ (Lemma 9.3 at isotropic primes, a bound on the valuation at anisotropic ones).
* `lemma92FamilyStatement_holds`, **`lemma92_holds : Lemma92`** (unconditional), and
  **`tartakowskyClassicalAt_four_holds`** (Theorem 1.6 for $n = 4$, classically integral forms, unconditional).

*Update (simplification), p. 246:* Cassels moves $\mathbf t$ to $\mathbf u$ by an automorph $\sigma$ of $f$; here the shape of
Lemma 9.3 is transported directly (`Shape93.perturb`: if $f(\mathbf y) = f(\mathbf t)$ and $\mathbf y \equiv \mathbf t \pmod{p^{\mu+2}}$,
the projection of $\Delta$ to $\mathbf y^\perp$ has the same shape). *Update (clarification), p. 248:* the choice of $b$ ("left to
the reader") is made by local conditions modulo $p^{N_p}$ at each $p \in P^*$ and the Chinese remainder theorem
(`exists_family_of_pkgs`); at $p(0)$ the sign of $\mathbf c$ is chosen afterwards, as in Cassels.
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92Types
import QuadFormsKB.Literature.Cassels.Ch11Lemma91

open NumberField IsDedekindDomain Matrix QuadFormsKB.Cassels.Ch11L93

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

/-- **The prime $p(0)$** (Cassels (9.39)–(9.40), by Dirichlet's theorem, Mathlib `Nat.forall_exists_prime_gt_and_zmodEq`):
given a finite set $T_0$ of primes, exponents $k$ and residues $R_p$ with $p \nmid R_p$, there is a prime $p_0 > B$ with
$c_p p_0 \equiv R_p \pmod{p^3}$ for all $p \in T_0$, where $c_p = \prod_{p' \in T_0 \setminus \{p\}} p'^{k_{p'}}$. -/
theorem exists_dirichlet_prime (T0 : Finset ℕ) (hT0 : ∀ p ∈ T0, p.Prime) (k : ℕ → ℕ) (R : ℕ → ℤ)
    (hR : ∀ p ∈ T0, ¬ (p : ℤ) ∣ R p) (B : ℕ) :
    ∃ p0 : ℕ, p0.Prime ∧ B < p0 ∧
      ∀ p ∈ T0, (∏ p' ∈ T0.erase p, (p' : ℤ) ^ k p') * p0 ≡ R p [ZMOD ((p ^ 3 : ℕ) : ℤ)] := by
  classical
  set c : ℕ → ℤ := fun p => ∏ p' ∈ T0.erase p, (p' : ℤ) ^ k p' with hc
  have hcop : ∀ p ∈ T0, IsCoprime (c p) ((p ^ 3 : ℕ) : ℤ) := by
    intro p hp
    push_cast
    refine IsCoprime.pow_right (IsCoprime.prod_left fun p' hp' => IsCoprime.pow_left ?_)
    have hne : p' ≠ p := (Finset.mem_erase.mp hp').1
    have := (Nat.coprime_primes (hT0 p' (Finset.mem_erase.mp hp').2) (hT0 p hp)).mpr hne
    exact Nat.isCoprime_iff_coprime.mpr this
  -- `r_p` with `c_p r_p ≡ R_p`
  have hr : ∀ p ∈ T0, ∃ rp : ℤ, c p * rp ≡ R p [ZMOD ((p ^ 3 : ℕ) : ℤ)] := by
    intro p hp
    obtain ⟨s, t, hst⟩ := hcop p hp
    refine ⟨s * R p, Int.modEq_iff_dvd.mpr ⟨t * R p, by linear_combination (-(R p)) * hst⟩⟩
  choose! rp hrp using hr
  obtain ⟨r, hr'⟩ := Ch11Sec9Steps.exists_int_modEq_primePow T0 hT0 (fun _ => 3) rp
  set M : ℕ := ∏ p ∈ T0, p ^ 3 with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hT0 p hp).ne_zero
  have hrM : IsCoprime r (M : ℤ) := by
    rw [hM]; push_cast
    refine IsCoprime.prod_right fun p hp => IsCoprime.pow_right ?_
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (hT0 p hp)
    refine IsCoprime.symm ((Prime.irreducible hpp).coprime_iff_not_dvd.mpr fun hd => hR p hp ?_)
    have h1 : (p : ℤ) ∣ r - rp p := (dvd_pow_self (p : ℤ) (by norm_num : 3 ≠ 0)).trans
      (by have := (hr' p hp).symm.dvd; push_cast at this ⊢; exact this)
    have h2 : (p : ℤ) ∣ rp p := by have := dvd_sub hd h1; simpa using this
    have h3 : (p : ℤ) ∣ R p - c p * rp p := (dvd_pow_self (p : ℤ) (by norm_num : 3 ≠ 0)).trans
      (by have := (hrp p hp).dvd; push_cast at this ⊢; exact this)
    have := dvd_add h3 (Dvd.dvd.mul_left h2 (c p))
    simpa using this
  obtain ⟨p0, hp0B, hp0, hp0r⟩ := Nat.forall_exists_prime_gt_and_zmodEq B hM0 hrM
  refine ⟨p0, hp0, hp0B, fun p hp => ?_⟩
  have hdvd : ((p ^ 3 : ℕ) : ℤ) ∣ (M : ℤ) := by exact_mod_cast Finset.dvd_prod_of_mem _ hp
  have h1 : (p0 : ℤ) ≡ rp p [ZMOD ((p ^ 3 : ℕ) : ℤ)] := (hp0r.of_dvd hdvd).trans (hr' p hp)
  exact ((h1.mul_left (c p)).trans (hrp p hp))

section Approx

open QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **Theorem 8.1 applied to $f$** (Cassels, (9.41)): let $f$ be positive definite with $\det H_f \ne 0$, $T_0$ a finite set of
primes containing all $p \mid 2\det H_f$, $\pi \notin T_0$ a prime with $\pi \nmid 2\det H_f$, $g_1 > 0$, and at each place $v$
over $T_0$ a local vector $z_v$ with $f(z_v) = g_1$. Then for every $K$ there is $y \in \mathbb Q^4$ with $f(y) = g_1$, $y \equiv z_v$
modulo $p^K$ at the places over $T_0$, and $y$ integral at every other place $\ne \pi$. *Proof:* $g_1$ is represented over $\mathbb Q$
(Hasse–Minkowski), and `Lattices.vecApproxAt_of_isotropicAt` away from $\pi$ ($f$ is unimodular, hence isotropic, at $\pi$). -/
theorem exists_approx_vector (f : QuadForm ℤ 4) (hf : IntQF.PosDef f) (T0 : Finset ℕ) (hT0 : ∀ p ∈ T0, p.Prime)
    (hbad : ∀ p : ℕ, p.Prime → p ∉ T0 → ¬ (p : ℤ) ∣ 2 * f.hessian.det) {π : ℕ} (hπ : π.Prime) (hπT : π ∉ T0)
    {g1 : ℤ} (hg1 : 0 < g1) (z : ∀ v : HeightOneSpectrum (𝓞 ℚ), Fin 4 → v.adicCompletion ℚ)
    (hz : ∀ v, Rat.HeightOneSpectrum.natGenerator v ∈ T0 →
      (f.map (Int.castRingHom ℚ)).evalIn _ (z v) = algebraMap ℚ _ (g1 : ℚ)) (K : ℤ) :
    ∃ y : Fin 4 → ℚ, (f.map (Int.castRingHom ℚ)).eval y = g1 ∧
      (∀ v, Rat.HeightOneSpectrum.natGenerator v ∈ T0 → locVec v y - z v ∈ ball v K) ∧
      (∀ v, Rat.HeightOneSpectrum.natGenerator v ∉ T0 → v ≠ placeOf π hπ → locVec v y ∈ std v) := by
  classical
  set Qq := f.map (Int.castRingHom ℚ) with hQq
  have hQ : Qq.Nondegenerate :=
    nondegenerate_map_of_det_ne_zero f (IntQF.PosDef.nondegenerate hf)
  have hg10 : (g1 : ℚ) ≠ 0 := by exact_mod_cast hg1.ne'
  -- local representations at the places outside `T0`
  have hloc_out : ∀ v, Rat.HeightOneSpectrum.natGenerator v ∉ T0 →
      ∃ y ∈ std v, Qq.evalIn (v.adicCompletion ℚ) y = algebraMap ℚ _ (g1 : ℚ) := by
    intro v hv
    set p := Rat.HeightOneSpectrum.natGenerator v
    have : Fact p.Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    have hb := hbad p (Rat.HeightOneSpectrum.prime_natGenerator v) hv
    have hp2 : p ≠ 2 := by
      intro h2; apply hb; rw [show (p : ℤ) = 2 by exact_mod_cast h2]; exact dvd_mul_right _ _
    obtain ⟨x, -, hx⟩ := exists_primitive_padic_of_unimodular p hp2 f
      (fun hd => hb (dvd_mul_of_dvd_right hd _)) (by norm_num) g1
    exact exists_mem_std_of_padic f v p rfl ⟨x, hx⟩
  -- `g₁` is represented over `ℚ`
  have hrat : Qq.RepresentsIn ℚ (g1 : ℚ) := by
    rw [represents_iff_everywhere_nf _ hQ _ hg10]
    intro w
    cases w with
    | infinite w =>
      exact representsIn_congr_alg _ _ _ _
        (representsIn_inf_of_real f (Ch11Sec9Gamma.exists_real_rep f hf (by norm_num) g1 hg1) w)
    | finite v =>
      by_cases hv : Rat.HeightOneSpectrum.natGenerator v ∈ T0
      · exact ⟨z v, hz v hv⟩
      · obtain ⟨y, -, hy⟩ := hloc_out v hv
        exact ⟨y, hy⟩
  obtain ⟨u0, hu0⟩ := hrat
  have hu0' : Qq.evalIn ℚ u0 = g1 := by simpa using hu0
  have hu0ne : u0 ≠ 0 := by
    rintro rfl; apply hg10; rw [← hu0']; simp [QuadForm.evalIn]
  -- the finite set `T` of places
  have hfin1 : {v : HeightOneSpectrum (𝓞 ℚ) | Rat.HeightOneSpectrum.natGenerator v ∈ T0}.Finite := finite_places T0
  have hfin2 : {v : HeightOneSpectrum (𝓞 ℚ) | locVec v u0 ∉ std v}.Finite := by
    have := eventually_locPrimitive (intVec_isLattice (F := ℚ) (n := 4)) hu0ne
    rw [Filter.eventually_cofinite] at this
    refine this.subset fun v hv h => hv ?_
    have := h.1; rw [loc_intVec] at this; exact this
  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) := (hfin1.union hfin2).toFinset with hT
  -- targets and neighbourhoods
  choose yo hyo hyov using hloc_out
  let zz : ∀ v : HeightOneSpectrum (𝓞 ℚ), Fin 4 → v.adicCompletion ℚ := fun v =>
    if hv : Rat.HeightOneSpectrum.natGenerator v ∈ T0 then z v else yo v hv
  have hzz : ∀ v ∈ T, Qq.evalIn (v.adicCompletion ℚ) (zz v) = algebraMap ℚ _ (Qq.evalIn ℚ u0) := by
    intro v _
    rw [hu0']
    simp only [zz]
    split_ifs with hv
    · exact hz v hv
    · exact hyov v hv
  let Z : ∀ v : HeightOneSpectrum (𝓞 ℚ), Set (Fin 4 → v.adicCompletion ℚ) := fun v =>
    if Rat.HeightOneSpectrum.natGenerator v ∈ T0 then {x | x - zz v ∈ ball v K} else {x | x - zz v ∈ ball v 0}
  have hZ : ∀ v ∈ T, Z v ∈ nhds (zz v) := by
    intro v _
    simp only [Z]
    split_ifs
    · exact ball_add_mem_nhds v (zz v) K
    · exact ball_add_mem_nhds v (zz v) 0
  -- isotropy at `π`
  have hiso : Qq.IsotropicIn ((placeOf π hπ).adicCompletion ℚ) := by
    have : Fact π.Prime := ⟨hπ⟩
    have hb := hbad π hπ hπT
    have hp2 : π ≠ 2 := by
      intro h2; apply hb; rw [show (π : ℤ) = 2 by exact_mod_cast h2]; exact dvd_mul_right _ _
    obtain ⟨x, ⟨i, hi⟩, hx⟩ := exists_primitive_padic_of_unimodular π hp2 f
      (fun hd => hb (dvd_mul_of_dvd_right hd _)) (by norm_num) 0
    refine isotropicIn_adicCompletion_of_padic Qq (placeOf π hπ) π (natGenerator_placeOf π hπ).symm
      ⟨fun j => (x j : ℚ_[π]), ?_, ?_⟩
    · intro h0
      have h1 := congrFun h0 i
      simp only [Pi.zero_apply, PadicInt.coe_eq_zero] at h1
      exact hi.ne_zero h1
    · rw [evalIn_castHom_rat]
      have := hom_eval_castHom f PadicInt.Coe.ringHom x
      rw [hx] at this
      simpa using this.symm
  have hVA := vecApproxAt_of_isotropicAt (m := 3) Qq le_rfl hQ (placeOf π hπ) hiso
  obtain ⟨y, hy, hyZ, hyout⟩ := hVA u0 (by rw [hu0']; exact hg10) T
    (fun v hvT _ => by
      by_contra h
      exact hvT (by simp only [hT, Set.Finite.mem_toFinset]; exact Or.inr h))
    zz hzz Z hZ
  refine ⟨y, by rw [← hu0']; exact hy, fun v hv => ?_, fun v hv hvπ => ?_⟩
  · have hvT : v ∈ T := by simp only [hT, Set.Finite.mem_toFinset]; exact Or.inl hv
    have hvπ : v ≠ placeOf π hπ := by
      intro h; apply hπT; rw [h, natGenerator_placeOf] at hv; exact hv
    have := hyZ v hvT hvπ
    simp only [Z, hv, if_true, zz, dif_pos hv] at this
    exact this
  · by_cases hvT : v ∈ T
    · have := hyZ v hvT hvπ
      simp only [Z, hv, if_false, zz, dif_neg hv] at this
      -- `y - yo ∈ ball 0 = std` and `yo ∈ std`
      have h1 : locVec v y = (locVec v y - yo v hv) + yo v hv := by abel
      rw [h1]
      refine (std v).add_mem (fun i => ?_) (hyo v hv)
      have := this i; simpa using this
    · exact hyout v hvT hvπ

/-- Helper: a nonzero element of $\mathbb Q_v$ has valuation $e^k$ for some integer $k$. -/
theorem exists_valued_eq_exp {v : HeightOneSpectrum (𝓞 ℚ)} {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    ∃ k : ℤ, Valued.v x = WithZero.exp k := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
  exact ⟨Multiplicative.toAdd a, by rw [← ha]; rfl⟩

/-- **Clearing the denominator at $\pi$** ((9.41): $\mathbf u = \pi^l\mathbf y$): if $y \in \mathbb Q^4$ is integral at every place
$\ne \pi$, there are $l \ge 0$ and $u \in \mathbb Z^4$ with $u = \pi^l y$, and $u$ is primitive at $\pi$ if $l > 0$. -/
theorem exists_pow_mul_int (y : Fin 4 → ℚ) {π : ℕ} (hπ : π.Prime)
    (hy : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ placeOf π hπ → locVec v y ∈ std v) :
    ∃ (l : ℕ) (u : Fin 4 → ℤ), (fun i => (u i : ℚ)) = (π : ℚ) ^ l • y ∧
      (0 < l → ¬ ∀ i, (π : ℤ) ∣ u i) := by
  classical
  set πv := placeOf π hπ with hπv
  have hvπ : Valued.v ((π : ℕ) : πv.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    have := valued_natGenerator πv; rw [natGenerator_placeOf] at this; exact_mod_cast this
  -- integrality at `π` after scaling
  let P : ℕ → Prop := fun l => locVec πv ((π : ℚ) ^ l • y) ∈ std πv
  have hex : ∃ l, P l := by
    have hk : ∀ i, ∃ k : ℕ, Valued.v (locVec πv y i) ≤ WithZero.exp (k : ℤ) := by
      intro i
      by_cases h0 : locVec πv y i = 0
      · exact ⟨0, by rw [h0, map_zero]; exact zero_le'⟩
      · obtain ⟨k, hk⟩ := exists_valued_eq_exp h0
        exact ⟨k.toNat, by rw [hk, WithZero.exp_le_exp]; omega⟩
    choose k hk using hk
    refine ⟨Finset.univ.sup k, fun i => ?_⟩
    simp only [locVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [hvπ, ← WithZero.exp_nsmul]
    have := hk i
    simp only [locVec_apply] at this
    calc WithZero.exp (Finset.univ.sup k • (-1 : ℤ)) * Valued.v (algebraMap ℚ (πv.adicCompletion ℚ) (y i))
        ≤ WithZero.exp (Finset.univ.sup k • (-1 : ℤ)) * WithZero.exp (k i : ℤ) := mul_le_mul' le_rfl this
      _ = WithZero.exp (Finset.univ.sup k • (-1 : ℤ) + k i) := by rw [WithZero.exp_add]
      _ ≤ WithZero.exp 0 := by
        rw [WithZero.exp_le_exp]
        have : k i ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ i)
        simp; omega
      _ = _ := by simp
  set l := Nat.find hex with hl
  have hPl : P l := Nat.find_spec hex
  have hint : ∀ (m : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)), v ≠ πv → locVec v ((π : ℚ) ^ m • y) ∈ std v := by
    intro m v hv i
    simp only [locVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    have h1 := hy v hv i
    simp only [locVec_apply] at h1
    have h2 : Valued.v ((π : ℕ) : v.adicCompletion ℚ) ≤ 1 := by simpa using valued_intCast_le_one' v (π : ℤ)
    calc Valued.v ((π : ℕ) : v.adicCompletion ℚ) ^ m * Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (y i))
        ≤ 1 * 1 := mul_le_mul' (pow_le_one' h2 m) (by simpa using h1)
      _ = _ := by simp
  have hmem : (π : ℚ) ^ l • y ∈ (intVec : Submodule (𝓞 ℚ) (Fin 4 → ℚ)) := by
    rw [mem_iff_forall_loc intVec_isLattice]
    intro v
    rw [loc_intVec]
    by_cases hv : v = πv
    · rw [hv]; exact hPl
    · exact hint l v hv
  obtain ⟨yz, hyz⟩ := mem_intVec_iff_exists.mp hmem
  refine ⟨l, fun i => Tamagawa.RatBridge.eZ (yz i), ?_, fun hl0 hall => ?_⟩
  · funext i; rw [eZ_cast_eq, ← hyz]
  · -- minimality of `l`
    have hlt : l - 1 < l := by omega
    apply Nat.find_min hex hlt
    intro i
    obtain ⟨w, hw⟩ := hall i
    have hyi : (π : ℚ) ^ l * y i = (π : ℚ) * w := by
      have := congrFun hyz i
      have e2 : intCoe yz i = ((Tamagawa.RatBridge.eZ (yz i) : ℤ) : ℚ) := (eZ_cast_eq (yz i)).symm
      rw [e2] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [← this]
      have hw' : (Tamagawa.RatBridge.eZ (yz i) : ℤ) = π * w := hw
      rw [hw']; push_cast; ring
    have hπ0 : (π : ℚ) ≠ 0 := by exact_mod_cast hπ.ne_zero
    have e : (π : ℚ) ^ (l - 1) * y i = w := by
      apply mul_left_cancel₀ hπ0
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega), hyi]
    simp only [locVec_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    simpa using valued_intCast_le_one' πv w

/-- **Closeness at $v$ as a congruence over $\mathbb Z_p$:** if $y \in \mathbb Q^4$ and $x \in \mathbb Z_p^4$ have
$y - \chi(x) \in p^K\mathfrak o_v^4$, then $y = x + p^K\delta$ in $\mathbb Q_p^4$ for some $\delta \in \mathbb Z_p^4$. -/
theorem padic_congr_of_ball (v : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 4 → ℚ} {x : Fin 4 → ℤ_[pOf v]} {K : ℕ}
    (h : locVec v y - (fun i => χ v (x i)) ∈ ball v K) :
    ∃ δ : Fin 4 → ℤ_[pOf v], ∀ i, ((y i : ℚ) : ℚ_[pOf v]) = (x i : ℚ_[pOf v]) + (pOf v : ℚ_[pOf v]) ^ K * (δ i : ℚ_[pOf v]) := by
  have hpv : Valued.v ((pOf v : ℕ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    have := valued_natGenerator v; rw [← pOf_eq] at this; exact_mod_cast this
  have hp0 : ((pOf v : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hpv; exact WithZero.zero_ne_coe hpv
  have hex : ∀ i, ∃ δ : ℤ_[pOf v], ψ v δ = (locVec v y i - χ v (x i)) / ((pOf v : ℕ) : v.adicCompletion ℚ) ^ K := by
    intro i
    apply exists_padicInt_of_valued_le_one
    rw [map_div₀, map_pow, hpv, ← WithZero.exp_nsmul]
    have := h i
    simp only [Pi.sub_apply] at this
    rw [div_le_iff₀ (zero_lt_iff.mpr (by simp))]
    simpa using this
  choose δ hδ using hex
  refine ⟨δ, fun i => ?_⟩
  have e1 : locVec v y i = χ v (x i) + ((pOf v : ℕ) : v.adicCompletion ℚ) ^ K * ψ v (δ i) := by
    rw [hδ]; field_simp; ring
  have e2 := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v) e1
  rw [map_add, map_mul, map_pow, χ_apply, padicEquiv_ψ, padicEquiv_ψ, map_natCast] at e2
  simp only [locVec_apply] at e2
  have hc : Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (algebraMap ℚ (v.adicCompletion ℚ) (y i)) =
      ((y i : ℚ) : ℚ_[pOf v]) := by
    simpa using (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).commutes (y i)
  rw [hc] at e2
  exact e2

end Approx

/-! ### Local targets and the datum of one type -/

/-- **A local target at the place `v`** (Cassels' choice of $k(p)$, p. 245): a vector $x \in \mathbb Z_p^4$ with $f(x) \ne 0$ which
is either Cassels' $\mathbf t$ of Lemma 9.3 with the shape data (`isA = true`, covering the $a$ with $p^{\mu+1} \mid a$) or a
primitive vector $\mathbf u_j(p)$ (`isA = false`, covering the $a \in f(x)U_p^2$). -/
structure LocTarget (f : QuadForm ℤ 4) (v : HeightOneSpectrum (𝓞 ℚ)) where
  /-- The vector. -/
  x : Fin 4 → ℤ_[pOf v]
  /-- Its value is nonzero. -/
  hne : (f.map (Int.castRingHom ℤ_[pOf v])).eval x ≠ 0
  /-- Case (a) or case (b). -/
  isA : Bool
  /-- The shape data of case (a). -/
  B : Matrix (Fin 4) (Fin 3) ℤ_[pOf v]
  /-- The exponent of case (a). -/
  μ : ℕ
  /-- The units of case (a). -/
  u1 : ℤ_[pOf v]
  /-- The units of case (a). -/
  u2 : ℤ_[pOf v]
  /-- Case (a): the shape of Lemma 9.3. -/
  hA : isA = true → Shape93 (f.map (Int.castRingHom ℤ_[pOf v])) x B μ u1 u2
  /-- Case (b): a primitive vector. -/
  hB : isA = false → ∃ i, IsUnit (x i)

/-- The integers covered by a local target. -/
def LocTarget.Cond {f : QuadForm ℤ 4} {v : HeightOneSpectrum (𝓞 ℚ)} (T : LocTarget f v) (a : ℤ) : Prop :=
  if T.isA then (pOf v : ℤ) ^ (T.μ + 1) ∣ a else
    ∃ β : ℤ_[pOf v], IsUnit β ∧ ((a : ℤ) : ℤ_[pOf v]) = (f.map (Int.castRingHom ℤ_[pOf v])).eval T.x * β ^ 2

/-- The finite set $T_0 = P \cup \{q\}$: the primes dividing $2\det H_f$ and $q$. -/
def T0set (f : QuadForm ℤ 4) (q : ℕ) : Finset ℕ := (2 * f.hessian.det).natAbs.primeFactors ∪ {q}

theorem prime_of_mem_T0set {f : QuadForm ℤ 4} {q : ℕ} (hq : q.Prime) {p : ℕ} (hp : p ∈ T0set f q) : p.Prime := by
  rcases Finset.mem_union.mp hp with h | h
  · exact Nat.prime_of_mem_primeFactors h
  · rw [Finset.mem_singleton.mp h]; exact hq

theorem not_dvd_of_not_mem_T0set {f : QuadForm ℤ 4} (hdet : f.hessian.det ≠ 0) {q p : ℕ} (hp : p.Prime)
    (hpT : p ∉ T0set f q) : ¬ (p : ℤ) ∣ 2 * f.hessian.det := by
  intro hd
  apply hpT
  refine Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp, ?_, ?_⟩)
  · exact Int.natCast_dvd.mp hd
  · simp [hdet]

/-! ### The number $g_1$ and the coordinates $W$ -/

/-- Helper: an integer congruent to a unit $w$ modulo $p^3$ is $w\varepsilon^2$ for a unit $\varepsilon$ of $\mathbb Z_p$. -/
theorem exists_unit_sq_of_cong {p : ℕ} [Fact p.Prime] {w : ℤ_[p]} (hw : IsUnit w) {c : ℤ_[p]}
    (hc : (p : ℤ_[p]) ^ 3 ∣ c - w) : ∃ ε : ℤ_[p], IsUnit ε ∧ c = w * ε ^ 2 := by
  obtain ⟨wi, hwi⟩ := hw.exists_right_inv
  obtain ⟨t, ht⟩ := hc
  obtain ⟨ε, hε⟩ := exists_sq_of_pow_three_dvd (p := p) (x := c * wi) ⟨t * wi, by linear_combination wi * ht + hwi⟩
  have hu : IsUnit (c * wi) := by
    have h1 : c * wi = 1 + (p : ℤ_[p]) * ((p : ℤ_[p]) ^ 2 * t * wi) := by linear_combination wi * ht + hwi
    rw [h1]; exact isUnit_add_p_mul isUnit_one _
  refine ⟨ε, (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp (by rw [hε]; exact hu), ?_⟩
  rw [hε]; linear_combination (-c) * hwi

/-- **The number $g_1$** (Cassels, (9.38)–(9.40)): given nonzero local values $a_v \in \mathbb Z_p$ at the places over a finite
set $T_0$ of primes, there are a prime $p_0 > B$ and a positive integer $c$ with all prime factors in $T_0$ such that
$g_1 = p_0c$ lies in the square class $a_vU_p^2$ at every place $v$ over $T_0$. -/
theorem exists_g1 (T0 : Finset ℕ) (hT0 : ∀ p ∈ T0, p.Prime)
    (val : ∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∈ T0 → ℤ_[pOf v])
    (hval : ∀ v hv, val v hv ≠ 0) (B : ℕ) :
    ∃ (p0 c : ℕ), p0.Prime ∧ B < p0 ∧ 0 < c ∧ (∀ p : ℕ, p.Prime → p ∣ c → p ∈ T0) ∧
      ∀ v hv, ∃ ε : ℤ_[pOf v], IsUnit ε ∧ (((p0 * c : ℕ) : ℤ) : ℤ_[pOf v]) = val v hv * ε ^ 2 := by
  classical
  have hdec : ∀ v hv, ∃ (k : ℕ) (w : ℤ_[pOf v]), IsUnit w ∧ val v hv = (pOf v : ℤ_[pOf v]) ^ k * w :=
    fun v hv => decomp (hval v hv)
  choose kk ww hww hkw using hdec
  have hpl : ∀ p (hp : p ∈ T0), Rat.HeightOneSpectrum.natGenerator (placeOf p (hT0 p hp)) ∈ T0 := by
    intro p hp; rw [natGenerator_placeOf]; exact hp
  let k : ℕ → ℕ := fun p => if hp : p ∈ T0 then kk _ (hpl p hp) else 0
  let R : ℕ → ℤ := fun p => if hp : p ∈ T0 then (PadicInt.appr (ww _ (hpl p hp)) 3 : ℤ) else 1
  have happr : ∀ v (hv : Rat.HeightOneSpectrum.natGenerator v ∈ T0),
      (pOf v : ℤ_[pOf v]) ^ 3 ∣ ww v hv - ((PadicInt.appr (ww v hv) 3 : ℕ) : ℤ_[pOf v]) :=
    fun v hv => Ideal.mem_span_singleton.mp (PadicInt.appr_spec 3 _)
  have hpv : ∀ p (hp : p ∈ T0), ((p : ℕ) : ℤ_[pOf (placeOf p (hT0 p hp))]) = (pOf (placeOf p (hT0 p hp)) : ℤ_[pOf (placeOf p (hT0 p hp))]) :=
    fun p hp => congrArg Nat.cast (by rw [pOf_eq, natGenerator_placeOf])
  have hR : ∀ p ∈ T0, ¬ (p : ℤ) ∣ R p := by
    intro p hp hd
    have hRp : R p = (PadicInt.appr (ww _ (hpl p hp)) 3 : ℤ) := dif_pos hp
    rw [hRp] at hd
    obtain ⟨m, hm⟩ := hd
    have hm' := congrArg (Int.cast : ℤ → ℤ_[pOf (placeOf p (hT0 p hp))]) hm
    push_cast at hm'
    rw [hpv p hp] at hm'
    have h2 : (pOf (placeOf p (hT0 p hp)) : ℤ_[pOf (placeOf p (hT0 p hp))]) ∣ ww _ (hpl p hp) := by
      have h3 := (dvd_pow_self (pOf (placeOf p (hT0 p hp)) : ℤ_[pOf (placeOf p (hT0 p hp))])
        (by norm_num : 3 ≠ 0)).trans (happr _ (hpl p hp))
      rw [hm'] at h3
      have := dvd_add h3 (dvd_mul_right _ (m : ℤ_[pOf (placeOf p (hT0 p hp))]))
      simpa using this
    exact PadicInt.p_nonunit (isUnit_of_dvd_unit h2 (hww _ _))
  obtain ⟨p0, hp0, hp0B, hp0c⟩ := exists_dirichlet_prime T0 hT0 k R hR B
  refine ⟨p0, ∏ p ∈ T0, p ^ k p, hp0, hp0B, Finset.prod_pos fun p hp => pow_pos (hT0 p hp).pos _,
    fun p hp hpd => ?_, fun v hv => ?_⟩
  · obtain ⟨a, ha, hpa⟩ := (Nat.Prime.prime hp).dvd_finset_prod_iff _ |>.mp hpd
    have := (Nat.prime_dvd_prime_iff_eq hp (hT0 a ha)).mp (hp.dvd_of_dvd_pow hpa)
    rw [this]; exact ha
  · obtain ⟨p, hp, rfl⟩ : ∃ p hp, v = placeOf p hp := ⟨_, _, (placeOf_natGenerator v).symm⟩
    have hpT : p ∈ T0 := by rw [natGenerator_placeOf] at hv; exact hv
    have hk : k p = kk _ hv := dif_pos hpT
    have hRp : R p = (PadicInt.appr (ww _ hv) 3 : ℤ) := dif_pos hpT
    have hc := (hp0c p hpT).symm.dvd
    rw [hRp] at hc
    obtain ⟨m, hm⟩ := hc
    have hm' := congrArg (Int.cast : ℤ → ℤ_[pOf (placeOf p hp)]) hm
    push_cast at hm'
    rw [hpv p hpT] at hm'
    have hcong : (pOf (placeOf p hp) : ℤ_[pOf (placeOf p hp)]) ^ 3 ∣
        ((∏ p' ∈ T0.erase p, (p' : ℤ) ^ k p') * p0 : ℤ) - ww _ hv := by
      obtain ⟨t, ht⟩ := happr _ hv
      refine ⟨m - t, ?_⟩
      push_cast
      linear_combination hm' - ht
    obtain ⟨ε, hε, hεe⟩ := exists_unit_sq_of_cong (hww _ hv) hcong
    refine ⟨ε, hε, ?_⟩
    rw [hkw _ hv, ← Finset.mul_prod_erase T0 (fun p => p ^ k p) hpT]
    have hpv' := hpv p hpT
    push_cast at hεe ⊢
    rw [hpv', hk] at *
    linear_combination ((pOf (placeOf p hp) : ℤ_[pOf (placeOf p hp)]) ^ kk _ hv) * hεe

/-- **Coordinates on $\mathbf u^\perp$** (Cassels, p. 246): for $\mathbf u \in \mathbb Z^4$ with $f(\mathbf u) \ne 0$ write
$H_f\mathbf u = e\,r$ with $r$ primitive; `exists_kernel_basis` gives $W$, $\tilde W$, $c_0$ with $\tilde WW = 1$,
$W\tilde W + c_0r^{\mathsf T} = 1$, and then $B(\mathbf u, Wz) = 0$ and $W\tilde Wx = x$ for $x \perp \mathbf u$. -/
theorem exists_uW (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (hu : f.eval u ≠ 0) :
    ∃ (W : Matrix (Fin 4) (Fin 3) ℤ) (Wt : Matrix (Fin 3) (Fin 4) ℤ) (c0 r : Fin 4 → ℤ) (e : ℤ),
      Wt * W = 1 ∧ W * Wt + Matrix.vecMulVec c0 r = 1 ∧ e ≠ 0 ∧ f.hessian *ᵥ u = e • r ∧
      (∀ z, bl f u (W *ᵥ z) = 0) ∧ (∀ x, bl f u x = 0 → W *ᵥ (Wt *ᵥ x) = x) ∧
      (∀ x, bl f u x = e * (r ⬝ᵥ x)) := by
  classical
  obtain ⟨r, hr, hr1⟩ := Finset.extract_gcd (f.hessian *ᵥ u) (Finset.univ_nonempty (α := Fin 4))
  set e := Finset.univ.gcd (f.hessian *ᵥ u) with he
  have hHu : f.hessian *ᵥ u = e • r := funext fun i => by rw [hr i (Finset.mem_univ i)]; rfl
  have hbl : ∀ x, bl f u x = e * (r ⬝ᵥ x) := by
    intro x
    rw [bl_comm, bl, hHu, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  have he0 : e ≠ 0 := by
    intro h0
    apply hu
    have := bl_self f u
    rw [hbl, h0, zero_mul] at this
    omega
  obtain ⟨W, Wt, hWt, horth, hrec, c0, hWW⟩ := exists_kernel_basis r hr1
  refine ⟨W, Wt, c0, r, e, hWt, hWW, he0, hHu, fun z => by rw [hbl, horth, mul_zero], fun x hx => ?_, hbl⟩
  rw [hbl] at hx
  exact hrec x ((mul_eq_zero.mp hx).resolve_left he0)

open QuadFormsKB.Lattices in
attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion in
/-- **Closeness at $v$ after scaling** ((9.41)): if $y - \chi(x) \in p^K\mathfrak o_v^4$ and $u = \pi^l y \in \mathbb Z^4$, then
$u \equiv \pi^l x \pmod{p^K}$ over $\mathbb Z_p$. -/
theorem int_congr_of_ball (v : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 4 → ℚ} {x : Fin 4 → ℤ_[pOf v]} {K : ℕ}
    (h : locVec v y - (fun i => χ v (x i)) ∈ ball v K) {π l : ℕ} {u : Fin 4 → ℤ}
    (hu : (fun i => (u i : ℚ)) = (π : ℚ) ^ l • y) (i : Fin 4) :
    (pOf v : ℤ_[pOf v]) ^ K ∣ ((u i : ℤ) : ℤ_[pOf v]) - (π : ℤ_[pOf v]) ^ l * x i := by
  obtain ⟨δ, hδ⟩ := padic_congr_of_ball v h
  refine ⟨(π : ℤ_[pOf v]) ^ l * δ i, ?_⟩
  apply Subtype.ext
  have hui := congrFun hu i
  simp only [Pi.smul_apply, smul_eq_mul] at hui
  have h1 : (((u i : ℤ) : ℚ) : ℚ_[pOf v]) = (((π : ℚ) ^ l * y i : ℚ) : ℚ_[pOf v]) := by rw [hui]
  push_cast at h1 ⊢
  rw [h1, hδ i]
  ring

/-! ### Local facts at the vector $\mathbf u$ -/

/-- Helper: an integer is a $p$-adic unit iff $p$ does not divide it. -/
theorem isUnit_intCast_iff {p : ℕ} [Fact p.Prime] (a : ℤ) : IsUnit ((a : ℤ) : ℤ_[p]) ↔ ¬ (p : ℤ) ∣ a := by
  rw [PadicInt.isUnit_iff, ← PadicInt.norm_int_lt_one_iff_dvd]
  constructor
  · intro h; rw [h]; exact lt_irrefl _
  · intro h; exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp h)

/-- Helper: $p \mid a$ in $\mathbb Z$ gives $p \mid a$ in $\mathbb Z_p$. -/
theorem dvd_intCast_of_dvd {p : ℕ} [Fact p.Prime] {a : ℤ} (h : (p : ℤ) ∣ a) : (p : ℤ_[p]) ∣ ((a : ℤ) : ℤ_[p]) := by
  obtain ⟨m, rfl⟩ := h; exact ⟨(m : ℤ_[p]), by push_cast; ring⟩

/-- **A vector $e$ with $p \nmid B(\mathbf u, e)$** when $p \nmid \det H_f$ and $\mathbf u$ is primitive at $p$
(Cassels, p. 247). *Proof:* $\det H_f\cdot\mathbf u = \operatorname{adj}(H_f)H_f\mathbf u$. -/
theorem exists_bl_not_dvd (f : QuadForm ℤ 4) {p : ℕ} (hp : p.Prime) (hdet : ¬ (p : ℤ) ∣ f.hessian.det)
    {u : Fin 4 → ℤ} (hu : PrimAt p u) : ∃ ee : Fin 4 → ℤ, ¬ (p : ℤ) ∣ bl f u ee := by
  classical
  by_contra hall
  push_neg at hall
  have hH : ∀ j, (p : ℤ) ∣ (f.hessian *ᵥ u) j := by
    intro j
    have := hall (Pi.single j 1)
    rw [bl_comm, bl, single_dotProduct, one_mul] at this
    exact this
  apply hu
  intro i
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h1 : (f.hessian.adjugate *ᵥ (f.hessian *ᵥ u)) i = f.hessian.det * u i := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul]
  have h2 : (p : ℤ) ∣ (f.hessian.adjugate *ᵥ (f.hessian *ᵥ u)) i := by
    simp only [mulVec, dotProduct]
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (hH j) _
  rw [h1] at h2
  exact (hpp.dvd_or_dvd h2).resolve_left hdet

/-- Helper: if $p^2 \nmid f(\mathbf u)$ then $\mathbf u$ is primitive at $p$. -/
theorem primAt_of_not_sq_dvd (f : QuadForm ℤ 4) {p : ℕ} {u : Fin 4 → ℤ} (h : ¬ (p : ℤ) ^ 2 ∣ f.eval u) :
    PrimAt p u := by
  intro hall
  apply h
  choose w hw using hall
  have : u = fun j => (p : ℤ) * w j := funext hw
  have e := LocalDensity.evalIn_const_mul f (p : ℤ) w
  rw [this]
  exact ⟨f.evalIn ℤ w, e⟩

/-- Helper: changing the square class representative ($a = f(x)\beta^2$, $f(\mathbf u) = \eta^2f(x)$). -/
theorem sq_class_trans {p : ℕ} [Fact p.Prime] {fu fx a η β : ℤ_[p]} (hη : IsUnit η) (hβ : IsUnit β)
    (hfu : fu = η ^ 2 * fx) (ha : a = fx * β ^ 2) : ∃ β' : ℤ_[p], IsUnit β' ∧ a = fu * β' ^ 2 := by
  obtain ⟨ηi, hηi⟩ := hη.exists_right_inv
  refine ⟨β * ηi, hβ.mul (isUnit_of_mul_eq_one_right' hηi), ?_⟩
  rw [ha, hfu]
  linear_combination (-(fx * β ^ 2 * (1 + η * ηi))) * hηi

/-- **The shape of Lemma 9.3 at $\mathbf u$** (Cassels, p. 246): if $\mathbf t$ has the shape (`Shape93`) and $\mathbf u \equiv \eta\mathbf t
\pmod{p^{\mu+2}}$ with $f(\mathbf u) = \eta^2 f(\mathbf t)$, $\eta$ a unit, then $\mathbf u$ has the shape with the same $\mu$. -/
theorem exists_shape_at_u {v : HeightOneSpectrum (𝓞 ℚ)} (f : QuadForm ℤ 4) {x : Fin 4 → ℤ_[pOf v]}
    {B : Matrix (Fin 4) (Fin 3) ℤ_[pOf v]} {μ : ℕ} {u1 u2 : ℤ_[pOf v]}
    (S : Shape93 (f.map (Int.castRingHom ℤ_[pOf v])) x B μ u1 u2) (u : Fin 4 → ℤ) {η : ℤ_[pOf v]} (hη : IsUnit η)
    (hfu : ((f.eval u : ℤ) : ℤ_[pOf v]) = η ^ 2 * (f.map (Int.castRingHom ℤ_[pOf v])).eval x)
    (hcong : ∀ i, (pOf v : ℤ_[pOf v]) ^ (μ + 2) ∣ ((u i : ℤ) : ℤ_[pOf v]) - η * x i) :
    ∃ (B' : Matrix (Fin 4) (Fin 3) ℤ_[pOf v]) (u1' u2' : ℤ_[pOf v]),
      Shape93 (f.map (Int.castRingHom ℤ_[pOf v])) (fun i => ((u i : ℤ) : ℤ_[pOf v])) B' μ u1' u2' := by
  have S' := S.smul_unit hη
  have hev : (f.map (Int.castRingHom ℤ_[pOf v])).eval (fun i => ((u i : ℤ) : ℤ_[pOf v])) =
      (f.map (Int.castRingHom ℤ_[pOf v])).eval (η • x) := by
    rw [show (fun i => ((u i : ℤ) : ℤ_[pOf v])) = fun i => Int.castRingHom ℤ_[pOf v] (u i) from rfl,
      eval_map_hom, show η • x = fun j => η * x j from rfl]
    change _ = (f.map (Int.castRingHom ℤ_[pOf v])).evalIn ℤ_[pOf v] _
    rw [LocalDensity.DVR.evalIn_const_mul]
    exact hfu
  obtain ⟨B', hB'⟩ := S'.perturb hev (fun i => hcong i)
  exact ⟨B', _, _, hB'⟩

/-- Helper: the Hessian determinant commutes with base change. -/
theorem hessian_det_map {S : Type*} [CommRing S] (φ : ℤ →+* S) (f : QuadForm ℤ 4) :
    (f.map φ).hessian.det = φ f.hessian.det := by
  rw [hessian_map, RingHom.map_det]; rfl

/-- Helper: an odd prime $\pi$ with $d \in U_\pi^2$ gives $\det H_f = 16\delta^2$ over $\mathbb Z_\pi$, uniformly in the prime. -/
theorem det_eq_sixteen_sq_of_isUnitSquareAt (f : QuadForm ℤ 4) {d : ℤ} (hdH : f.hessian.det = 2 ^ 4 * d)
    {π : ℕ} (hπ : π.Prime) (hsq : @IsUnitSquareAt π ⟨hπ⟩ (d : ℚ)) (p : ℕ) [Fact p.Prime] (hp : p = π) :
    ∃ δ : ℤ_[p], IsUnit δ ∧ (f.map (Int.castRingHom ℤ_[p])).hessian.det = 16 * δ ^ 2 := by
  subst hp
  obtain ⟨δ, hδ, hδ2⟩ := hsq
  refine ⟨δ, hδ, ?_⟩
  rw [hessian_det_map, hdH]
  have : δ ^ 2 = (d : ℤ_[p]) := Subtype.ext (by push_cast; exact hδ2)
  rw [this, eq_intCast]; push_cast; ring

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion in
open QuadFormsKB.Lattices in
/-- **The vector $\mathbf u$** (Cassels, (9.38)–(9.41)): from local targets $x_v$ at the places over $T_0 = P \cup \{q\}$, there are
primes $\pi$ ($d \in U_\pi^2$) and $p_0 \ge 7$ outside $T_0$, $l \ge 0$, $c > 0$ with prime factors in $T_0$, and $\mathbf u \in \mathbb Z^4$
with $f(\mathbf u) = \pi^{2l}p_0c$, $\mathbf u$ primitive at $\pi$ if $l > 0$, and at every place $v$ over $T_0$ a unit $\eta$ with
$f(\mathbf u) = \eta^2 f(x_v)$ and $\mathbf u \equiv \eta x_v \pmod{p^{\mu_v + 2}}$. -/
theorem exists_u_of_targets (f : QuadForm ℤ 4) (hf : IntQF.PosDef f) (hci : IsClassicallyIntegral f)
    {q : ℕ} (hq : q.Prime)
    (tgt : ∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∈ T0set f q → LocTarget f v) :
    ∃ (u : Fin 4 → ℤ) (p0 π l c : ℕ) (hπ : π.Prime), p0.Prime ∧ 7 ≤ p0 ∧ p0 ∉ T0set f q ∧ π ∉ T0set f q ∧
      p0 ≠ π ∧ 0 < c ∧ (∀ p : ℕ, p.Prime → p ∣ c → p ∈ T0set f q) ∧
      f.eval u = (π : ℤ) ^ (2 * l) * ((p0 : ℤ) * c) ∧ (0 < l → PrimAt π u) ∧
      (∀ (p : ℕ) [Fact p.Prime], p = π →
        ∃ δ : ℤ_[p], IsUnit δ ∧ (f.map (Int.castRingHom ℤ_[p])).hessian.det = 16 * δ ^ 2) ∧
      ∀ v hv, ∃ η : ℤ_[pOf v], IsUnit η ∧
        ((f.eval u : ℤ) : ℤ_[pOf v]) = η ^ 2 * (f.map (Int.castRingHom ℤ_[pOf v])).eval (tgt v hv).x ∧
        ∀ i, (pOf v : ℤ_[pOf v]) ^ ((tgt v hv).μ + 2) ∣ ((u i : ℤ) : ℤ_[pOf v]) - η * (tgt v hv).x i := by
  classical
  obtain ⟨d, -, hdH⟩ := exists_cassDet_eq hci
  have hdet0 : f.hessian.det ≠ 0 := IntQF.PosDef.nondegenerate hf
  have hd0 : d ≠ 0 := by intro h0; apply hdet0; rw [hdH, h0, mul_zero]
  let T0 := T0set f q
  have hT0 : ∀ p ∈ T0, p.Prime := fun p hp => prime_of_mem_T0set hq hp
  have hbad : ∀ p : ℕ, p.Prime → p ∉ T0 → ¬ (p : ℤ) ∣ 2 * f.hessian.det :=
    fun p hp hpT => not_dvd_of_not_mem_T0set hdet0 hp hpT
  have hsupT : ∀ p ∈ T0, p ≤ T0.sup id := fun p hp => Finset.le_sup (f := id) hp
  -- the prime `π`
  obtain ⟨π, hπ, hπB, hsqπ⟩ := exists_prime_isUnitSquareAt d hd0 (T0.sup id + 7)
  have hπT : π ∉ T0 := fun h => by have := hsupT π h; omega
  -- `g₁ = p₀ c`
  obtain ⟨p0, c, hp0, hp0B, hc0, hcT, hloc⟩ := exists_g1 T0 hT0
    (fun v hv => (f.map (Int.castRingHom ℤ_[pOf v])).eval (tgt v hv).x) (fun v hv => (tgt v hv).hne) (T0.sup id + π + 7)
  have hp0T : p0 ∉ T0 := fun h => by have := hsupT p0 h; omega
  choose ε hε hεe using hloc
  set g1 : ℤ := ((p0 * c : ℕ) : ℤ) with hg1
  have hg1pos : 0 < g1 := by rw [hg1]; exact_mod_cast Nat.mul_pos hp0.pos hc0
  -- targets for Theorem 8.1
  let z : ∀ v : HeightOneSpectrum (𝓞 ℚ), Fin 4 → v.adicCompletion ℚ := fun v =>
    if hv : Rat.HeightOneSpectrum.natGenerator v ∈ T0 then fun i => χ v (ε v hv * (tgt v hv).x i) else 0
  have hz : ∀ v (hv : Rat.HeightOneSpectrum.natGenerator v ∈ T0), z v = fun i => χ v (ε v hv * (tgt v hv).x i) :=
    fun v hv => dif_pos hv
  have hzval : ∀ v, Rat.HeightOneSpectrum.natGenerator v ∈ T0 →
      (f.map (Int.castRingHom ℚ)).evalIn _ (z v) = algebraMap ℚ _ (g1 : ℚ) := by
    intro v hv
    rw [hz v hv, evalIn_χ]
    have e1 : (f.map (Int.castRingHom ℤ_[pOf v])).eval (fun i => ε v hv * (tgt v hv).x i) =
        ε v hv ^ 2 * (f.map (Int.castRingHom ℤ_[pOf v])).eval (tgt v hv).x :=
      LocalDensity.DVR.evalIn_const_mul _ _ _
    rw [e1, ← χ_intCast, hg1, hεe v hv]; ring_nf
  set Tv := (finite_places T0).toFinset with hTv
  set K : ℕ := Tv.sup fun v => if hv : Rat.HeightOneSpectrum.natGenerator v ∈ T0 then (tgt v hv).μ + 2 else 0 with hK
  have hKle : ∀ v (hv : Rat.HeightOneSpectrum.natGenerator v ∈ T0), (tgt v hv).μ + 2 ≤ K := by
    intro v hv
    have hmem : v ∈ Tv := by rw [hTv, Set.Finite.mem_toFinset]; exact hv
    have := Finset.le_sup (f := fun v => if hv : Rat.HeightOneSpectrum.natGenerator v ∈ T0 then (tgt v hv).μ + 2 else 0)
      hmem
    simp only [dif_pos hv] at this
    exact this
  obtain ⟨y, hy, hyz, hyout⟩ := exists_approx_vector f hf T0 hT0 hbad hπ hπT hg1pos z hzval (K : ℤ)
  have hyint : ∀ v, v ≠ placeOf π hπ → locVec v y ∈ std v := by
    intro v hvπ
    by_cases hv : Rat.HeightOneSpectrum.natGenerator v ∈ T0
    · have h1 : locVec v y = (locVec v y - z v) + z v := by abel
      rw [h1]
      refine (std v).add_mem (ball_anti v (by omega) (hyz v hv)) ?_
      rw [hz v hv]
      exact fun i => valued_ψ_le_one v _
    · exact hyout v hv hvπ
  obtain ⟨l, u, hu, hprim⟩ := exists_pow_mul_int y hπ hyint
  -- `f(u) = π^{2l} g₁`
  have hfu : f.eval u = (π : ℤ) ^ (2 * l) * g1 := by
    have e1 : (f.map (Int.castRingHom ℚ)).eval (fun i => (u i : ℚ)) = ((f.eval u : ℤ) : ℚ) :=
      eval_map_hom (Int.castRingHom ℚ) f u
    rw [hu, show (π : ℚ) ^ l • y = fun j => (π : ℚ) ^ l * y j from rfl] at e1
    have e2 : (f.map (Int.castRingHom ℚ)).eval (fun j => (π : ℚ) ^ l * y j) =
        ((π : ℚ) ^ l) ^ 2 * (f.map (Int.castRingHom ℚ)).eval y := LocalDensity.DVR.evalIn_const_mul _ _ _
    rw [e2, hy] at e1
    have : ((f.eval u : ℤ) : ℚ) = (((π : ℤ) ^ (2 * l) * g1 : ℤ) : ℚ) := by rw [← e1]; push_cast; ring
    exact_mod_cast this
  refine ⟨u, p0, π, l, c, hπ, hp0, by omega, hp0T, hπT, by omega, hc0, hcT, ?_, hprim,
    det_eq_sixteen_sq_of_isUnitSquareAt f hdH hπ hsqπ, fun v hv => ?_⟩
  · rw [hfu, hg1]; push_cast; ring
  · have hpπ : ¬ ((pOf v : ℕ) : ℤ) ∣ (π : ℤ) := by
      intro hd
      have h1 : pOf v ∣ π := Int.natCast_dvd_natCast.mp hd
      have h2 := (Nat.prime_dvd_prime_iff_eq (Fact.out) hπ).mp h1
      apply hπT; rw [← h2, pOf_eq]; exact hv
    have hπu : IsUnit ((π : ℤ) : ℤ_[pOf v]) := (isUnit_intCast_iff _).mpr hpπ
    push_cast at hπu
    refine ⟨(π : ℤ_[pOf v]) ^ l * ε v hv, (hπu.pow l).mul (hε v hv), ?_, fun i => ?_⟩
    · rw [hfu]; push_cast; rw [hεe v hv]; ring
    · have hball : locVec v y - (fun i => χ v (ε v hv * (tgt v hv).x i)) ∈ ball v (((tgt v hv).μ + 2 : ℕ) : ℤ) := by
        rw [← hz v hv]; exact ball_anti v (by exact_mod_cast hKle v hv) (hyz v hv)
      have := int_congr_of_ball v hball hu i
      rw [show (π : ℤ_[pOf v]) ^ l * (ε v hv * (tgt v hv).x i) = (π : ℤ_[pOf v]) ^ l * ε v hv * (tgt v hv).x i by ring]
        at this
      exact this

section Datum

open QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **The datum of one type** (Cassels, pp. 245–248): given local targets at the places over $T_0 = P \cup \{q\}$ (case (b)
with a unit value at $q$), there is a datum of the final stage serving every $a$ prime to $q$ covered by all the targets. -/
theorem exists_datum_of_targets (f : QuadForm ℤ 4) (hf : IntQF.PosDef f) (hci : IsClassicallyIntegral f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hsq : @IsUnitSquareAt q ⟨hq⟩ (cassDet f))
    (tgt : ∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∈ T0set f q → LocTarget f v)
    (htq : ∀ hv, (tgt (placeOf q hq) hv).isA = false ∧
      IsUnit ((f.map (Int.castRingHom ℤ_[pOf (placeOf q hq)])).eval (tgt (placeOf q hq) hv).x)) :
    ∃ D : L92Datum f q hq, ∀ k : ℕ, ∃ B : Finset ℤ, ∀ a : ℤ, ¬ (q : ℤ) ∣ a →
      (∀ v hv, (tgt v hv).Cond a) → ∃ b ∈ B, LocalOK D k a b := by
  classical
  obtain ⟨u, p0, π, l, c, hπ, hp0, h7, hp0T, hπT, hp0π, hc0, hcT, hfu, hπprim, hδ, hloc⟩ :=
    exists_u_of_targets f hf hci hq tgt
  obtain ⟨d, hdq, hdH⟩ := exists_cassDet_eq hci
  have hdet0 : f.hessian.det ≠ 0 := IntQF.PosDef.nondegenerate hf
  let T0 := T0set f q
  have hT0 : ∀ p ∈ T0, p.Prime := fun p hp => prime_of_mem_T0set hq hp
  have hqT : q ∈ T0 := Finset.mem_union_right _ (Finset.mem_singleton_self q)
  have hbad : ∀ p : ℕ, p.Prime → p ∉ T0 → ¬ (p : ℤ) ∣ 2 * f.hessian.det :=
    fun p hp hpT => not_dvd_of_not_mem_T0set hdet0 hp hpT
  have hg0 : f.eval u ≠ 0 := by
    rw [hfu]
    have : (0 : ℤ) < (π : ℤ) ^ (2 * l) * ((p0 : ℤ) * c) := by
      have := hπ.pos; have := hp0.pos; positivity
    exact this.ne'
  obtain ⟨W, Wt, c0, r, e, hWt, hWW, he0, he, horth, hrec, hbl⟩ := exists_uW f u hg0
  have hQ : ((gramOf f W).map (Int.castRingHom ℚ)).Nondegenerate :=
    nondegenerate_map_of_det_ne_zero _ (IntQF.PosDef.nondegenerate (posDef_gramOf hf hWt))
  -- local facts at the targets
  have hprimB : ∀ v hv, (tgt v hv).isA = false → ∃ i, ¬ (pOf v : ℤ) ∣ u i := by
    intro v hv hB
    obtain ⟨η, hη, -, hcong⟩ := hloc v hv
    obtain ⟨i, hi⟩ := (tgt v hv).hB hB
    refine ⟨i, fun hd => ?_⟩
    have h1 : (pOf v : ℤ_[pOf v]) ∣ ((u i : ℤ) : ℤ_[pOf v]) := by
      have := dvd_intCast_of_dvd (p := pOf v) hd; exact_mod_cast this
    have h2 : (pOf v : ℤ_[pOf v]) ∣ ((u i : ℤ) : ℤ_[pOf v]) - η * (tgt v hv).x i :=
      (dvd_pow_self _ (by omega)).trans (hcong i)
    have h3 : (pOf v : ℤ_[pOf v]) ∣ η * (tgt v hv).x i := by
      have := dvd_sub h1 h2; simpa using this
    exact PadicInt.p_nonunit (isUnit_of_dvd_unit h3 (hη.mul hi))
  have hsqB : ∀ v hv, (tgt v hv).isA = false → ∀ a, (tgt v hv).Cond a →
      ∃ β : ℤ_[pOf v], IsUnit β ∧ ((a : ℤ) : ℤ_[pOf v]) = ((f.eval u : ℤ) : ℤ_[pOf v]) * β ^ 2 := by
    intro v hv hB a ha
    simp only [LocTarget.Cond, hB, Bool.false_eq_true, if_false] at ha
    obtain ⟨β, hβ, hab⟩ := ha
    obtain ⟨η, hη, hfη, -⟩ := hloc v hv
    exact sq_class_trans hη hβ hfη hab
  have hshape : ∀ v hv, (tgt v hv).isA = true → ∃ (B' : Matrix (Fin 4) (Fin 3) ℤ_[pOf v]) (u1 u2 : ℤ_[pOf v]),
      Shape93 (f.map (Int.castRingHom ℤ_[pOf v])) (fun i => ((u i : ℤ) : ℤ_[pOf v])) B' (tgt v hv).μ u1 u2 := by
    intro v hv hA
    obtain ⟨η, hη, hfη, hcong⟩ := hloc v hv
    exact exists_shape_at_u f ((tgt v hv).hA hA) u hη hfη hcong
  have hAdvd : ∀ v hv, (tgt v hv).isA = true → ∀ a, (tgt v hv).Cond a → (pOf v : ℤ) ^ ((tgt v hv).μ + 1) ∣ a := by
    intro v hv hA a ha
    simpa only [LocTarget.Cond, hA, if_true] using ha
  -- facts at `p₀`
  have hp0c : ¬ (p0 : ℤ) ∣ c := fun h => hp0T (hcT p0 hp0 (Int.natCast_dvd_natCast.mp h))
  have hp0πd : ¬ (p0 : ℤ) ∣ π := fun h =>
    hp0π ((Nat.prime_dvd_prime_iff_eq hp0 hπ).mp (Int.natCast_dvd_natCast.mp h))
  have hp0pr : Prime (p0 : ℤ) := Nat.prime_iff_prime_int.mp hp0
  have hdetp0 : ¬ (p0 : ℤ) ∣ f.hessian.det := fun h => hbad p0 hp0 hp0T (dvd_mul_of_dvd_right h _)
  have hgp0 : (p0 : ℤ) ∣ f.eval u := by rw [hfu]; exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  have hg2p0 : ¬ (p0 : ℤ) ^ 2 ∣ f.eval u := by
    rw [hfu]
    intro h
    obtain ⟨m, hm⟩ := h
    have h1 : (π : ℤ) ^ (2 * l) * c = p0 * m := by
      apply mul_left_cancel₀ (show (p0 : ℤ) ≠ 0 by exact_mod_cast hp0.ne_zero)
      linear_combination hm
    have h2 : (p0 : ℤ) ∣ (π : ℤ) ^ (2 * l) * c := ⟨m, h1⟩
    rcases hp0pr.dvd_or_dvd h2 with h3 | h3
    · exact hp0πd (hp0pr.dvd_of_dvd_pow h3)
    · exact hp0c h3
  have hup0 : PrimAt p0 u := primAt_of_not_sq_dvd f hg2p0
  have hee0 : ∃ ee : Fin 4 → ℤ, ¬ (p0 : ℤ) ∣ bl f u ee := exists_bl_not_dvd f hp0 hdetp0 hup0
  -- facts at `π`
  have hπ2 : π ≠ 2 := by
    rintro rfl; exact hbad 2 hπ hπT (dvd_mul_right _ _)
  have hdetπ : ¬ (π : ℤ) ∣ f.hessian.det := fun h => hbad π hπ hπT (dvd_mul_of_dvd_right h _)
  have hgπ : 0 < l → (π : ℤ) ∣ f.eval u := fun hl => by
    rw [hfu]; exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
  have heeπ : 0 < l → ∃ ee : Fin 4 → ℤ, ¬ (π : ℤ) ∣ bl f u ee := fun hl =>
    exists_bl_not_dvd f hπ hdetπ (hπprim hl)
  -- facts at `q`
  set vq := placeOf q hq with hvqdef
  have hvqT : Rat.HeightOneSpectrum.natGenerator vq ∈ T0 := by rw [natGenerator_placeOf]; exact hqT
  have hpq : pOf vq = q := by rw [pOf_eq, natGenerator_placeOf]
  have hqfu : ¬ (q : ℤ) ∣ f.eval u := by
    obtain ⟨η, hη, hfη, -⟩ := hloc vq hvqT
    have hu' : IsUnit ((f.eval u : ℤ) : ℤ_[pOf vq]) := by rw [hfη]; exact (hη.pow 2).mul (htq hvqT).2
    have := (isUnit_intCast_iff _).mp hu'
    rwa [hpq] at this
  have hqdet : ¬ (q : ℤ) ∣ f.hessian.det := by
    rw [hdq] at hsq
    obtain ⟨δq, hδq, hdq'⟩ := det_eq_sixteen_sq_of_isUnitSquareAt f hdH hq hsq (pOf vq) hpq
    have h16 : IsUnit ((16 : ℤ) : ℤ_[pOf vq]) := by
      rw [isUnit_intCast_iff, hpq]
      intro h
      have h2 : (q : ℤ) ∣ 2 := (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow (n := 4) (by norm_num; exact h)
      have := Int.le_of_dvd (by norm_num) h2
      have := hq.two_le
      omega
    have hu' : IsUnit ((f.hessian.det : ℤ) : ℤ_[pOf vq]) := by
      rw [← eq_intCast (Int.castRingHom ℤ_[pOf vq]), ← hessian_det_map, hdq']
      push_cast at h16
      exact h16.mul (hδq.pow 2)
    have := (isUnit_intCast_iff _).mp hu'
    rwa [hpq] at this
  have hqg : ¬ (q : ℤ) ∣ 2 * f.eval u * f.hessian.det := by
    have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    intro h
    rcases hqp.dvd_or_dvd h with h1 | h1
    · rcases hqp.dvd_or_dvd h1 with h2 | h2
      · have := Int.le_of_dvd (by norm_num) h2
        have h22 : (q : ℤ) ≠ 2 := by exact_mod_cast hq2
        have := hq.two_le
        omega
      · exact hqfu h2
    · exact hqdet h1
  -- the set `S`
  let S : Finset ℕ := T0 ∪ {p0} ∪ (if 0 < l then {π} else ∅)
  have hSp : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact hT0 p h'
      · rw [Finset.mem_singleton.mp h']; exact hp0
    · split_ifs at h with hl
      · rw [Finset.mem_singleton.mp h]; exact hπ
      · simp at h
  have hqS : q ∈ S := Finset.mem_union_left _ (Finset.mem_union_left _ hqT)
  have hp0S : p0 ∈ S := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hπS : 0 < l → π ∈ S := fun hl => Finset.mem_union_right _ (by simp [hl])
  have hScases : ∀ p ∈ S, p ∉ T0 → p ≠ p0 → p = π ∧ 0 < l := by
    intro p hp hT h0
    rcases Finset.mem_union.mp hp with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact absurd h' hT
      · exact absurd (Finset.mem_singleton.mp h') h0
    · split_ifs at h with hl
      · exact ⟨Finset.mem_singleton.mp h, hl⟩
      · simp at h
  have hout : ∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ 2 * f.eval u * f.hessian.det := by
    intro p hp hpS
    have hpT : p ∉ T0 := fun h => hpS (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hb := hbad p hp hpT
    intro h
    rcases hpp.dvd_or_dvd h with h1 | h1
    · rcases hpp.dvd_or_dvd h1 with h2 | h2
      · exact hb (dvd_mul_of_dvd_left h2 _)
      · rw [hfu] at h2
        rcases hpp.dvd_or_dvd h2 with h3 | h3
        · have h4 := hpp.dvd_of_dvd_pow h3
          have h5 : p = π := (Nat.prime_dvd_prime_iff_eq hp hπ).mp (Int.natCast_dvd_natCast.mp h4)
          rcases Nat.eq_zero_or_pos l with hl | hl
          · rw [hl] at h3; simp at h3; exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h3)
          · exact hpS (h5 ▸ hπS hl)
        · rcases hpp.dvd_or_dvd h3 with h4 | h4
          · have h5 : p = p0 := (Nat.prime_dvd_prime_iff_eq hp hp0).mp (Int.natCast_dvd_natCast.mp h4)
            exact hpS (h5 ▸ hp0S)
          · exact hpT (hcT p hp (Int.natCast_dvd_natCast.mp h4))
    · exact hb (dvd_mul_of_dvd_right h1 _)
  -- the type `A` and the condition at `q`
  let A : ℤ → Prop := fun a => ¬ (q : ℤ) ∣ a ∧ ∀ v hv, (tgt v hv).Cond a
  have hqb : ∀ a, A a → ∀ k : ℕ, ∃ b0 : ℤ, ∀ b : ℤ, b ≡ b0 [ZMOD ((q ^ (2 * k) : ℕ) : ℤ)] →
      (q : ℤ) ^ (2 * k) ∣ a - b ^ 2 * f.eval u := by
    intro a ha k
    obtain ⟨β, -, hβ⟩ := hsqB vq hvqT (htq hvqT).1 a (ha.2 vq hvqT)
    obtain ⟨b0, hb0⟩ := exists_residue_of_sq (pOf vq) a (f.eval u) β hβ (2 * k)
    rw [hpq] at hb0
    exact ⟨b0, hb0⟩
  -- the local packages
  have hπv : ∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∈ S →
      Rat.HeightOneSpectrum.natGenerator v ∉ T0 → Rat.HeightOneSpectrum.natGenerator v ≠ p0 → pOf v = π ∧ 0 < l :=
    fun v hvS hT h0 => hScases _ hvS hT h0
  let pkg : ∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∈ S →
      Rat.HeightOneSpectrum.natGenerator v ≠ q → LocalPkg f u W A p0 v := fun v hvS _ =>
    if hT : Rat.HeightOneSpectrum.natGenerator v ∈ T0 then
      if hA : (tgt v hT).isA = true then
        pkgCaseA v f u W Wt c0 r hWW e he0 he horth _ (tgt v hT).μ _ _
          (hshape v hT hA).choose_spec.choose_spec.choose_spec A (fun a ha => hAdvd v hT hA a (ha.2 v hT)) p0
      else
        pkgCaseB v f u W hQ (hprimB v hT (by simpa using hA)) hg0 A
          (fun a ha => hsqB v hT (by simpa using hA) a (ha.2 v hT)) p0
    else if h0 : Rat.HeightOneSpectrum.natGenerator v = p0 then
      (by
        have hv0 : pOf v = p0 := h0
        have hu0 : ∃ i, ¬ (pOf v : ℤ) ∣ u i := by
          rw [hv0]; by_contra hn; push_neg at hn; exact hup0 hn
        exact hv0 ▸ pkgP0 v f u W Wt hWt horth hrec hQ (by rw [hv0]; exact h7) (by rw [hv0]; exact hdetp0)
          (by rw [hv0]; exact hgp0) (by rw [hv0]; exact hg2p0) hu0 hee0.choose (by rw [hv0]; exact hee0.choose_spec) A)
    else
      (by
        obtain ⟨hvπ, hl⟩ := hπv v hvS hT h0
        exact pkgPi v f u W Wt c0 r hWW e he0 he horth (by rw [hvπ]; exact hπ2) (heeπ hl).choose
          (by rw [hvπ]; exact (heeπ hl).choose_spec) (by rw [hvπ]; exact hgπ hl) (hδ (pOf v) hvπ).choose
          (hδ (pOf v) hvπ).choose_spec.1 (hδ (pOf v) hvπ).choose_spec.2 A p0)
  obtain ⟨D, hD⟩ := exists_family_of_pkgs f hf hq u W Wt hWt horth S hSp hqS hout hqg A (fun a ha => ha.1) p0 pkg hqb
  refine ⟨D, fun k => ?_⟩
  obtain ⟨B, hB⟩ := hD k
  exact ⟨B, fun a hqa hcond => hB a ⟨hqa, hcond⟩⟩

end Datum

/-! ### Local options and the covering by types -/

/-- A local target of case (b): a primitive vector with nonzero value. -/
def LocTarget.ofPrim {f : QuadForm ℤ 4} {v : HeightOneSpectrum (𝓞 ℚ)} (x : Fin 4 → ℤ_[pOf v])
    (hx : ∃ i, IsUnit (x i)) (hne : (f.map (Int.castRingHom ℤ_[pOf v])).eval x ≠ 0) : LocTarget f v where
  x := x
  hne := hne
  isA := false
  B := 0
  μ := 0
  u1 := 0
  u2 := 0
  hA := fun h => absurd h (by simp)
  hB := fun _ => hx

/-- A local target of case (a): Cassels' $\mathbf t$ with the shape of Lemma 9.3. -/
def LocTarget.ofShape {f : QuadForm ℤ 4} {v : HeightOneSpectrum (𝓞 ℚ)} {t : Fin 4 → ℤ_[pOf v]}
    {B : Matrix (Fin 4) (Fin 3) ℤ_[pOf v]} {μ : ℕ} {u1 u2 : ℤ_[pOf v]}
    (S : Shape93 (f.map (Int.castRingHom ℤ_[pOf v])) t B μ u1 u2) : LocTarget f v where
  x := t
  hne := by rw [S.ht]; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : (pOf v).Prime).ne_zero)) S.hu2.ne_zero
  isA := true
  B := B
  μ := μ
  u1 := u1
  u2 := u2
  hA := fun _ => S
  hB := fun h => absurd h (by simp)

theorem LocTarget.cond_ofPrim {f : QuadForm ℤ 4} {v : HeightOneSpectrum (𝓞 ℚ)} (x : Fin 4 → ℤ_[pOf v])
    (hx : ∃ i, IsUnit (x i)) (hne : (f.map (Int.castRingHom ℤ_[pOf v])).eval x ≠ 0) (a : ℤ) :
    (LocTarget.ofPrim x hx hne).Cond a ↔
      ∃ β : ℤ_[pOf v], IsUnit β ∧ ((a : ℤ) : ℤ_[pOf v]) = (f.map (Int.castRingHom ℤ_[pOf v])).eval x * β ^ 2 := by
  simp [LocTarget.Cond, LocTarget.ofPrim]

theorem LocTarget.cond_ofShape {f : QuadForm ℤ 4} {v : HeightOneSpectrum (𝓞 ℚ)} {t : Fin 4 → ℤ_[pOf v]}
    {B : Matrix (Fin 4) (Fin 3) ℤ_[pOf v]} {μ : ℕ} {u1 u2 : ℤ_[pOf v]}
    (S : Shape93 (f.map (Int.castRingHom ℤ_[pOf v])) t B μ u1 u2) (a : ℤ) :
    (LocTarget.ofShape S).Cond a ↔ (pOf v : ℤ) ^ (μ + 1) ∣ a := by
  simp [LocTarget.Cond, LocTarget.ofShape]

/-- Helper: `PrimRepZp` in terms of the base change of `f`. -/
theorem primRepZp_iff_map {p : ℕ} [Fact p.Prime] (f : QuadForm ℤ 4) (a : ℤ) :
    PrimRepZp p f a ↔ ∃ y : Fin 4 → ℤ_[p], (∃ i, IsUnit (y i)) ∧
      (f.map (Int.castRingHom ℤ_[p])).eval y = ((a : ℤ) : ℤ_[p]) := by
  have e : ∀ y : Fin 4 → ℤ_[p], (f.map (Int.castRingHom ℤ_[p])).eval y = f.evalIn ℤ_[p] y := by
    intro y; simp [QuadForm.evalIn, QuadForm.map, Algebra.smul_def]
  simp only [PrimRepZp, e]

/-- **Class representatives cover the values of bounded valuation**, as local targets of case (b). -/
theorem exists_prim_targets (f : QuadForm ℤ 4) (v : HeightOneSpectrum (𝓞 ℚ)) (K : ℕ) :
    ∃ (N : ℕ) (T : Fin N → LocTarget f v), (∀ j, (T j).isA = false ∧
        ¬ (pOf v : ℤ_[pOf v]) ^ (K + 1) ∣ (f.map (Int.castRingHom ℤ_[pOf v])).eval (T j).x) ∧
      ∀ a : ℤ, PrimRepZp (pOf v) f a → ¬ (pOf v : ℤ_[pOf v]) ^ (K + 1) ∣ ((a : ℤ) : ℤ_[pOf v]) →
        ∃ j, (T j).Cond a := by
  obtain ⟨N, x, hx, hcov⟩ := exists_class_reps (f.map (Int.castRingHom ℤ_[pOf v])) K
  refine ⟨N, fun j => LocTarget.ofPrim (x j) (hx j).1 (hx j).2.1, fun j => ⟨rfl, (hx j).2.2⟩, fun a ha hK => ?_⟩
  obtain ⟨j, β, hβ, hab⟩ := hcov _ ((primRepZp_iff_map f a).mp ha) hK
  exact ⟨j, (LocTarget.cond_ofPrim _ _ _ a).mpr ⟨β, hβ, hab⟩⟩

/-- **Local options at a place** (Cassels, p. 245): finitely many local targets at $v$ such that every $a$ primitively
represented by $f$ over $\mathbb Z_p$ satisfies the condition of one of them. Isotropic case: the target $\mathbf t$ of Lemma 9.3
for $p^{\mu+1} \mid a$ and class representatives otherwise; anisotropic case: class representatives
(`not_dvd_of_anisotropic`). -/
theorem exists_options (f : QuadForm ℤ 4) (hf : f.hessian.det ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (N : ℕ) (T : Fin N → LocTarget f v), ∀ a : ℤ, PrimRepZp (pOf v) f a → ∃ j, (T j).Cond a := by
  classical
  set Q := f.map (Int.castRingHom ℤ_[pOf v]) with hQ
  have hdet : Q.hessian.det ≠ 0 := by
    rw [hQ, hessian_det_map, eq_intCast]; exact_mod_cast hf
  by_cases hiso : (Q.map PadicInt.Coe.ringHom).IsotropicIn ℚ_[pOf v]
  · obtain ⟨t, B, μ, u1, u2, S⟩ := exists_shape93 Q hdet hiso
    obtain ⟨N, T, -, hcov⟩ := exists_prim_targets f v μ
    refine ⟨N + 1, Fin.cons (α := fun _ => LocTarget f v) (LocTarget.ofShape S) T, fun a ha => ?_⟩
    by_cases hdv : (pOf v : ℤ) ^ (μ + 1) ∣ a
    · exact ⟨0, by rw [Fin.cons_zero]; exact (LocTarget.cond_ofShape S a).mpr hdv⟩
    · have hK : ¬ (pOf v : ℤ_[pOf v]) ^ (μ + 1) ∣ ((a : ℤ) : ℤ_[pOf v]) := by
        intro h
        apply hdv
        have h2 := (pow_dvd_sub_iff_toZModPow (μ + 1) ((a : ℤ) : ℤ_[pOf v]) 0).mp (by simpa using h)
        rw [map_intCast, map_zero] at h2
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd a ((pOf v) ^ (μ + 1))).mp h2
        exact_mod_cast this
      obtain ⟨j, hj⟩ := hcov a ha hK
      exact ⟨j.succ, by rw [Fin.cons_succ]; exact hj⟩
  · obtain ⟨δ, w, hw, hδ⟩ := decomp hdet
    obtain ⟨N, T, -, hcov⟩ := exists_prim_targets f v (2 * δ)
    refine ⟨N, T, fun a ha => hcov a ha ?_⟩
    obtain ⟨y, hy, hya⟩ := (primRepZp_iff_map f a).mp ha
    rw [← hya]
    exact not_dvd_of_anisotropic Q hw hδ hiso y hy

/-- **Local options at $q$**: class representatives with unit values cover every $a$ with $q \nmid a$ that is primitively
represented over $\mathbb Z_q$. -/
theorem exists_options_q (f : QuadForm ℤ 4) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (N : ℕ) (T : Fin N → LocTarget f v), (∀ j, (T j).isA = false ∧
        IsUnit ((f.map (Int.castRingHom ℤ_[pOf v])).eval (T j).x)) ∧
      ∀ a : ℤ, PrimRepZp (pOf v) f a → ¬ (pOf v : ℤ) ∣ a → ∃ j, (T j).Cond a := by
  obtain ⟨N, T, hT, hcov⟩ := exists_prim_targets f v 0
  refine ⟨N, T, fun j => ⟨(hT j).1, ?_⟩, fun a ha hqa => hcov a ha ?_⟩
  · have := (hT j).2
    rw [zero_add, pow_one] at this
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => this ((PadicInt.norm_lt_one_iff_dvd _).mp hlt))
  · rw [zero_add, pow_one]
    intro h
    exact PadicInt.p_nonunit (isUnit_of_dvd_unit h ((isUnit_intCast_iff a).mpr hqa))

/-- **The construction of Cassels' proof of Lemma 9.2** (Ch. 11, pp. 245–249), proved: for every positive definite
classically integral quaternary $f$ and odd prime $q$ with $d(f) \in U_q^2$ there is a family of data as in `Lemma92Family`.
The types are the choices of one local option at each place over $P \cup \{q\}$ (`exists_options`, `exists_options_q`); for
each type `exists_datum_of_targets` gives the datum. -/
@[kb "cassels1978" "Ch. 11, proof of Lemma 9.2, pp. 245–249 (construction of u, Γ and the finite sets of b), proved"]
theorem lemma92FamilyStatement_holds : Lemma92FamilyStatement := by
  refine ⟨fun f hf hci q _ hq2 hsq => ?_⟩
  classical
  have hq : q.Prime := Fact.out
  have hdet0 : f.hessian.det ≠ 0 := IntQF.PosDef.nondegenerate hf
  let T0 := T0set f q
  let P := {v : HeightOneSpectrum (𝓞 ℚ) // Rat.HeightOneSpectrum.natGenerator v ∈ T0}
  letI : Fintype P := (finite_places T0).fintype
  have hopt : ∀ v : P, ∃ (N : ℕ) (T : Fin N → LocTarget f v.1),
      (Rat.HeightOneSpectrum.natGenerator v.1 = q → ∀ j, (T j).isA = false ∧
        IsUnit ((f.map (Int.castRingHom ℤ_[pOf v.1])).eval (T j).x)) ∧
      ∀ a : ℤ, ¬ (q : ℤ) ∣ a → PrimRepZp (pOf v.1) f a → ∃ j, (T j).Cond a := by
    intro v
    by_cases hvq : Rat.HeightOneSpectrum.natGenerator v.1 = q
    · obtain ⟨N, T, hT, hcov⟩ := exists_options_q f v.1
      refine ⟨N, T, fun _ => hT, fun a hqa ha => hcov a ha ?_⟩
      rw [pOf_eq, hvq]; exact hqa
    · obtain ⟨N, T, hcov⟩ := exists_options f hdet0 v.1
      exact ⟨N, T, fun h => absurd h hvq, fun a _ ha => hcov a ha⟩
  choose N T hTq hTcov using hopt
  have hD : ∀ κ : (∀ v : P, Fin (N v)), ∃ D : L92Datum f q hq, ∀ k : ℕ, ∃ B : Finset ℤ, ∀ a : ℤ, ¬ (q : ℤ) ∣ a →
      (∀ v (hv : Rat.HeightOneSpectrum.natGenerator v ∈ T0), (T ⟨v, hv⟩ (κ ⟨v, hv⟩)).Cond a) →
        ∃ b ∈ B, LocalOK D k a b := by
    intro κ
    exact exists_datum_of_targets f hf hci hq hq2 hsq (fun v hv => T ⟨v, hv⟩ (κ ⟨v, hv⟩))
      (fun hv => hTq ⟨placeOf q hq, hv⟩ (natGenerator_placeOf q hq) _)
  choose D hD using hD
  let e := Fintype.equivFin (∀ v : P, Fin (N v))
  refine ⟨Fintype.card (∀ v : P, Fin (N v)), fun i => D (e.symm i), fun k => ?_⟩
  choose B hB using fun κ => hD κ k
  refine ⟨fun i => B (e.symm i), fun a hqa hloc => ?_⟩
  have hty : ∀ v : P, ∃ j, (T v j).Cond a := fun v => hTcov v a hqa (hloc (pOf v.1))
  choose κ hκ using hty
  obtain ⟨b, hb, hok⟩ := hB κ a hqa (fun v hv => hκ ⟨v, hv⟩)
  exact ⟨e κ, b, by simpa using hb, by simpa using hok⟩

/-- **Cassels, Lemma 9.2, proved** (Ch. 11, p. 242): for a positive definite classically integral quaternary form $Q$ of
determinant $d$ and an odd prime $q$ with $d \in U_q^2$, $\mathcal R(Q, a)$ holds for all $a > N_1(Q, q)$ with $q \nmid a$. -/
@[kb "cassels1978" "Ch. 11, Lemma 9.2, p. 242 (proof pp. 243–249)"]
theorem lemma92_holds : Lemma92 := lemma92_of_family lemma92FamilyStatement_holds

/-- **Theorem 1.6 for $n = 4$, unconditional** (Cassels, Ch. 11, p. 204 and pp. 242–243; classically integral forms): a
positive definite classically integral quaternary form $Q$ primitively represents over $\mathbb Z$ every sufficiently large integer
that it primitively represents over every $\mathbb Z_p$ (`TartakowskyClassicalAt 4`).
`Ch11Lemma91.tartakowskyClassicalAt_four_of_lemma92` with Lemma 9.2 supplied by `lemma92_holds`. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.6 for n = 4, pp. 242–243 (unconditional)"]
theorem tartakowskyClassicalAt_four_holds : TartakowskyClassicalAt 4 :=
  Ch11Lemma91.tartakowskyClassicalAt_four_of_lemma92 lemma92_holds

end QuadFormsKB.Cassels.Ch11L92
