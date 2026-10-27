/-
# Hanke 2004, Theorem 6.4 for even $n \ge 6$ over $\mathbb Q$, via Hecke's bound (Tartakowsky's theorem)

**Theorem** (`thm_6_4_even_uncond`, **unconditional**). Let $Q$ be a positive definite integral quadratic form in an even number
$n = 2k \ge 6$ of variables. There is $M_0$ such that every integer $m \ge M_0$ that is locally represented at every prime $p$ is
represented by $Q$:
$$\exists M_0\ \forall m \ge M_0:\ \big(\forall p,\ m \text{ is locally represented at } p\big) \Rightarrow \exists x \in \mathbb Z^n,\ Q(x) = m.$$
`thm_6_4_even_uncond'` is the same with Hanke's extra hypothesis "$(m)_{\mathrm{Aniso}} \le B$", which is vacuous for $n \ge 5$: every $p$
is isotropic (`isIsotropicPrime_of_five_le`), so $(m)_{\mathrm{Aniso}} = 1$ (`anisoPart_eq_one_of_five_le`).

**Structure.**
* `tartakowsky_even`: the theorem from the named local input `LocalDensityGap Q p` at $p \mid 2\det H$ (a uniform positive lower bound
  for $\beta_p$ on the $m$ with $\beta_p(m) > 0$);
* `localDensityGap_of_five_le`: that input is a theorem for $n \ge 5$ at every prime (decomposition $m = p^{2\nu}T'$, (5.11), positivity
  of $C'_p$ at isotropic $p$, local constancy of $\beta_p$, $C'_p$; all from main: `LocalDensity/LowerBounds.lean`, `NFDepth.lean`).

No Siegel formula for the genus, no Deligne bound and no eigenform decomposition are used. The constant $M_0$ is **not explicit**: it
comes from Hecke's bound for the cusp form $\theta_Q - E_Q$ (a supremum over $\mathbb H$).

**Proof** (`HilbertModular/Tartakowsky.lean` at $F = \mathbb Q$). The single-lattice decomposition $\theta_Q = E_Q + (\theta_Q - E_Q)$
over $\mathcal O_{\mathbb Q} \cong \mathbb Z$, the coefficient formula $a_m(E_Q) = \beta_\infty(m)\prod_p\beta_p(m)$ (with
$|d_{\mathbb Q}| = 1$), Hecke's bound $|r_Q(m) - a_E(m)| \le C m^{k/2}$, and the lower bound $a_E(m) \ge \kappa m^{k-1}$ (good primes
explicit, bad primes from `LocalDensityGap`). Here $k - 1 > k/2$ since $k \ge 3$.

*Comparison with `thm_6_4_even`* (conditional on Siegel's formula, `ThetaSplit`, and Deligne's bound (4.8) through `CuspBound`):
that version gives the explicit threshold $m^{(n-2)/4}/\tau(m) > C/\hat\Lambda_n$ with $C = \sum_i|\gamma_i|$ from (4.7); this one has
no inputs, but $M_0$ is only shown to exist. `thm_6_4_even_hecke` (`Siegel/HeckeBound.lean`) is the Hanke-shaped intermediate (Hecke
in place of Deligne, Siegel's formula and `hglob` kept).

Sources: Hanke 2004, Thm 6.4, p. 382; Tartakowsky, *Die Gesamtheit der Zahlen, die durch eine positive quadratische Form
$F(x_1, \dots, x_s)$ ($s \ge 4$) darstellbar sind*, Izv. Akad. Nauk SSSR (1929) [unverified]; Iwaniec, *Topics in Classical Automorphic
Forms*, Thm 5.1 (Hecke's bound) and §11 [unverified].
-/
import QuadFormsKB.HilbertModular.Tartakowsky
import QuadFormsKB.Siegel.HeckeBound
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Tamagawa.SiegelAllRanks

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

open LocalDensity

variable {n : ℕ}

/-! ### $n \ge 5$: no anisotropic primes -/

/-- **Every prime is isotropic for $n \ge 5$** (Serre, *A Course in Arithmetic*, Ch. IV, §2.2, Thm 6; `isotropic_padic_of_five_le`): a
nondegenerate integral form in $n \ge 5$ variables is isotropic over $\mathbb Q_p$ for every prime $p$. -/
@[kb "serre1973" "Ch. IV, §2.2, Thm. 6 (n ≥ 5: isotropic at every p)"]
theorem isIsotropicPrime_of_five_le (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n) {p : ℕ}
    (hp : p.Prime) : IsIsotropicPrime Q p := by
  have := Fact.mk hp
  refine ⟨hp, ?_⟩
  have hQ' : (Q.map (Int.castRingHom ℚ)).Nondegenerate := by
    have e : (Q.map (Int.castRingHom ℚ)).hessian = Q.hessian.map (Int.castRingHom ℚ) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [QuadForm.Nondegenerate, e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h; apply hQ; simpa using h
  obtain ⟨x, hx, h0⟩ := isotropic_padic_of_five_le p _ hn hQ'
  refine ⟨x, hx, ?_⟩
  rwa [evalIn_map_intCast] at h0

/-- **For $n \ge 5$ the anisotropic part is trivial**: $(m)_{\mathrm{Aniso}} = 1$ for every $m$ (`isIsotropicPrime_of_five_le`). So
Hanke's hypothesis of Thm 6.4, "a priori bounded divisibility at the anisotropic primes", holds for every $m$. -/
theorem anisoPart_eq_one_of_five_le (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n) (m : ℕ) :
    anisoPart Q m = 1 := by
  classical
  unfold anisoPart
  refine Finset.prod_eq_one fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  simp [isIsotropicPrime_of_five_le Q hQ hn hpp]

/-! ### The local input over $\mathbb Q$ -/

/-- **Input (local, per bad prime): a gap at $0$ for the local density** $\beta_p$ (the $\mathbb Q$ form of `LocalDensityGapNF`). There is
$c_p > 0$ such that every integer $m \ne 0$ with $\beta_p(m) > 0$ (e.g. $m$ locally represented at $p$,
`localDensity_pos_of_isLocallyRepresentedAt`) has $\beta_p(m) \ge c_p$.

For $n \ge 5$ this is the local core of Hanke 2004, Thm 5.7(c): writing $m = p^{2\nu}T'$ with $T'$ bad-reduced at $p$, (5.11)
(`localDensity_pow_sq_ge`) gives $\beta_p(m) \ge C'_p(T')\beta_p(T')$ with $C'_p(T') > 0$ ($p$ isotropic, `localConstC'_pos_of_isotropic`),
and $\beta_p(T')$, $C'_p(T')$ take finitely many values (`finite_badFactor_image`). It is assumed only at $p \mid 2\det H$
(`badPrimes`); to be discharged by the per-place lower bounds.

Fields:
- `exists_le`: there is $c > 0$ with $c \le \beta_p(m)$ for every integer $m \ne 0$ such that $0 < \beta_p(m)$. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (local factor at p | 2 det H, n ≥ 5; via (5.11) and B_T finite)"]
structure LocalDensityGap (Q : QuadForm ℤ n) (p : ℕ) : Prop where
  exists_le : ∃ c : ℝ, 0 < c ∧ ∀ m : ℤ, m ≠ 0 → 0 < localDensity Q p m → c ≤ localDensity Q p m

/-! ### Discharging `LocalDensityGap` for $n \ge 5$ (every prime isotropic) -/

/-- $\beta_p(m) > 0 \Rightarrow m$ is locally represented at $p$ ($\beta_p(m) = r_{p^k}(m)/p^{k(n-1)}$ for $k$ large). -/
theorem isLocallyRepresentedAt_of_localDensity_pos (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ)
    [Fact p.Prime] {m : ℤ} (hm : m ≠ 0) (h : 0 < localDensity Q p m) : IsLocallyRepresentedAt Q p m := by
  filter_upwards [localDensity_eventually_eq Q hQ p m hm] with k hk
  rw [← hk] at h
  have hp : (0 : ℝ) < (p : ℝ) ^ (k * (n - 1)) := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  have : (0 : ℝ) < repCount Q p k m := by
    by_contra h0
    have := div_nonpos_of_nonpos_of_nonneg (not_lt.1 h0) hp.le
    linarith
  exact_mod_cast this

/-- **Stripping $p^2$**: every $m \ne 0$ is $p^{2\nu}T$ with $p^{K+2} \nmid T$, and $p^K \mid T$ if $\nu \ge 1$ (any $K$). -/
theorem exists_pow_sq_mul_reduced (p K : ℕ) (hp : p.Prime) {m : ℤ} (hm : m ≠ 0) :
    ∃ ν : ℕ, ∃ T : ℤ, m = (p : ℤ) ^ (2 * ν) * T ∧ T ≠ 0 ∧ ¬ (p : ℤ) ^ (K + 2) ∣ T ∧
      (ν ≠ 0 → (p : ℤ) ^ K ∣ T) := by
  induction h : m.natAbs using Nat.strong_induction_on generalizing m with
  | _ N IH =>
  by_cases hred : (p : ℤ) ^ (K + 2) ∣ m
  · obtain ⟨m₁, hm₁⟩ : (p : ℤ) ^ 2 ∣ m := (pow_dvd_pow (p : ℤ) (by omega)).trans hred
    have hp2 : (1 : ℤ) < (p : ℤ) ^ 2 := by
      have : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
      nlinarith
    have hm₁0 : m₁ ≠ 0 := by rintro rfl; simp at hm₁; exact hm hm₁
    have hlt : m₁.natAbs < N := by
      rw [← h, hm₁, Int.natAbs_mul]
      have h1 : 1 < ((p : ℤ) ^ 2).natAbs := by
        rw [Int.natAbs_pow]; exact Nat.one_lt_pow (by norm_num) (by simpa using hp.one_lt)
      have h2 : 0 < m₁.natAbs := Int.natAbs_pos.2 hm₁0
      nlinarith
    have hK : (p : ℤ) ^ K ∣ m₁ := by
      rw [hm₁, show K + 2 = 2 + K by ring, pow_add] at hred
      exact (mul_dvd_mul_iff_left (pow_ne_zero 2 (by exact_mod_cast hp.ne_zero))).1 hred
    obtain ⟨ν, T, h1, hT0, hTred, hTK⟩ := IH _ hlt hm₁0 rfl
    refine ⟨ν + 1, T, by rw [hm₁, h1]; ring, hT0, hTred, fun _ => ?_⟩
    by_cases hν : ν = 0
    · subst hν; simp at h1; rw [← h1]; exact hK
    · exact hTK hν
  · exact ⟨0, m, by simp, hm, hred, fun h => absurd rfl h⟩

/-- A function of $T \in \mathbb Z$ that is constant on residue classes mod $M$ among the $T$ with property $P$ takes finitely many
values on $P$. -/
theorem finite_image_of_congr {M : ℕ} [NeZero M] (P : ℤ → Prop) (f : ℤ → ℝ)
    (hf : ∀ T T', P T → P T' → (M : ℤ) ∣ T - T' → f T = f T') :
    {x : ℝ | ∃ T, P T ∧ x = f T}.Finite := by
  classical
  let g : ZMod M → ℝ := fun r => if h : ∃ T, P T ∧ (T : ZMod M) = r then f h.choose else 0
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨T, hT, rfl⟩
  refine ⟨(T : ZMod M), ?_⟩
  have hex : ∃ T', P T' ∧ (T' : ZMod M) = (T : ZMod M) := ⟨T, hT, rfl⟩
  obtain ⟨h1, h2⟩ := hex.choose_spec
  simp only [g, hex, ↓reduceDIte]
  exact hf _ _ h1 hT ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2.symm)

/-- A finite set of positive reals has a positive lower bound. -/
theorem exists_pos_le_of_finite {A : Set ℝ} (hA : A.Finite) (hpos : ∀ x ∈ A, 0 < x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ A, c ≤ x := by
  classical
  by_cases hne : hA.toFinset.Nonempty
  · refine ⟨hA.toFinset.min' hne, hpos _ ((Set.Finite.mem_toFinset hA).1 (Finset.min'_mem _ hne)),
      fun x hx => Finset.min'_le _ _ ((Set.Finite.mem_toFinset hA).2 hx)⟩
  · refine ⟨1, one_pos, fun x hx => absurd ⟨x, (Set.Finite.mem_toFinset hA).2 hx⟩ hne⟩

/-- **`LocalDensityGap` holds at every prime for $n \ge 5$** (the local core of Hanke 2004, Thm 5.7(c), over $\mathbb Q$). Let $K = K_0(p)$
(`depthLevelP`). Write $m = p^{2\nu}T$ with $p^{K+2} \nmid T$ and $p^K \mid T$ if $\nu \ge 1$ (`exists_pow_sq_mul_reduced`). If $\nu = 0$,
$\beta_p(m) = \beta_p(T)$; if $\nu \ge 1$, $T$ is $p$-stable (Remark 3.6.1, `isPStable_of_dvd_padic`) and locally represented, and
(5.11) gives $\beta_p(m) \ge C'_p(T)\beta_p(T)$ with $C'_p(T) > 0$ since $p$ is isotropic (`localConstC'_pos_of_isotropic`). Both
$\beta_p(T)$ and $C'_p(T)\beta_p(T)$ depend only on $T \bmod p^{2K+1}$ (`localDensity_congr_padic`), so they take finitely many positive
values, whose minimum is $c_p$. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (local factor at p, n ≥ 5: uniform lower bound), via (5.11) and local constancy"]
theorem localDensityGap_of_five_le (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n) {p : ℕ}
    (hp : p.Prime) : LocalDensityGap Q p := by
  classical
  have := Fact.mk hp
  have hiso := (isIsotropicPrime_of_five_le Q hQ hn hp).2
  set K := depthLevelP Q p with hKdef
  set M : ℕ := p ^ (2 * K + 1)
  have : NeZero M := ⟨pow_ne_zero _ hp.ne_zero⟩
  let Red : ℤ → Prop := fun T => T ≠ 0 ∧ ¬ (p : ℤ) ^ (K + 2) ∣ T
  have hcongr : ∀ T T', Red T → (M : ℤ) ∣ T - T' →
      localDensity Q p T = localDensity Q p T' ∧ localConstC' Q p T = localConstC' Q p T' := by
    intro T T' hT hM
    refine localDensity_congr_padic Q hQ p (a := K + 1) hT.2 ?_
    have : (M : ℤ) = (p : ℤ) ^ (K + 1 + depthLevelP Q p) := by
      simp only [M, hKdef]; push_cast; ring_nf
    rwa [← this]
  let P₁ : ℤ → Prop := fun T => Red T ∧ 0 < localDensity Q p T
  let P₂ : ℤ → Prop := fun T => Red T ∧ (p : ℤ) ^ K ∣ T ∧ IsLocallyRepresentedAt Q p T
  have hA₁ := finite_image_of_congr (M := M) P₁ (fun T => localDensity Q p T)
    (fun T T' hT _ h => (hcongr T T' hT.1 h).1)
  have hA₂ := finite_image_of_congr (M := M) P₂ (fun T => localConstC' Q p T * localDensity Q p T)
    (fun T T' hT _ h => by
      obtain ⟨h1, h2⟩ := hcongr T T' hT.1 h
      simp only [h1, h2])
  have hstab : ∀ T, P₂ T → IsPStable Q ∅ p T := fun T hT => by
    refine isPStable_of_dvd_padic Q hQ ∅ p ((pow_dvd_pow _ ?_).trans hT.2.1) hT.2.2
    rw [hKdef, depthLevelP, DVR.depthLevel]; unfold levelExpP; omega
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_of_finite (hA₁.union hA₂) (by
    rintro x (⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩)
    · exact hT.2
    · exact mul_pos (localConstC'_pos_of_isotropic Q hQ (by omega) p ∅ hiso T hT.1.1 (hstab T hT))
        (localDensity_pos_of_isLocallyRepresentedAt Q hQ p T hT.1.1 hT.2.2))
  refine ⟨⟨c, hc0, fun m hm hpos => ?_⟩⟩
  obtain ⟨ν, T, rfl, hT0, hTred, hTK⟩ := exists_pow_sq_mul_reduced p K hp hm
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · simp only [mul_zero, pow_zero, one_mul] at hpos ⊢
    exact hc _ (Or.inl ⟨T, ⟨⟨hT0, hTred⟩, hpos⟩, rfl⟩)
  · have hK := hTK hν.ne'
    have hlocm := isLocallyRepresentedAt_of_localDensity_pos Q hQ p hm hpos
    have hlocT := (isLocallyRepresentedAt_pow_mul_iff_padic Q hQ p hK ν).1 hlocm
    have hP₂ : P₂ T := ⟨⟨hT0, hTred⟩, hK, hlocT⟩
    exact (hc _ (Or.inr ⟨T, hP₂, rfl⟩)).trans
      (localDensity_pow_sq_ge Q hQ (by omega) p ∅ T hT0 (hstab T hP₂) ν)

/-! ### From $\mathbb Z$ to $\mathcal O_{\mathbb Q}$ -/

/-- $Q \otimes \mathcal O_{\mathbb Q}$. -/
abbrev toOQ (Q : QuadForm ℤ n) : QuadForm (𝓞 ℚ) n := Q.map (Int.castRingHom (𝓞 ℚ))

lemma formF_toOQ_eval (Q : QuadForm ℤ n) (x : Fin n → ℚ) :
    (HilbertModular.formF (toOQ Q)).eval x = Q.evalIn ℚ x := by
  simp [QuadForm.evalIn, QuadForm.map, HilbertModular.formF]

/-- A positive definite integral form is totally positive definite over $\mathbb Q$ (`Lattices.IsTotallyPosDef`). -/
theorem isTotallyPosDef_toOQ {Q : IntQF n} (hQ : Q.PosDef) :
    Lattices.IsTotallyPosDef (HilbertModular.formF (toOQ Q)) := by
  intro x hx σ
  have hx' : (fun i => (x i : ℝ)) ≠ 0 := by
    intro h; apply hx; funext i; simpa using congrFun h i
  have hpos : (0 : ℝ) < (((HilbertModular.formF (toOQ Q)).eval x : ℚ) : ℝ) := by
    have e : ((Q.evalIn ℚ x : ℚ) : ℝ) = Q.evalIn ℝ (fun i => (x i : ℝ)) :=
      evalIn_intForm_map (Rat.castHom ℝ) Q x
    rw [formF_toOQ_eval, e]
    exact hQ.evalIn_real_pos _ hx'
  have hσ : σ ((HilbertModular.formF (toOQ Q)).eval x) = (((HilbertModular.formF (toOQ Q)).eval x : ℚ) : ℂ) := by
    simp
  rw [hσ, show (((HilbertModular.formF (toOQ Q)).eval x : ℚ) : ℂ) =
    ((((HilbertModular.formF (toOQ Q)).eval x : ℚ) : ℝ) : ℂ) by push_cast; rfl]
  exact Complex.zero_lt_real.2 hpos

/-- $\mathfrak p \mid 2\det H$ over $\mathcal O_{\mathbb Q}$ implies $p \mid 2\det H$ for $p$ = `natGenerator`. -/
lemma natGenerator_mem_badPrimes {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ∈ badPrimesNF (toOQ Q)) : Rat.HeightOneSpectrum.natGenerator w ∈ badPrimes Q := by
  have hdet : (toOQ Q).hessian.det = ((Q.hessian.det : ℤ) : 𝓞 ℚ) := by
    have e : (toOQ Q).hessian = Q.hessian.map (Int.castRingHom (𝓞 ℚ)) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have h0 : (2 * (toOQ Q).hessian.det) ≠ 0 := by
    rw [hdet]; exact_mod_cast mul_ne_zero two_ne_zero hQ
  rw [badPrimesNF, mem_primesDividing h0, hdet] at hw
  have hz : ((2 * Q.hessian.det : ℤ) : 𝓞 ℚ) ∈ w.asIdeal := by
    rw [Int.cast_mul, Int.cast_ofNat]; exact hw
  have hmap : (2 * Q.hessian.det : ℤ) ∈ w.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    rw [Ideal.mem_map_of_equiv]
    exact ⟨_, hz, map_intCast _ _⟩
  rw [← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton] at hmap
  rw [badPrimes, Nat.mem_primeFactors]
  refine ⟨Rat.HeightOneSpectrum.prime_natGenerator w, Int.natCast_dvd.1 hmap,
    Int.natAbs_ne_zero.2 (mul_ne_zero two_ne_zero hQ)⟩

/-- `LocalDensityGap` at the bad primes over $\mathbb Z$ gives `LocalDensityGapNF` at the bad primes of $\mathcal O_{\mathbb Q}$
(`NF.localDensity_rat`). -/
theorem localDensityGapNF_toOQ {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate)
    (hgap : ∀ p ∈ badPrimes Q, LocalDensityGap Q p) :
    ∀ w ∈ badPrimesNF (toOQ Q), LocalDensityGapNF (toOQ Q) w := by
  intro w hw
  obtain ⟨c, hc0, hc⟩ := (hgap _ (natGenerator_mem_badPrimes hQ hw)).exists_le
  refine ⟨⟨c, hc0, fun m hm hpos => ?_⟩⟩
  obtain ⟨z, rfl⟩ : ∃ z : ℤ, ((z : ℤ) : 𝓞 ℚ) = m :=
    ⟨Rat.ringOfIntegersEquiv m, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
      (Rat.ringOfIntegersEquiv.symm_apply_apply m)⟩
  have hz : z ≠ 0 := by rintro rfl; exact hm (by simp)
  rw [NF.localDensity_rat] at hpos ⊢
  exact hc z hz hpos

/-! ### The theorem -/

/-- **Hanke 2004, Theorem 6.4 for even $n \ge 6$, with a non-explicit constant (Tartakowsky's theorem)**, via Hecke's bound. For $Q$
positive definite integral in $n = 2k \ge 6$ variables and the local input `LocalDensityGap Q p` at every $p \mid 2\det H$: there is
$M_0 \in \mathbb N$ such that every $m \ge M_0$ that is locally represented at every prime is represented by $Q$. (No anisotropic
primes exist for $n \ge 5$, `anisoPart_eq_one_of_five_le`.) $M_0$ exists but is not explicit. -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n even ≥ 6), via Hecke's bound: non-explicit constant (Tartakowsky)"]
theorem tartakowsky_even (Q : IntQF n) (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) (hk : 3 ≤ k)
    (hgap : ∀ p ∈ badPrimes Q, LocalDensityGap Q p) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → (∀ p : ℕ, p.Prime → IsLocallyRepresentedAt Q p m) →
      IntQF.Represents Q m := by
  have hQnd := hQ.nondegenerate
  obtain ⟨M, hM⟩ := HilbertModular.exists_eval_eq_of_localDensity_pos (isTotallyPosDef_toOQ hQ) hn hk
    (localDensityGapNF_toOQ hQnd hgap)
  refine ⟨⌈M⌉₊ + 1, fun m hm hloc => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hcast : algebraMap (𝓞 ℚ) ℚ ((m : ℤ) : 𝓞 ℚ) = (m : ℚ) := by simp
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  obtain ⟨y, hy⟩ := hM ((m : ℤ) : 𝓞 ℚ) (fun v => by
      rw [hcast, map_natCast]; exact hmR)
    (fun w hw => by
      have := Fact.mk (Rat.HeightOneSpectrum.prime_natGenerator w)
      rw [NF.localDensity_rat]
      exact localDensity_pos_of_isLocallyRepresentedAt Q hQnd _ m hm0
        (hloc _ (Rat.HeightOneSpectrum.prime_natGenerator w)))
    (by
      rw [hcast, Algebra.norm_self, MonoidHom.id_apply]
      have h1 : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
      have h2 : ((⌈M⌉₊ : ℕ) : ℝ) ≤ m := by exact_mod_cast (by omega : ⌈M⌉₊ ≤ m)
      rw [Rat.cast_natCast, abs_of_pos hmR]; linarith)
  refine ⟨fun i => Rat.ringOfIntegersEquiv (y i), ?_⟩
  have h1 := evalIn_intForm_map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) Q y
  change QuadForm.evalIn (𝓞 ℚ) (Q.map (Int.castRingHom (𝓞 ℚ))) y = _ at hy
  rw [evalIn_map_intCast] at hy
  rw [hy] at h1
  simpa using h1.symm

/-- **Hanke 2004, Theorem 6.4 for even $n \ge 6$, unconditional (non-explicit constant; Tartakowsky's theorem)**. For every positive
definite integral quadratic form $Q$ in an even number $n \ge 6$ of variables there is $M_0 \in \mathbb N$ such that every integer
$m \ge M_0$ that is locally represented by $Q$ at every prime $p$ is represented by $Q$ over $\mathbb Z$.

No inputs: `tartakowsky_even` with `LocalDensityGap` discharged at every prime (`localDensityGap_of_five_le`). The proof uses Hecke's
bound for the cusp form $\theta_Q - E_Q$ (no Deligne, no eigenform decomposition), the Fourier coefficients of the Eisenstein series
$E_Q$ (over $F = \mathbb Q$; no Siegel formula for the genus is needed), and the local lower bounds of §5.
$M_0$ exists but is
not explicit; compare `thm_6_4_even` (explicit threshold, conditional on Siegel's formula, (4.7) and Deligne's bound (4.8)). -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n even ≥ 6): unconditional, non-explicit constant (Tartakowsky), via Hecke's bound"]
theorem thm_6_4_even_uncond (Q : IntQF n) (hQ : Q.PosDef) (hn : 6 ≤ n) (heven : Even n) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → (∀ p : ℕ, p.Prime → IsLocallyRepresentedAt Q p m) →
      IntQF.Represents Q m := by
  obtain ⟨k, hk⟩ := heven
  exact tartakowsky_even Q hQ (k := k) (by omega) (by omega)
    (fun p hp => localDensityGap_of_five_le Q hQ.nondegenerate (by omega) ((mem_badPrimes hQ.nondegenerate).1 hp).1)

/-- **Thm 6.4 ($n \ge 6$ even) in Hanke's form**: for every bound $B$ there is $M_0$ such that every $m \ge M_0$ that is locally
represented at every prime and has $(m)_{\mathrm{Aniso}} \le B$ ("a priori bounded divisibility at the anisotropic primes") is
represented by $Q$. For $n \ge 5$ the second condition is automatic ($(m)_{\mathrm{Aniso}} = 1$, `anisoPart_eq_one_of_five_le`), so $M_0$
does not depend on $B$. Unconditional; $M_0$ not explicit. -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n even ≥ 6), as printed: locally represented, bounded anisotropic part (unconditional)"]
theorem thm_6_4_even_uncond' (Q : IntQF n) (hQ : Q.PosDef) (hn : 6 ≤ n) (heven : Even n) (B : ℕ) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → ((∀ p : ℕ, p.Prime → IsLocallyRepresentedAt Q p m) ∧ anisoPart Q m ≤ B) →
      IntQF.Represents Q m := by
  obtain ⟨M₀, h⟩ := thm_6_4_even_uncond Q hQ hn heven
  exact ⟨M₀, fun m hm hloc => h m hm hloc.1⟩

end QuadFormsKB.Siegel
