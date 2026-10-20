/-
# A gap at $0$ for the local density over a complete DVR (isotropic forms)

**Layer:** DVR ($R$ a complete discrete valuation ring with uniformizer $\pi$, finite residue field, $2 \ne 0$; e.g. the
completion $\mathfrak o_\mathfrak p$ of a number field at any prime $\mathfrak p$, dyadic included).

**Theorem** (`DVR.exists_localDensity_gap`). Let $Q$ be nondegenerate over $R$ in $n \ge 3$ variables and isotropic over the
fraction field $K$. There is $c > 0$ such that every $m \ne 0$ with $\beta_\pi(m) > 0$ has $\beta_\pi(m) \ge c$.

This is the local core of Hanke 2004, Thm 5.7(c) (p. 373) at an isotropic prime, and the DVR version of
`Siegel.localDensityGap_of_five_le` over $\mathbb Q$. *Proof* (purely local). Let $K_0 = \mathrm{ord}_\pi(4N) + 1$ (`depthLevel`).
1. *Strip $\pi^2$* (`exists_pow_sq_mul_reduced`): $m = \pi^{2\nu}T$ with $\pi^{K_0+2} \nmid T$, and $\pi^{K_0} \mid T$ if $\nu \ge 1$.
2. If $\nu = 0$, $\beta_\pi(m) = \beta_\pi(T)$. If $\nu \ge 1$: $\beta_\pi(m) > 0$ makes $m$ locally represented
   (`isLocallyRepresentedAt_of_localDensity_pos`), hence $T$ (deep square classes, `isLocallyRepresentedAt_pow_mul_iff`), hence $T$
   is $\pi$-stable (Remark 3.6.1, `isPStable_of_dvd`), and (5.11) (`localDensity_pow_sq_ge`) gives
   $\beta_\pi(m) \ge C'_\pi(T)\beta_\pi(T)$, with $C'_\pi(T) > 0$ since $Q$ is isotropic (`localConstC_pos`).
3. *Local constancy* (`localDensity_congr`, `localConstC_congr`): on $\{T \ne 0 : \pi^{K_0+2} \nmid T\}$ both $\beta_\pi(T)$ and
   $C'_\pi(T)$ depend only on $T \bmod \pi^{2K_0+1}$, and $R/\pi^{2K_0+1}$ is finite, so they take finitely many values; $c$ is
   the least of the finitely many positive values of $\beta_\pi(T)$ and $C'_\pi(T)\beta_\pi(T)$.

**Depends on** `DVRDepth.lean` (Remarks 3.5.1, 3.6.1, local constancy), `DVRLowerBounds.lean` ((5.11), $C_\pi > 0$).
-/
import QuadFormsKB.LocalDensity.NFDepth

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Filter

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

local notation "𝔽" => IsLocalRing.ResidueField R

/-- **$\beta_\pi(m) > 0 \Rightarrow m$ is locally represented** ($\beta_\pi(m) = r_{\pi^k}(m)/q^{k(n-1)}$ for $k$ large). -/
theorem isLocallyRepresentedAt_of_localDensity_pos [Finite 𝔽] (Q : QuadForm R n) (hQ : Q.Nondegenerate)
    (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) {m : R} (hm : m ≠ 0) (h : 0 < localDensity Q π m) :
    IsLocallyRepresentedAt Q π m := by
  filter_upwards [localDensity_eventually_eq Q hQ π hπ m hm h20] with k hk
  rw [← hk] at h
  have hq : (0 : ℝ) < (q R : ℝ) ^ (k * (n - 1)) := pow_pos (by exact_mod_cast (q_pos (R := R))) _
  have : (0 : ℝ) < repCount Q π k m := by
    by_contra h0
    have := div_nonpos_of_nonpos_of_nonneg (not_lt.1 h0) hq.le
    linarith
  exact_mod_cast this

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- $\pi^{j+1} \nmid \pi^j w$ when $\pi \nmid w$. -/
theorem not_pow_succ_dvd_pow_mul {π w : R} (hπ0 : π ≠ 0) [IsDomain R] (hw : ¬ π ∣ w) (j : ℕ) :
    ¬ π ^ (j + 1) ∣ π ^ j * w := by
  rintro ⟨c, hc⟩
  apply hw
  refine ⟨c, mul_left_cancel₀ (pow_ne_zero j hπ0) ?_⟩
  rw [hc]; ring

/-- **Stripping $\pi^2$** over $R$: every $m \ne 0$ is $\pi^{2\nu}T$ with $\pi^{K+2} \nmid T$, and $\pi^K \mid T$ if $\nu \ge 1$
(any $K$). -/
theorem exists_pow_sq_mul_reduced (π : R) (hπ : Irreducible π) (K : ℕ) {m : R} (hm : m ≠ 0) :
    ∃ ν : ℕ, ∃ T : R, m = π ^ (2 * ν) * T ∧ T ≠ 0 ∧ ¬ π ^ (K + 2) ∣ T ∧ (ν ≠ 0 → π ^ K ∣ T) := by
  obtain ⟨e, ⟨w, rfl⟩, he⟩ := exists_pow_dvd_not_dvd π hπ hm
  have hπ0 := hπ.ne_zero
  have hw : ¬ π ∣ w := fun h => he (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (dvd_zero _)
  by_cases hsmall : e < K + 2
  · refine ⟨0, π ^ e * w, by simp, mul_ne_zero (pow_ne_zero _ hπ0) hw0, fun h => ?_, fun h => absurd rfl h⟩
    exact not_pow_succ_dvd_pow_mul hπ0 hw e ((pow_dvd_pow π (by omega)).trans h)
  · set ν := (e - K) / 2 with hν
    have h1 : K ≤ e - 2 * ν := by omega
    have h2 : e - 2 * ν ≤ K + 1 := by omega
    refine ⟨ν, π ^ (e - 2 * ν) * w, ?_, mul_ne_zero (pow_ne_zero _ hπ0) hw0, fun h => ?_,
      fun _ => (pow_dvd_pow π h1).trans (dvd_mul_right _ _)⟩
    · rw [← mul_assoc, ← pow_add, show 2 * ν + (e - 2 * ν) = e by omega]
    · exact not_pow_succ_dvd_pow_mul hπ0 hw _ ((pow_dvd_pow π (by omega)).trans h)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- A function on $R$ that is constant on the classes of an ideal $I$ with $R/I$ finite, among the $T$ with property $P$, takes
finitely many values on $P$. -/
theorem finite_image_of_congr_ideal {I : Ideal R} [Finite (R ⧸ I)] (P : R → Prop) (f : R → ℝ)
    (hf : ∀ T T', P T → P T' → T - T' ∈ I → f T = f T') :
    {x : ℝ | ∃ T, P T ∧ x = f T}.Finite := by
  classical
  let g : R ⧸ I → ℝ := fun r => if h : ∃ T, P T ∧ Ideal.Quotient.mk I T = r then f h.choose else 0
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨T, hT, rfl⟩
  refine ⟨Ideal.Quotient.mk I T, ?_⟩
  have hex : ∃ T', P T' ∧ Ideal.Quotient.mk I T' = Ideal.Quotient.mk I T := ⟨T, hT, rfl⟩
  obtain ⟨h1, h2⟩ := hex.choose_spec
  simp only [g, hex, ↓reduceDIte]
  exact hf _ _ h1 hT (Ideal.Quotient.eq.1 h2)

/-- A finite set of positive reals has a positive lower bound. -/
theorem exists_pos_le_of_finite' {A : Set ℝ} (hA : A.Finite) (hpos : ∀ x ∈ A, 0 < x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ A, c ≤ x := by
  classical
  by_cases hne : hA.toFinset.Nonempty
  · refine ⟨hA.toFinset.min' hne, hpos _ ((Set.Finite.mem_toFinset hA).1 (Finset.min'_mem _ hne)),
      fun x hx => Finset.min'_le _ _ ((Set.Finite.mem_toFinset hA).2 hx)⟩
  · refine ⟨1, one_pos, fun x hx => absurd ⟨x, (Set.Finite.mem_toFinset hA).2 hx⟩ hne⟩

/-- **A gap at $0$ for $\beta_\pi$ at an isotropic prime** (the local core of Hanke 2004, Thm 5.7(c), p. 373, over a complete DVR;
every prime with $2 \ne 0$, dyadic included). For $Q$ nondegenerate over $R$ in $n \ge 3$ variables and isotropic over the
fraction field $K$, there is $c > 0$ with $c \le \beta_\pi(m)$ for every $m \ne 0$ such that $\beta_\pi(m) > 0$.
*Proof:* strip $\pi^2$, (5.11) with $C'_\pi > 0$, and local constancy of $\beta_\pi$, $C'_\pi$ modulo $\pi^{2K_0+1}$ (see the module
docstring). -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (local factor at an isotropic prime: uniform lower bound), via (5.11) and local constancy"]
theorem exists_localDensity_gap [Finite 𝔽] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (Q : QuadForm R n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (π : R)
    (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (hiso : Q.IsotropicIn K) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : R, m ≠ 0 → 0 < localDensity Q π m → c ≤ localDensity Q π m := by
  classical
  obtain ⟨e, he⟩ := exists_pow_dvd_not_dvd π hπ h20
  set K₀ := depthLevel Q π e with hK₀
  set I : Ideal R := Ideal.span {π ^ (2 * K₀ + 1)}
  have : Finite (R ⧸ I) := finite_quot_pow π hπ _
  let Red : R → Prop := fun T => T ≠ 0 ∧ ¬ π ^ (K₀ + 2) ∣ T
  have hcongr : ∀ T T', Red T → T - T' ∈ I →
      localDensity Q π T = localDensity Q π T' ∧ localConstC' Q π T = localConstC' Q π T' := by
    intro T T' hT hI
    have hd : π ^ (K₀ + 1 + depthLevel Q π e) ∣ T - T' := by
      rw [← hK₀, show K₀ + 1 + K₀ = 2 * K₀ + 1 by ring]
      exact Ideal.mem_span_singleton.1 hI
    exact ⟨localDensity_congr Q hQ π hπ h20 e he hT.2 hd, (localConstC_congr Q hQ π hπ h20 e he hT.2 hd).2⟩
  let P₁ : R → Prop := fun T => Red T ∧ 0 < localDensity Q π T
  let P₂ : R → Prop := fun T => Red T ∧ π ^ K₀ ∣ T ∧ IsLocallyRepresentedAt Q π T
  have hA₁ := finite_image_of_congr_ideal (I := I) P₁ (fun T => localDensity Q π T)
    (fun T T' hT _ h => (hcongr T T' hT.1 h).1)
  have hA₂ := finite_image_of_congr_ideal (I := I) P₂ (fun T => localConstC' Q π T * localDensity Q π T)
    (fun T T' hT _ h => by
      obtain ⟨h1, h2⟩ := hcongr T T' hT.1 h
      simp only [h1, h2])
  have hstab : ∀ T, P₂ T → IsPStable Q ∅ π T := fun T hT => by
    refine isPStable_of_dvd Q hQ π hπ h20 e he ∅ ((pow_dvd_pow _ ?_).trans hT.2.1) hT.2.2
    rw [hK₀, depthLevel]; omega
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_of_finite' (hA₁.union hA₂) (by
    rintro x (⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩)
    · exact hT.2
    · exact mul_pos (lt_min one_pos (localConstC_pos K Q hQ hn π hπ h20 ∅ hiso T hT.1.1 (hstab T hT)))
        (localDensity_pos_of_isLocallyRepresentedAt Q hQ π hπ h20 T hT.1.1 hT.2.2))
  refine ⟨c, hc0, fun m hm hpos => ?_⟩
  obtain ⟨ν, T, rfl, hT0, hTred, hTK⟩ := exists_pow_sq_mul_reduced π hπ K₀ hm
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · simp only [mul_zero, pow_zero, one_mul] at hpos ⊢
    exact hc _ (Or.inl ⟨T, ⟨⟨hT0, hTred⟩, hpos⟩, rfl⟩)
  · have hK := hTK hν.ne'
    have hlocm := isLocallyRepresentedAt_of_localDensity_pos Q hQ π hπ h20 hm hpos
    have hlocT := (isLocallyRepresentedAt_pow_mul_iff Q hQ π hπ h20 e he hK ν).1 hlocm
    have hP₂ : P₂ T := ⟨⟨hT0, hTred⟩, hK, hlocT⟩
    exact (hc _ (Or.inr ⟨T, hP₂, rfl⟩)).trans
      (localDensity_pow_sq_ge Q hQ hn π hπ h20 ∅ T hT0 (hstab T hP₂) ν)

end QuadFormsKB.LocalDensity.DVR
