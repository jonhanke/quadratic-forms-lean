/-
# Depth and stability bounds over $\mathbb{Q}$ and over a number field

**Layer:** ℚ (forms `QuadForm ℤ n` at a prime $p$, via $\mathbb{Z}_p$: `Bridge.lean`, `BridgeExplicit.lean`) and number
field (forms `QuadForm (𝓞 F) n` at a prime $\mathfrak p$ = `v`, via $\mathfrak o_\mathfrak p$: `NFBridge.lean`, `NFLocal.lean`).

**Proves**, as instantiations of `DVRDepth.lean` (Hanke 2004, Lemma 3.4, Remarks 3.4.1(c), 3.5.1, 3.6.1, p. 361–362):

* uniform stabilization of the primitive counts from level $\mathrm{ord}_\mathfrak p(4N) + 1$ (`repCountOf_nonZero_succ_padic`,
  `NF.repCountNonZero_succ`);
* Remark 3.5.1 (`isLocallyRepresentedAt_iff_nonZero_padic`, `NF.isLocallyRepresentedAt_iff_nonZero`);
* Remark 3.6.1: $\mathfrak p$-stability of locally represented $m \in \mathfrak p^{\mathrm{ord}_\mathfrak p(4N) - 1}$, of $m \in \mathfrak p^{\mathrm{ord}_\mathfrak p N}$ as
  printed at $\mathfrak p \nmid 2$, and the global stable ideal $8\det H$ (`isStable_of_dvd_padic`, `NF.isStable_of_dvd`);
* representability of deep square classes and local constancy of $\beta_\mathfrak p$, $C'_\mathfrak p$ (for $B_{\mathbb T}$, p. 372).

Here $\mathrm{ord}_\mathfrak p N$ is `DVR.levelExp` of the base change (`levelExpP`, `NF.levelExp`), $e = \mathrm{ord}_\mathfrak p 2$ (`ordTwoP`,
`NF.ordTwo`) and $K_0 = \mathrm{ord}_\mathfrak p N + 2e + 1$ (`depthLevelP`, `NF.depthLevel`).

**Depends on** `DVRDepth.lean`, `BridgeExplicit.lean`, `NFLocalGeneral.lean`.
-/
import QuadFormsKB.LocalDensity.DVRDepth
import QuadFormsKB.LocalDensity.BridgeExplicit
import QuadFormsKB.LocalDensity.NFLocalGeneral

set_option linter.unusedSectionVars false

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-! ### Over $\mathbb{Q}$ -/

section Rat

/-- $e = \mathrm{ord}_p 2$: $1$ for $p = 2$, else $0$. -/
abbrev ordTwoP (p : ℕ) : ℕ := if p = 2 then 1 else 0

theorem det_map_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] :
    (Q.map (Int.castRingHom ℤ_[p])).hessian.det = (Q.hessian.det : ℤ_[p]) := by
  have : (Q.map (Int.castRingHom ℤ_[p])).hessian = Q.hessian.map (Int.castRingHom ℤ_[p]) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]

theorem nondegenerate_map_padic {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime] :
    (Q.map (Int.castRingHom ℤ_[p])).Nondegenerate := by
  unfold QuadForm.Nondegenerate at hQ ⊢
  rw [det_map_padic]; exact_mod_cast hQ

/-- **$\mathrm{ord}_p N$** for an integral form: the level exponent of $Q \otimes \mathbb{Z}_p$ (Hanke 2004, p. 355). -/
noncomputable def levelExpP (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] : ℕ :=
  DVR.levelExp (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p])

/-- **$K_0 = \mathrm{ord}_p(4N) + 1$** for an integral form at $p$. -/
noncomputable def depthLevelP (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] : ℕ :=
  DVR.depthLevel (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) (ordTwoP p)

theorem padic_two_ne_zero (p : ℕ) [Fact p.Prime] : (2 : ℤ_[p]) ≠ 0 := two_ne_zero

/-- **Lemma 3.4 over $\mathbb{Q}$, uniform form** (Hanke 2004, p. 361): for $Q$ nondegenerate, every $m \in \mathbb{Z}$ and every
$k \ge \mathrm{ord}_p(4N) + 1$, $r^{\mathrm{Good}\cup\mathrm{Bad}}_{p^{k+1}}(m) = p^{n-1}r^{\mathrm{Good}\cup\mathrm{Bad}}_{p^k}(m)$. -/
@[kb "hanke2004" "Lemma 3.4, p. 361 (over Q)"]
theorem repCountOf_nonZero_succ_padic (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (m : ℤ) (k : ℕ) (hk : depthLevelP Q p ≤ k) :
    repCountOf Q p (k + 1) m (fun x => ¬ IsZeroType p (k + 1) x) =
      p ^ (n - 1) * repCountOf Q p k m (fun x => ¬ IsZeroType p k x) := by
  rw [repCountOf_nonZero_eq_padic, repCountOf_nonZero_eq_padic]
  have := DVR.repCountOf_nonZero_succ _ (nondegenerate_map_padic hQ p) _ PadicInt.irreducible_p
    (padic_two_ne_zero p) _ (padicInt_pow_dvd_two p) (m : ℤ_[p]) k hk
  rwa [q_padicInt] at this

/-- **Remark 3.5.1 over $\mathbb{Q}$** (Hanke 2004, p. 362, corrected): for $K \ge \mathrm{ord}_p(4N) + 1$, $m$ is locally represented at
$p$ iff $m = 0$ or $m = p^{2j}m'$ with $m'$ **primitively** represented mod $p^K$. -/
@[kb "hanke2004" "Remark 3.5.1, p. 362 (over Q)"]
theorem isLocallyRepresentedAt_iff_nonZero_padic (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ)
    [Fact p.Prime] {K : ℕ} (hK : depthLevelP Q p ≤ K) (m : ℤ) :
    IsLocallyRepresentedAt Q p m ↔
      m = 0 ∨ ∃ j m', m = (p : ℤ) ^ (2 * j) * m' ∧ 0 < repCountOf Q p K m' (fun x => ¬ IsZeroType p K x) := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := PadicInt.irreducible_p.ne_zero
  rw [isLocallyRepresentedAt_iff_padic, DVR.isLocallyRepresentedAt_iff_nonZero _ (nondegenerate_map_padic hQ p)
    _ PadicInt.irreducible_p (padic_two_ne_zero p) _ (padicInt_pow_dvd_two p) hK]
  constructor
  · rintro (h0 | ⟨j, m'', hj, hp⟩)
    · left; exact_mod_cast h0
    · right
      obtain ⟨m₀, rfl⟩ := (padic_pow_dvd_int_iff p (2 * j) m).1 ⟨m'', hj⟩
      refine ⟨j, m₀, rfl, ?_⟩
      rw [repCountOf_nonZero_eq_padic]
      have : (m₀ : ℤ_[p]) = m'' := by
        push_cast at hj
        exact mul_left_cancel₀ (pow_ne_zero _ hp0) hj
      rwa [this]
  · rintro (rfl | ⟨j, m', rfl, hp⟩)
    · left; simp
    · right
      exact ⟨j, (m' : ℤ_[p]), by push_cast; ring, by rwa [← repCountOf_nonZero_eq_padic]⟩

/-- **Remark 3.6.1 over $\mathbb{Q}$, every prime** (Hanke 2004, p. 362): a locally represented $m$ with
$p^{\mathrm{ord}_p N + 2e - 1} \mid m$ ($e = \mathrm{ord}_p 2$) is $p$-stable. -/
@[kb "hanke2004" "Remark 3.6.1, p. 362 (over Q)"]
theorem isPStable_of_dvd_padic (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (S₀ : Finset (Fin n)) (p : ℕ)
    [Fact p.Prime] {m : ℤ} (hm : (p : ℤ) ^ (levelExpP Q p + 2 * ordTwoP p - 1) ∣ m)
    (hloc : IsLocallyRepresentedAt Q p m) : IsPStable Q S₀ p m := by
  rw [isPStable_iff_padic]
  rw [isLocallyRepresentedAt_iff_padic] at hloc
  exact DVR.isPStable_of_dvd _ (nondegenerate_map_padic hQ p) _ PadicInt.irreducible_p (padic_two_ne_zero p)
    _ (padicInt_pow_dvd_two p) S₀ ((padic_pow_dvd_int_iff p _ m).2 hm) hloc

/-- **Remark 3.6.1 over $\mathbb{Q}$ as printed, $p$ odd**: every locally represented $m \in p^{\mathrm{ord}_p N}\mathbb{Z}$ is $p$-stable. -/
theorem isPStable_of_dvd_padic_odd (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (S₀ : Finset (Fin n)) (p : ℕ)
    [Fact p.Prime] (hp : p ≠ 2) {m : ℤ} (hm : (p : ℤ) ^ levelExpP Q p ∣ m)
    (hloc : IsLocallyRepresentedAt Q p m) : IsPStable Q S₀ p m := by
  refine isPStable_of_dvd_padic Q hQ S₀ p ((pow_dvd_pow _ ?_).trans hm) hloc
  simp [ordTwoP, hp]

/-- $p^{\mathrm{ord}_p(4N)} \mid 8\det H$ over $\mathbb{Z}$. -/
theorem pow_levelExpP_dvd (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime] :
    (p : ℤ) ^ (levelExpP Q p + 2 * ordTwoP p) ∣ 8 * Q.hessian.det := by
  rw [← padic_pow_dvd_int_iff]
  have h := DVR.pow_levelExp_add_dvd (nondegenerate_map_padic hQ p) PadicInt.irreducible_p
    (padic_two_ne_zero p) (padicInt_pow_dvd_two p)
  rw [det_map_padic] at h
  rw [Int.cast_mul, Int.cast_ofNat]
  exact h

/-- **A stable ideal over $\mathbb{Q}$** (Hanke 2004, Remark 3.6.1 and p. 372): every $m \in 8\det(H)\mathbb{Z}$ that is locally
represented at $p$ is $p$-stable, at every prime $p$. (The paper's stable ideal is $N\mathbb{Z}$; $8\det H$ is a multiple of $4N$,
which this proof needs at $p = 2$.) -/
@[kb "hanke2004" "Remark 3.6.1, p. 362 (stable ideal over Q)"]
theorem isStable_of_dvd_padic (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (S₀ : Finset (Fin n)) (p : ℕ)
    [Fact p.Prime] {m : ℤ} (hm : 8 * Q.hessian.det ∣ m) (hloc : IsLocallyRepresentedAt Q p m) :
    IsPStable Q S₀ p m :=
  isPStable_of_dvd_padic Q hQ S₀ p ((pow_dvd_pow _ (by omega)).trans ((pow_levelExpP_dvd Q hQ p).trans hm))
    hloc

/-- **Deep square classes over $\mathbb{Q}$**: if $p^{\mathrm{ord}_p(4N)+1} \mid m$, then $p^{2\nu}m$ is locally represented at $p$ iff $m$ is. -/
theorem isLocallyRepresentedAt_pow_mul_iff_padic (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ)
    [Fact p.Prime] {m : ℤ} (hm : (p : ℤ) ^ depthLevelP Q p ∣ m) (ν : ℕ) :
    IsLocallyRepresentedAt Q p ((p : ℤ) ^ (2 * ν) * m) ↔ IsLocallyRepresentedAt Q p m := by
  rw [isLocallyRepresentedAt_iff_padic, isLocallyRepresentedAt_iff_padic]
  push_cast
  exact DVR.isLocallyRepresentedAt_pow_mul_iff _ (nondegenerate_map_padic hQ p) _ PadicInt.irreducible_p
    (padic_two_ne_zero p) _ (padicInt_pow_dvd_two p) ((padic_pow_dvd_int_iff p _ m).2 hm) ν

/-- **Local constancy of $\beta_p$ and $C'_p$ over $\mathbb{Q}$** (behind the finiteness of $B_{\mathbb T}$, p. 372): if
$p^{a+1} \nmid m$ and $m \equiv m' \pmod{p^{a + K_0}}$, then $\beta_p(m) = \beta_p(m')$ and $C'_p(m) = C'_p(m')$. -/
@[kb "hanke2004" "p. 372 (local constancy, over Q)"]
theorem localDensity_congr_padic (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime] {a : ℕ}
    {m m' : ℤ} (ha : ¬ (p : ℤ) ^ (a + 1) ∣ m) (h : (p : ℤ) ^ (a + depthLevelP Q p) ∣ m - m') :
    localDensity Q p m = localDensity Q p m' ∧ localConstC' Q p m = localConstC' Q p m' := by
  have ha' : ¬ (p : ℤ_[p]) ^ (a + 1) ∣ (m : ℤ_[p]) := by rwa [padic_pow_dvd_int_iff]
  have h' : (p : ℤ_[p]) ^ (a + DVR.depthLevel (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) (ordTwoP p)) ∣
      (m : ℤ_[p]) - (m' : ℤ_[p]) := by
    rw [← Int.cast_sub, padic_pow_dvd_int_iff]; exact h
  have hD := DVR.localDensity_congr _ (nondegenerate_map_padic hQ p) _ PadicInt.irreducible_p
    (padic_two_ne_zero p) _ (padicInt_pow_dvd_two p) ha' h'
  have hC := (DVR.localConstC_congr _ (nondegenerate_map_padic hQ p) _ PadicInt.irreducible_p
    (padic_two_ne_zero p) _ (padicInt_pow_dvd_two p) ha' h').1
  refine ⟨by rw [localDensity_eq_padic, localDensity_eq_padic, hD], ?_⟩
  unfold localConstC'
  rw [localConstC_eq_padic, localConstC_eq_padic, hC]

end Rat

/-! ### Over a number field $F$ -/

namespace NF

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "𝔬" => v.adicCompletionIntegers F

/-- **$e = \mathrm{ord}_\mathfrak p 2$**, the ramification index of $2$ at $\mathfrak p$ ($0$ for $\mathfrak p \nmid 2$). -/
noncomputable def ordTwo : ℕ :=
  Classical.choose (DVR.exists_pow_dvd_not_dvd (π v) (irreducible_π v) (two_ne_zero' v))

theorem ordTwo_spec : π v ^ ordTwo v ∣ 2 ∧ ¬ π v ^ (ordTwo v + 1) ∣ 2 :=
  Classical.choose_spec (DVR.exists_pow_dvd_not_dvd (π v) (irreducible_π v) (two_ne_zero' v))

theorem ordTwo_eq_zero (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : ordTwo v = 0 := by
  by_contra h
  exact π_not_dvd_two v h2 ((dvd_pow_self _ h).trans (ordTwo_spec v).1)

/-- **$\mathrm{ord}_\mathfrak p N$** for $Q$ over $\mathcal O_F$: the level exponent of $Q \otimes \mathfrak o_\mathfrak p$ (Hanke 2004, p. 355). -/
noncomputable def levelExp (Q : QuadForm (𝓞 F) n) : ℕ := DVR.levelExp (Qp v Q) (π v)

/-- **$K_0 = \mathrm{ord}_\mathfrak p(4N) + 1$** for $Q$ over $\mathcal O_F$ at $\mathfrak p$. -/
noncomputable def depthLevel (Q : QuadForm (𝓞 F) n) : ℕ := DVR.depthLevel (Qp v Q) (π v) (ordTwo v)

/-- **Lemma 3.4 over $F$, uniform form** (Hanke 2004, p. 361; every $\mathfrak p$): for every $m \in \mathcal O_F$ and
$k \ge \mathrm{ord}_\mathfrak p(4N) + 1$, $r^{\mathrm{Good}\cup\mathrm{Bad}}_{\mathfrak p^{k+1}}(m) = (N\mathfrak p)^{n-1}r^{\mathrm{Good}\cup\mathrm{Bad}}_{\mathfrak p^k}(m)$. -/
@[kb "hanke2004" "Lemma 3.4, p. 361 (over F)"]
theorem repCountNonZero_succ (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (m : 𝓞 F) (k : ℕ)
    (hk : depthLevel v Q ≤ k) :
    repCountOf v Q (k + 1) m (fun x => ¬ IsZeroType v (k + 1) x) =
      Ideal.absNorm v.asIdeal ^ (n - 1) * repCountOf v Q k m (fun x => ¬ IsZeroType v k x) := by
  rw [repCountNonZero_eq_completion, repCountNonZero_eq_completion, ← q_completion]
  exact DVR.repCountOf_nonZero_succ _ (nondegenerate_Qp v hQ) _ (irreducible_π v) (two_ne_zero' v) _
    (ordTwo_spec v) _ k hk

/-- **Remark 3.5.1 over $F$** (Hanke 2004, p. 362, corrected): for $K \ge \mathrm{ord}_\mathfrak p(4N) + 1$, $m \in \mathcal O_F$ is locally
represented at $\mathfrak p$ iff $m = 0$ or, for some $j$ and $m' \in \mathcal O_F$, $m \equiv \varpi^{2j}m' \pmod{\mathfrak p^{2j+K}}$ and $m'$ is
**primitively** represented mod $\mathfrak p^K$ ($\varpi$ = `unif v`; the congruence replaces $m = \varpi^{2j}m'$, since $m/\varpi^{2j}$
need not lie in $\mathcal O_F$). -/
@[kb "hanke2004" "Remark 3.5.1, p. 362 (over F)"]
theorem isLocallyRepresentedAt_iff_nonZero (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {K : ℕ}
    (hK : depthLevel v Q ≤ K) (m : 𝓞 F) :
    IsLocallyRepresentedAt v Q m ↔
      m = 0 ∨ ∃ j, ∃ m' : 𝓞 F, m - unif v ^ (2 * j) * m' ∈ v.asIdeal ^ (2 * j + K) ∧
        0 < repCountOf v Q K m' (fun x => ¬ IsZeroType v K x) := by
  rw [isLocallyRepresentedAt_iff, DVR.isLocallyRepresentedAt_iff_nonZero _ (nondegenerate_Qp v hQ) _
    (irreducible_π v) (two_ne_zero' v) _ (ordTwo_spec v) hK]
  constructor
  · rintro (h0 | ⟨j, m'', hj, hp⟩)
    · left
      exact (injective_iff_map_eq_zero _).mp (ι_injective v) _ h0
    · right
      obtain ⟨m', hm'⟩ := redHom_surjective v K (Ideal.Quotient.mk _ m'')
      have hd : π v ^ K ∣ ι v m' - m'' := (DVR.mk_eq_mk_iff _ K _ _).1 hm'
      refine ⟨j, m', ?_, ?_⟩
      · rw [← π_pow_dvd_ι_iff, map_sub, map_mul, map_pow, hj, pow_add,
          show π v ^ (2 * j) * m'' - ι v (unif v) ^ (2 * j) * ι v m' =
            π v ^ (2 * j) * -(ι v m' - m'') by ring]
        exact mul_dvd_mul_left _ ((dvd_neg).2 hd)
      · rw [repCountNonZero_eq_completion, DVR.repCountOf_congr_mod _ _ K hd]; exact hp
  · rintro (rfl | ⟨j, m', hj, hp⟩)
    · left; simp
    · right
      rw [← π_pow_dvd_ι_iff, map_sub, map_mul, map_pow] at hj
      obtain ⟨t, ht⟩ := hj
      refine ⟨j, ι v m' + π v ^ K * t, ?_, ?_⟩
      · rw [mul_add, ← mul_assoc, ← pow_add, ← ht]; ring
      · rw [repCountNonZero_eq_completion] at hp
        rwa [DVR.repCountOf_congr_mod _ _ K (show π v ^ K ∣ ι v m' + π v ^ K * t - ι v m' by
          rw [add_sub_cancel_left]; exact dvd_mul_right _ _)]

/-- **Remark 3.6.1 over $F$, every prime** (Hanke 2004, p. 362): a locally represented $m \in \mathfrak p^{\mathrm{ord}_\mathfrak p N + 2e - 1}$
($e = \mathrm{ord}_\mathfrak p 2$) is $\mathfrak p$-stable. -/
@[kb "hanke2004" "Remark 3.6.1, p. 362 (over F)"]
theorem isPStable_of_mem (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {m : 𝓞 F}
    (hm : m ∈ v.asIdeal ^ (levelExp v Q + 2 * ordTwo v - 1)) (hloc : IsLocallyRepresentedAt v Q m) :
    IsPStable v Q m := by
  rw [isPStable_iff v Q ∅]
  rw [isLocallyRepresentedAt_iff] at hloc
  exact DVR.isPStable_of_dvd _ (nondegenerate_Qp v hQ) _ (irreducible_π v) (two_ne_zero' v) _ (ordTwo_spec v)
    ∅ ((π_pow_dvd_ι_iff v _ m).2 hm) hloc

/-- **Remark 3.6.1 over $F$ as printed, at $\mathfrak p \nmid 2$**: every locally represented $m \in \mathfrak s_\mathfrak p = \mathfrak p^{\mathrm{ord}_\mathfrak p N}$
is $\mathfrak p$-stable. -/
theorem isPStable_of_mem_nondyadic (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate)
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {m : 𝓞 F} (hm : m ∈ v.asIdeal ^ levelExp v Q)
    (hloc : IsLocallyRepresentedAt v Q m) : IsPStable v Q m := by
  refine isPStable_of_mem v Q hQ (Ideal.pow_le_pow_right ?_ hm) hloc
  rw [ordTwo_eq_zero v h2]; omega

/-- $\mathfrak p^{\mathrm{ord}_\mathfrak p(4N)} \supseteq 8\det(H)\mathcal O_F$. -/
theorem mem_pow_levelExp_of_dvd (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {m : 𝓞 F}
    (hm : 8 * Q.hessian.det ∣ m) : m ∈ v.asIdeal ^ (levelExp v Q + 2 * ordTwo v) := by
  rw [← π_pow_dvd_ι_iff]
  have h := DVR.pow_levelExp_add_dvd (nondegenerate_Qp v hQ) (irreducible_π v) (two_ne_zero' v)
    (ordTwo_spec v)
  rw [det_hessian_Qp, show (8 : 𝔬) = ι v 8 from (map_ofNat _ 8).symm, ← map_mul] at h
  exact h.trans (map_dvd _ hm)

/-- **A stable ideal over $F$** (Hanke 2004, Remark 3.6.1 and p. 372): every $m \in 8\det(H)\mathcal O_F$ that is locally represented
at $\mathfrak p$ is $\mathfrak p$-stable, at every prime $\mathfrak p$ (dyadic or not). The paper's stable ideal is $\mathfrak s = N\mathcal O_F$
(proved here at $\mathfrak p \nmid 2$: `isPStable_of_mem_nondyadic`); $8\det H \in 4N$ is what this proof needs at dyadic $\mathfrak p$. -/
@[kb "hanke2004" "Remark 3.6.1, p. 362 (stable ideal over F)"]
theorem isStable_of_dvd (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {m : 𝓞 F}
    (hm : 8 * Q.hessian.det ∣ m) (hloc : IsLocallyRepresentedAt v Q m) : IsPStable v Q m :=
  isPStable_of_mem v Q hQ (Ideal.pow_le_pow_right (by omega) (mem_pow_levelExp_of_dvd v Q hQ hm)) hloc

/-- **Deep square classes over $F$**: if $m \in \mathfrak p^{K_0}$, then $\varpi^{2\nu}m$ is locally represented at $\mathfrak p$ iff $m$ is. -/
theorem isLocallyRepresentedAt_pow_mul_iff (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {m : 𝓞 F}
    (hm : m ∈ v.asIdeal ^ depthLevel v Q) (ν : ℕ) :
    IsLocallyRepresentedAt v Q (unif v ^ (2 * ν) * m) ↔ IsLocallyRepresentedAt v Q m := by
  rw [isLocallyRepresentedAt_iff, isLocallyRepresentedAt_iff, map_mul, map_pow]
  exact DVR.isLocallyRepresentedAt_pow_mul_iff _ (nondegenerate_Qp v hQ) _ (irreducible_π v) (two_ne_zero' v)
    _ (ordTwo_spec v) ((π_pow_dvd_ι_iff v _ m).2 hm) ν

/-- **Local constancy of $\beta_\mathfrak p$ and $C'_\mathfrak p$ over $F$** (behind the finiteness of $B_{\mathbb T}$, Hanke 2004,
p. 372): if $m \notin \mathfrak p^{a+1}$ and $m \equiv m' \pmod{\mathfrak p^{a + K_0}}$, then $\beta_\mathfrak p(m) = \beta_\mathfrak p(m')$ and
$C'_\mathfrak p(m) = C'_\mathfrak p(m')$. -/
@[kb "hanke2004" "p. 372 (local constancy, over F)"]
theorem localDensity_congr (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {a : ℕ} {m m' : 𝓞 F}
    (ha : m ∉ v.asIdeal ^ (a + 1)) (h : m - m' ∈ v.asIdeal ^ (a + depthLevel v Q)) :
    localDensity v Q m = localDensity v Q m' ∧ localConstC' v Q m = localConstC' v Q m' := by
  have ha' : ¬ π v ^ (a + 1) ∣ ι v m := by rwa [π_pow_dvd_ι_iff]
  have h' : π v ^ (a + DVR.depthLevel (Qp v Q) (π v) (ordTwo v)) ∣ ι v m - ι v m' := by
    rw [← map_sub, π_pow_dvd_ι_iff]; exact h
  have hD := DVR.localDensity_congr _ (nondegenerate_Qp v hQ) _ (irreducible_π v) (two_ne_zero' v) _
    (ordTwo_spec v) ha' h'
  have hC := (DVR.localConstC_congr _ (nondegenerate_Qp v hQ) _ (irreducible_π v) (two_ne_zero' v) _
    (ordTwo_spec v) ha' h').2
  exact ⟨by rw [localDensity_eq_completion, localDensity_eq_completion, hD],
    by rw [localConstC'_eq_completion, localConstC'_eq_completion, hC]⟩

end NF

end QuadFormsKB.LocalDensity
