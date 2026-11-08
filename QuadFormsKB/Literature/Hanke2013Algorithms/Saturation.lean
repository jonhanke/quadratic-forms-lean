/-
# Hanke 2013, §3.1: saturated discriminant modules

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`).

Setting as in `Duality.lean`: $R$ is a Dedekind domain with fraction field $F$, $2 \in F^\times$, and the bilinear
space $(V, B)$ is encoded by $Q = Q_B$.

**Proves** Lemma **3.5** (scaled duals of modular lattices; for general fractional ideals and for integer powers of a
prime), a corrected form of Theorem **3.7** (see below), and the correctness and termination of Algorithm **3.8**
(every $\mathfrak a$-valued lattice lies in an $\mathfrak a$-saturated one).

**Defines** the maximal scale index (Definition **3.6**) and $\mathfrak a$-saturated lattices (Definition **3.1**).

*Deviation (Definition 3.6):* the paper defines $m_{\mathfrak p,\mathfrak a}$ through a Jordan decomposition of
$L_{\mathfrak p}$. Here it is the exponent of $\mathfrak p$ in the annihilator ideal
$\operatorname{Ann}_R D_{\mathfrak a}(L)$. The two agree: if $L_{\mathfrak p} = \bigoplus_i L_i$ with $L_i$
$\mathfrak a\mathfrak p^i$-modular, then $(D_{\mathfrak a})_{\mathfrak p} \cong \bigoplus_i (L_i/\mathfrak p^iL_i)$,
whose annihilator is $\mathfrak p^{\max\{i : L_i \ne 0\}}$ (proved in `Algorithm32.lean`,
`maxScaleIndex_eq_of_split`). With this definition no Jordan decomposition is needed: the whole section is proved globally.

*Erratum (Theorem 3.7):* with a single prime, $L' = L + \mathfrak p^\lambda L^{\#\mathfrak a}$ is in general **not**
$\mathfrak a$-valued, because at every prime $\mathfrak q \ne \mathfrak p$ the ideal $\mathfrak p^\lambda$ is a unit,
so $L'_{\mathfrak q} = L^{\#\mathfrak a}_{\mathfrak q}$. Example over $\mathbb Z$ with $\mathfrak a = \mathbb Z$:
$B = \operatorname{diag}(4, 3)$, $\mathfrak p = 2$, $m_{2} = 2$, $\lambda = 1$; then $L' \ni \frac13 e_2$ and
$B(\frac13e_2, \frac13e_2) = \frac13 \notin \mathbb Z$. Also the new index is $m' \le \lambda$, not $= \lambda$
(e.g. for $B = \operatorname{diag}(4)$ on $L = \mathbb Ze_1$: $m = 2$, $\lambda = 1$, $L' = L + 2L^\# =
\mathbb Z\frac12e_1$ is unimodular, so $m' = 0$).
The correct statement (`theorem_3_7`) uses an ideal $\mathfrak l$ with $\mathfrak l^2 \subseteq
\operatorname{Ann}D_{\mathfrak a}(L)$ and $\mathfrak p$-exponent $\lambda$, as Algorithm 3.8 does
($\mathfrak l = \prod_{\mathfrak q}\mathfrak q^{\lceil m_{\mathfrak q}/2\rceil}$).
-/
import QuadFormsKB.Literature.Hanke2013Algorithms.Uniqueness
import QuadFormsKB.Citation

open QuadraticMap Submodule Module
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.OMeara

section Lemma35

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Lemma 3.5, for general fractional ideals** (Hanke 2013, p. 8): if $M$ is $\mathfrak a\mathfrak c$-modular,
then $M' := \mathfrak a\mathfrak b M^\#$ is $\mathfrak a\mathfrak b^2\mathfrak c^{-1}$-modular, and (for $V \ne 0$)
$M'$ is $\mathfrak a$-valued if and only if $\mathfrak b^2 \subseteq \mathfrak c$. Here $\mathfrak a, \mathfrak b,
\mathfrak c$ are non-zero fractional ideals and $M$ is a lattice in a non-degenerate space. (The paper's case is
$\mathfrak c = \mathfrak p^i$, $\mathfrak b = \mathfrak p^\lambda$: `lemma_3_5`.) -/
@[kb "hanke2013algorithms" "Lemma 3.5, p. 8 (general fractional ideals)"]
theorem lemma_3_5_general [Nontrivial V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    {a b c : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) (hb : b.FG) (hb0 : b ≠ ⊥) (hc : c.FG) (hc0 : c ≠ ⊥)
    {M : Submodule R V} (hM : M.IsLattice F) (hmod : IsAModular Q (a * c) M) :
    IsAModular Q (a * b ^ 2 * (1 / c)) ((a * b) • dual Q M) ∧
      (IsAValued Q a ((a * b) • dual Q M) ↔ b ^ 2 ≤ c) := by
  obtain ⟨hic, hic0⟩ := one_div_fg hc hc0
  have hac : (a * c).FG := ha.mul hc
  have hac0 : a * c ≠ ⊥ := mul_ne_bot' ha0 hc0
  obtain ⟨hiac, hiac0⟩ := one_div_fg hac hac0
  have hca := mul_one_div_cancel_of_fg hc hc0
  have haca := mul_one_div_cancel_of_fg hac hac0
  have haa := mul_one_div_cancel_of_fg ha ha0
  -- $M' = \mathfrak b\mathfrak c^{-1} M$
  have hb' : (b * (1 / c)).FG := hb.mul hic
  have hb'0 : b * (1 / c) ≠ ⊥ := mul_ne_bot' hb0 hic0
  have hdual := (isAModular_iff_dual_eq Q hac hac0 hM).1 hmod
  have hkey : a * b * (1 / (a * c)) = b * (1 / c) := by
    calc a * b * (1 / (a * c)) = a * b * (1 / (a * c)) * (c * (1 / c)) := by rw [hca, mul_one]
      _ = b * (1 / c) * (a * c * (1 / (a * c))) := by ring
      _ = b * (1 / c) := by rw [haca, mul_one]
  have hM' : (a * b) • dual Q M = (b * (1 / c)) • M := by
    rw [hdual, ← mul_smul_submodule, hkey]
  have hmod' := lemma_2_7 Q hV hac hac0 hb' hb'0 hM hmod
  have hval : (b * (1 / c)) ^ 2 * (a * c) = a * b ^ 2 * (1 / c) := by
    calc (b * (1 / c)) ^ 2 * (a * c) = a * b ^ 2 * (1 / c) * (c * (1 / c)) := by ring
      _ = a * b ^ 2 * (1 / c) := by rw [hca, mul_one]
  rw [hval] at hmod'
  rw [hM']
  refine ⟨hmod', ?_⟩
  have hlat := isLattice_smul_max hb' hb'0 hM
  have habc : (a * b ^ 2 * (1 / c)).FG := ((ha.mul (hb.pow 2))).mul hic
  have habc0 : a * b ^ 2 * (1 / c) ≠ ⊥ :=
    mul_ne_bot' (mul_ne_bot' ha0 (pow_fg_ne_bot hb hb0 2).2) hic0
  rw [IsAValued, lemma_2_6 Q hV habc habc0 hlat hmod']
  constructor
  · intro h
    calc b ^ 2 = (a * (1 / a)) * (b ^ 2 * (1 / c)) * c := by rw [haa, one_mul, mul_assoc, mul_comm (1 / c),
            hca, mul_one]
      _ = (1 / a) * (a * b ^ 2 * (1 / c)) * c := by ring
      _ ≤ (1 / a) * a * c := mul_le_mul' (mul_le_mul' le_rfl h) le_rfl
      _ = c := by rw [mul_comm (1 / a), haa, one_mul]
  · intro h
    calc a * b ^ 2 * (1 / c) ≤ a * c * (1 / c) := mul_le_mul' (mul_le_mul' le_rfl h) le_rfl
      _ = a := by rw [mul_assoc, hca, mul_one]

/-- The fractional ideal $\mathfrak p^k$ ($k \in \mathbb Z$) of an ideal $\mathfrak p$ of $R$, as an $R$-submodule
of $F$. -/
def idealZPow (p : Ideal R) (k : ℤ) : Submodule R F :=
  (((p : FractionalIdeal R⁰ F) ^ k : FractionalIdeal R⁰ F) : Submodule R F)

variable {p : Ideal R}

theorem idealZPow_ne_zero (hp0 : p ≠ ⊥) (k : ℤ) : ((p : FractionalIdeal R⁰ F) ^ k) ≠ 0 :=
  zpow_ne_zero k (FractionalIdeal.coeIdeal_ne_zero.2 hp0)

theorem idealZPow_fg (hp0 : p ≠ ⊥) (k : ℤ) : (idealZPow (F := F) p k).FG :=
  FractionalIdeal.fg_of_isUnit _ (idealZPow_ne_zero hp0 k).isUnit

theorem idealZPow_ne_bot (hp0 : p ≠ ⊥) (k : ℤ) : idealZPow (F := F) p k ≠ ⊥ :=
  FractionalIdeal.coeToSubmodule_ne_bot.2 (idealZPow_ne_zero hp0 k)

theorem idealZPow_add (hp0 : p ≠ ⊥) (j k : ℤ) :
    idealZPow (F := F) p (j + k) = idealZPow p j * idealZPow p k := by
  rw [idealZPow, zpow_add₀ (FractionalIdeal.coeIdeal_ne_zero.2 hp0), FractionalIdeal.coe_mul]; rfl

theorem idealZPow_zero : idealZPow (F := F) p 0 = 1 := by
  rw [idealZPow, zpow_zero, FractionalIdeal.coe_one]

theorem idealZPow_natCast (n : ℕ) : idealZPow (F := F) p n = ((p ^ n : Ideal R) : FractionalIdeal R⁰ F) := by
  rw [idealZPow, zpow_natCast, FractionalIdeal.coeIdeal_pow]

theorem one_div_idealZPow (hp0 : p ≠ ⊥) (k : ℤ) : 1 / idealZPow (F := F) p k = idealZPow p (-k) := by
  have h1 := mul_one_div_cancel_of_fg (idealZPow_fg (F := F) hp0 k) (idealZPow_ne_bot hp0 k)
  have h2 : idealZPow (F := F) p k * idealZPow p (-k) = 1 := by
    rw [← idealZPow_add hp0, add_neg_cancel, idealZPow_zero]
  calc 1 / idealZPow (F := F) p k = 1 / idealZPow p k * (idealZPow p k * idealZPow p (-k)) := by
        rw [h2, mul_one]
    _ = idealZPow p (-k) * (idealZPow p k * (1 / idealZPow p k)) := by ring
    _ = idealZPow p (-k) := by rw [h1, mul_one]

/-- For a prime $\mathfrak p \ne 0, R$: $\mathfrak p^k \subseteq \mathcal O_F$ if and only if $k \ge 0$. -/
theorem idealZPow_le_one_iff (hp0 : p ≠ ⊥) (hp1 : p ≠ ⊤) {k : ℤ} : idealZPow (F := F) p k ≤ 1 ↔ 0 ≤ k := by
  constructor
  · intro h
    by_contra hk
    push Not at hk
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    have hle : idealZPow (F := F) p (-1) ≤ 1 := by
      have : idealZPow (F := F) p (-1) = idealZPow p k * idealZPow p n := by
        rw [← idealZPow_add hp0]; congr 1; omega
      rw [this, idealZPow_natCast, ← mul_one (1 : Submodule R F)]
      exact mul_le_mul' h (by rw [← FractionalIdeal.coe_one]; exact FractionalIdeal.coe_le_coe.2 FractionalIdeal.coeIdeal_le_one)
    have h1 : (1 : Submodule R F) ≤ idealZPow p 1 := by
      calc (1 : Submodule R F) = idealZPow p 1 * idealZPow p (-1) := by
            rw [← idealZPow_add hp0]; simp [idealZPow_zero]
        _ ≤ idealZPow p 1 * 1 := mul_le_mul' le_rfl hle
        _ = idealZPow p 1 := mul_one _
    have h2 : ((⊤ : Ideal R) : FractionalIdeal R⁰ F) ≤ (p : FractionalIdeal R⁰ F) := by
      rw [FractionalIdeal.coeIdeal_top, ← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_one]
      simpa [idealZPow] using h1
    exact hp1 (top_le_iff.1 ((FractionalIdeal.coeIdeal_le_coeIdeal F).1 h2))
  · intro hk
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [idealZPow_natCast, ← FractionalIdeal.coe_one, FractionalIdeal.coe_le_coe]
    exact FractionalIdeal.coeIdeal_le_one

/-- For a prime $\mathfrak p \ne 0, R$: $\mathfrak p^j \subseteq \mathfrak p^i$ if and only if $i \le j$. -/
theorem idealZPow_le_iff (hp0 : p ≠ ⊥) (hp1 : p ≠ ⊤) {i j : ℤ} :
    idealZPow (F := F) p j ≤ idealZPow p i ↔ i ≤ j := by
  have hc := mul_one_div_cancel_of_fg (idealZPow_fg (F := F) hp0 i) (idealZPow_ne_bot hp0 i)
  rw [one_div_idealZPow hp0] at hc
  have hj : idealZPow (F := F) p j = idealZPow p (j - i) * idealZPow p i := by
    rw [← idealZPow_add hp0]; congr 1; omega
  rw [← sub_nonneg (a := j), ← idealZPow_le_one_iff (F := F) hp0 hp1]
  constructor
  · intro h
    calc idealZPow (F := F) p (j - i) = idealZPow p j * idealZPow p (-i) := by
          rw [hj, mul_assoc, hc, mul_one]
      _ ≤ idealZPow p i * idealZPow p (-i) := mul_le_mul' h le_rfl
      _ = 1 := hc
  · intro h
    rw [hj]
    calc idealZPow (F := F) p (j - i) * idealZPow p i ≤ 1 * idealZPow p i := mul_le_mul' h le_rfl
      _ = idealZPow p i := one_mul _

/-- **Lemma 3.5** (Hanke 2013, p. 8): if $M$ is $\mathfrak a\mathfrak p^i$-modular ($i \in \mathbb Z$), then for every
$\lambda \in \mathbb Z$ the scaled dual lattice $M' := \mathfrak a\mathfrak p^\lambda M^\#$ is
$\mathfrak a\mathfrak p^{2\lambda - i}$-modular, and $M'$ is $\mathfrak a$-valued if and only if
$\lambda \ge \lceil i/2\rceil$. Here $\mathfrak p$ is a non-zero prime ideal, $\mathfrak a$ a non-zero fractional
ideal, $M$ a lattice in a non-degenerate space $V \ne 0$ (for $V = 0$ the "only if" fails, as for Lemma 2.6). The
paper's proof (via $M^\# = \mathfrak a^{-1}\mathfrak p^{-i}M$ and Lemma 2.7) is `lemma_3_5_general`. -/
@[kb "hanke2013algorithms" "Lemma 3.5, p. 8"]
theorem lemma_3_5 [Nontrivial V] (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) (hp : p.IsMaximal) (hp0 : p ≠ ⊥) {i lam : ℤ} {M : Submodule R V}
    (hM : M.IsLattice F) (hmod : IsAModular Q (a * idealZPow p i) M) :
    IsAModular Q (a * idealZPow p (2 * lam - i)) ((a * idealZPow p lam) • dual Q M) ∧
      (IsAValued Q a ((a * idealZPow p lam) • dual Q M) ↔ ⌈(i : ℚ) / 2⌉ ≤ lam) := by
  obtain ⟨h1, h2⟩ := lemma_3_5_general Q hV ha ha0 (idealZPow_fg hp0 lam) (idealZPow_ne_bot hp0 lam)
    (idealZPow_fg hp0 i) (idealZPow_ne_bot hp0 i) hM hmod
  have hsq : idealZPow (F := F) p lam ^ 2 = idealZPow p (2 * lam) := by
    rw [_root_.sq, ← idealZPow_add hp0, two_mul]
  have he : a * idealZPow (F := F) p lam ^ 2 * (1 / idealZPow p i) = a * idealZPow p (2 * lam - i) := by
    rw [hsq, one_div_idealZPow hp0, mul_assoc, ← idealZPow_add hp0, sub_eq_add_neg]
  rw [he] at h1
  refine ⟨h1, h2.trans ?_⟩
  rw [hsq, idealZPow_le_iff hp0 hp.ne_top, Int.ceil_le]
  constructor
  · intro h; have : (i : ℚ) ≤ 2 * lam := by exact_mod_cast h
    linarith
  · intro h; have : (i : ℚ) ≤ 2 * lam := by linarith
    exact_mod_cast this

end Lemma35

section LocalAnn

variable {R : Type*} [CommRing R] {D : Type*} [AddCommGroup D] [Module R D]

/-- A finite family of elements each killed by some element outside $\mathfrak p$ is killed by one such element. -/
theorem exists_notMem_smul_eq_zero_finset {p : Ideal R} [p.IsPrime] (S : Finset D)
    (h : ∀ x ∈ S, ∃ u ∉ p, u • x = 0) : ∃ u ∉ p, ∀ x ∈ S, u • x = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun h1 => (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 h1), by simp⟩
  | insert y S hy ih =>
    obtain ⟨u, hu, hS⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    obtain ⟨v, hv, hvy⟩ := h y (Finset.mem_insert_self _ _)
    refine ⟨u * v, fun huv => (Ideal.IsPrime.mem_or_mem ‹_› huv).elim hu hv, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [mul_smul, hvy, smul_zero]
    · rw [mul_comm, mul_smul, hS x hx, smul_zero]

/-- **The local annihilation condition of Definition 3.1, globally**: for a finitely generated module $D$ over a
Noetherian ring and a prime $\mathfrak p$, the localization $D_{\mathfrak p}$ is annihilated by $\mathfrak p$ if and
only if $s\mathfrak p \subseteq \operatorname{Ann}D$ for some $s \notin \mathfrak p$. -/
theorem localization_annihilated_iff [IsNoetherianRing R] [Module.Finite R D] {p : Ideal R} [p.IsPrime] :
    (∀ r ∈ p, ∀ x : LocalizedModule p.primeCompl D, r • x = 0) ↔
      ∃ s ∉ p, ∀ r ∈ p, s * r ∈ Module.annihilator R D := by
  classical
  constructor
  · intro h
    obtain ⟨T, hT⟩ := (IsNoetherian.noetherian p : (p : Submodule R R).FG)
    obtain ⟨G, hG⟩ := (Module.Finite.fg_top : (⊤ : Submodule R D).FG)
    have hTp : ∀ t ∈ T, t ∈ p := fun t ht => hT ▸ Submodule.subset_span ht
    have hloc : ∀ x ∈ (T ×ˢ G).image (fun z => z.1 • z.2), ∃ u ∉ p, u • x = 0 := by
      intro x hx
      obtain ⟨⟨r, g⟩, hz, rfl⟩ := Finset.mem_image.1 hx
      have h0 := h r (hTp r (Finset.mem_product.1 hz).1) (LocalizedModule.mk g 1)
      rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk (1 : p.primeCompl),
        LocalizedModule.mk_eq] at h0
      obtain ⟨u, hu⟩ := h0
      exact ⟨u, u.2, by simpa [Submonoid.smul_def] using hu⟩
    obtain ⟨s, hs, hsT⟩ := exists_notMem_smul_eq_zero_finset _ hloc
    refine ⟨s, hs, fun r hr => ?_⟩
    rw [Module.mem_annihilator]
    intro x
    have hx : x ∈ Submodule.span R (G : Set D) := by rw [hG]; trivial
    have hr' : r ∈ Submodule.span R (T : Set R) := by rw [hT]; exact hr
    clear hr
    induction hx using Submodule.span_induction with
    | mem g hg =>
      induction hr' using Submodule.span_induction with
      | mem t ht =>
        rw [mul_smul]
        exact hsT _ (Finset.mem_image.2 ⟨⟨t, g⟩, Finset.mem_product.2 ⟨ht, hg⟩, rfl⟩)
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add, add_smul, hy, hz, add_zero]
      | smul c y _ hy => rw [smul_eq_mul, mul_left_comm, mul_smul, hy, smul_zero]
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_comm, hy, smul_zero]
  · rintro ⟨s, hs, hsr⟩ r hr x
    induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
      refine ⟨⟨s, hs⟩, ?_⟩
      have := (Module.mem_annihilator.1 (hsr r hr)) m
      simp only [smul_zero, Submonoid.smul_def]
      rw [smul_comm s (t : R), ← mul_smul s r m, this, smul_zero]

end LocalAnn

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- In a Dedekind domain, for a non-zero prime $\mathfrak p$ and an ideal $I$: $s\mathfrak p \subseteq I$ for some
$s \notin \mathfrak p$ if and only if $I \not\subseteq \mathfrak p^2$. -/
theorem exists_notMem_mul_le_iff {p : Ideal R} (_hp : p.IsPrime) (hp0 : p ≠ ⊥) (I : Ideal R) :
    (∃ s ∉ p, ∀ r ∈ p, s * r ∈ I) ↔ ¬ I ≤ p ^ 2 := by
  constructor
  · rintro ⟨s, hs, hsI⟩ hI
    apply hs
    have h1 : Ideal.span {s} * p ≤ p * p := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro r hr; rw [← _root_.sq]; exact hI (hsI r hr)
    rw [← Ideal.dvd_iff_le, mul_comm (Ideal.span {s})] at h1
    have h2 := (mul_dvd_mul_iff_left (show p ≠ 0 from hp0)).1 h1
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff] at h2
    exact h2
  · intro hI
    by_cases hIp : I ≤ p
    · obtain ⟨K, rfl⟩ := Ideal.dvd_iff_le.2 hIp
      have hK : ¬ K ≤ p := by
        intro hK; apply hI; rw [_root_.sq]; exact Ideal.mul_mono_right hK
      obtain ⟨s, hsK, hsp⟩ := Set.not_subset.1 hK
      exact ⟨s, hsp, fun r hr => by rw [mul_comm s r]; exact Ideal.mul_mem_mul hr hsK⟩
    · obtain ⟨s, hsI, hsp⟩ := Set.not_subset.1 hIp
      exact ⟨s, hsp, fun r _ => I.mul_mem_right r hsI⟩

end Dedekind

section Saturation

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- The annihilator ideal $\operatorname{Ann}_R D_{\mathfrak a}(L) = \{r \in R : rL^{\#\mathfrak a} \subseteq L\}$ of
the $\mathfrak a$-discriminant module (Hanke 2013, §3.1.2, p. 8: "the annihilator ideal of $D_{\mathfrak a}$"). -/
abbrev annD (a : Submodule R F) (L : Submodule R V) : Ideal R :=
  Module.annihilator R (DiscModule Q a L)

theorem mem_annD {a : Submodule R F} {L : Submodule R V} {r : R} :
    r ∈ annD Q a L ↔ ∀ x ∈ aDual Q a L, r • x ∈ L :=
  mem_annihilator_subQuot (M := L) (L := aDual Q a L)

/-- For a lattice $L$ in a non-degenerate space, $\operatorname{Ann}D_{\mathfrak a}(L) \ne 0$. -/
theorem annD_ne_bot (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) : annD Q a L ≠ ⊥ := by
  have hd := isLattice_aDual Q hV ha ha0 hL
  obtain ⟨c, hc0, hc⟩ := exists_smul_le_of_fg (F := F) hd.fg
    (by rw [hL.span_eq_top]; intro _ _; trivial)
  intro h
  have : c ∈ annD Q a L := (mem_annD Q).2 hc
  rw [h, Ideal.mem_bot] at this
  exact hc0 this

/-- **$\mathfrak a$-saturated lattice** (Hanke 2013, Definition 3.1, p. 7): an $\mathfrak a$-valued lattice $L$ such
that for every non-zero prime ideal $\mathfrak p$ of $R$ the local $\mathfrak a$-discriminant module
$(D_{\mathfrak a})_{\mathfrak p} = D_{\mathfrak a}(L) \otimes_R R_{\mathfrak p}$ (here the localized module
`LocalizedModule p.primeCompl`) is annihilated by $\mathfrak p$. -/
@[kb "hanke2013algorithms" "Definition 3.1, p. 7"]
def IsASaturated (a : Submodule R F) (L : Submodule R V) : Prop :=
  IsAValued Q a L ∧ ∀ (p : Ideal R) [p.IsPrime], p ≠ ⊥ →
    ∀ r ∈ p, ∀ x : LocalizedModule p.primeCompl (DiscModule Q a L), r • x = 0

/-- **Maximal scale index** $m_{\mathfrak p,\mathfrak a}(L)$ (Hanke 2013, Definition 3.6, p. 9): here the exponent
of $\mathfrak p$ in $\operatorname{Ann}_R D_{\mathfrak a}(L)$ (the largest $m$ with
$\operatorname{Ann}D_{\mathfrak a}(L) \subseteq \mathfrak p^m$). *Deviation:* the paper defines it as the largest $i$
with a non-zero $\mathfrak a\mathfrak p^i$-modular Jordan component of $L_{\mathfrak p}$; the two agree (see the module
docstring; proved: `maxScaleIndex_eq_of_split`, `Algorithm32.lean`). -/
@[kb "hanke2013algorithms" "Definition 3.6, p. 9 (maximal scale index, via the annihilator)"]
def maxScaleIndex (a : Submodule R F) (L : Submodule R V) (p : Ideal R) : ℕ :=
  multiplicity p (annD Q a L)

theorem finiteMultiplicity_annD (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) {p : Ideal R} (hp : p.IsPrime)
    (hp0 : p ≠ ⊥) : FiniteMultiplicity p (annD Q a L) :=
  FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hp0 hp) (annD_ne_bot Q hV ha ha0 hL)

/-- $m_{\mathfrak p,\mathfrak a}(L) \le 1$ if and only if $\operatorname{Ann}D_{\mathfrak a}(L) \not\subseteq
\mathfrak p^2$. -/
theorem maxScaleIndex_le_one_iff (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) {p : Ideal R} (hp : p.IsPrime)
    (hp0 : p ≠ ⊥) : maxScaleIndex Q a L p ≤ 1 ↔ ¬ annD Q a L ≤ p ^ 2 := by
  rw [maxScaleIndex, ← Nat.lt_succ_iff,
    (finiteMultiplicity_annD Q hV ha ha0 hL hp hp0).multiplicity_lt_iff_not_dvd, Ideal.dvd_iff_le]

/-- **Definition 3.1 in terms of Definition 3.6** (Hanke 2013, §3.1.2, p. 8: "repeating this process until the
annihilator of $D_{\mathfrak a}$ is a squarefree ideal"): an $\mathfrak a$-valued lattice $L$ in a non-degenerate
space is $\mathfrak a$-saturated if and only if $m_{\mathfrak p,\mathfrak a}(L) \le 1$ for every non-zero prime
$\mathfrak p$. -/
@[kb "hanke2013algorithms" "Definition 3.1, p. 7; §3.1.2, p. 8 (saturated iff the annihilator is squarefree)"]
theorem isASaturated_iff (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) :
    IsASaturated Q a L ↔ IsAValued Q a L ∧ ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → maxScaleIndex Q a L p ≤ 1 := by
  have hfin : Module.Finite R (DiscModule Q a L) := by
    have := (isLattice_aDual Q hV ha ha0 hL).fg
    have : Module.Finite R (aDual Q a L) := Module.Finite.iff_fg.2 this
    infer_instance
  unfold IsASaturated
  refine and_congr Iff.rfl (forall_congr' fun p => forall_congr' fun hp => forall_congr' fun hp0 => ?_)
  rw [localization_annihilated_iff, exists_notMem_mul_le_iff hp hp0,
    maxScaleIndex_le_one_iff Q hV ha ha0 hL hp hp0]

theorem le_aDual_comm {a : Submodule R F} {K N : Submodule R V} : K ≤ aDual Q a N ↔ N ≤ aDual Q a K := by
  constructor <;> intro h x hx y hy <;> rw [bil_comm] <;> exact h hy x hx

/-- The lattice $L + \mathfrak lL^{\#\mathfrak a}$ of Theorem 3.7 and Algorithm 3.8, step 3 (Hanke 2013, p. 9). -/
@[kb "hanke2013algorithms" "Theorem 3.7, p. 9; Algorithm 3.8, step 3 (L' = L + l L^{#a})"]
def satStep (a : Submodule R F) (L : Submodule R V) (l : Ideal R) : Submodule R V :=
  L ⊔ l • aDual Q a L

/-- **Theorem 3.7, the general step** (Hanke 2013, p. 9, corrected): for an $\mathfrak a$-valued lattice $L$ in a
non-degenerate space and an ideal $\mathfrak l$ with $\mathfrak l^2 \subseteq \operatorname{Ann}D_{\mathfrak a}(L)$
(i.e. $\mathfrak l^2L^{\#\mathfrak a} \subseteq L$), the lattice $L' := L + \mathfrak lL^{\#\mathfrak a}$ is an
$\mathfrak a$-valued lattice containing $L$, and $\mathfrak l \subseteq \operatorname{Ann}D_{\mathfrak a}(L')$; it is
a proper superlattice exactly when $\mathfrak l \not\subseteq \operatorname{Ann}D_{\mathfrak a}(L)$. -/
@[kb "hanke2013algorithms" "Theorem 3.7, p. 9 (corrected: the step L + l L^{#a} with l² ⊆ Ann D_a(L))"]
theorem theorem_3_7_step (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) (hval : IsAValued Q a L) {l : Ideal R}
    (hl : l ^ 2 ≤ annD Q a L) :
    (satStep Q a L l).IsLattice F ∧ IsAValued Q a (satStep Q a L l) ∧ L ≤ satStep Q a L l ∧
      l ≤ annD Q a (satStep Q a L l) ∧ (L < satStep Q a L l ↔ ¬ l ≤ annD Q a L) := by
  have hLd : L ≤ aDual Q a L := (lemma_2_2 Q).1 hval
  have hN : l • aDual Q a L ≤ aDual Q a L := Submodule.smul_le_right
  have hle : satStep Q a L l ≤ aDual Q a L := sup_le hLd hN
  have hlat : (satStep Q a L l).IsLattice F :=
    isLattice_of_le_of_le hL (isLattice_aDual Q hV ha ha0 hL) le_sup_left hle
  have hNN : l • aDual Q a L ≤ aDual Q a (l • aDual Q a L) := by
    rw [Submodule.smul_le]
    intro r hr v hv y hy
    refine Submodule.smul_induction_on hy (fun s hs w hw => ?_) (fun y1 y2 h1 h2 => ?_)
    · have hrs : r * s ∈ annD Q a L := hl (by rw [_root_.sq]; exact Ideal.mul_mem_mul hr hs)
      have h1 := (mem_annD Q).1 hrs v hv
      have h2 : bil Q ((r * s) • v) w ∈ a := by rw [bil_comm]; exact hw _ h1
      have h3 : bil Q (r • v) (s • w) = bil Q ((r * s) • v) w := by
        rw [bil_rsmul_left, bil_rsmul_right, bil_rsmul_left, map_mul]; ring
      rw [h3]; exact h2
    · rw [bil_add_right]; exact add_mem h1 h2
  have hval' : IsAValued Q a (satStep Q a L l) := by
    rw [lemma_2_2, satStep, aDual_sup]
    refine sup_le (le_inf hLd ?_) (le_inf ?_ hNN)
    · exact (le_aDual_comm Q).1 hN
    · exact hN
  have hann : l ≤ annD Q a (satStep Q a L l) := by
    intro r hr
    rw [mem_annD]
    intro v hv
    apply le_sup_left (b := l • aDual Q a L)
    rw [← lemma_2_4 Q hV ha ha0 hL]
    intro w hw
    rw [bil_rsmul_left, ← bil_rsmul_right]
    exact hv _ (le_sup_right (a := L) (Submodule.smul_mem_smul hr hw))
  refine ⟨hlat, hval', le_sup_left, hann, ?_⟩
  constructor
  · intro hlt hlA
    apply hlt.ne
    refine le_antisymm le_sup_left (sup_le le_rfl ?_)
    rw [Submodule.smul_le]
    intro r hr v hv
    exact (mem_annD Q).1 (hlA hr) v hv
  · intro hnot
    refine lt_of_le_of_ne le_sup_left fun heq => hnot fun r hr => (mem_annD Q).2 fun v hv => ?_
    rw [heq]
    exact le_sup_right (a := L) (Submodule.smul_mem_smul hr hv)

/-- **Theorem 3.7** (Hanke 2013, p. 9, corrected): let $L$ be an $\mathfrak a$-valued lattice in a non-degenerate
space with maximal scale index $m := m_{\mathfrak p,\mathfrak a}(L) \ge 2$ at a non-zero prime $\mathfrak p$, and
$\lambda := \lceil m/2\rceil = \lfloor (m+1)/2\rfloor$. Write $\operatorname{Ann}D_{\mathfrak a}(L) =
\mathfrak p^m\mathfrak c$ with $\mathfrak p \nmid \mathfrak c$ and put $\mathfrak l := \mathfrak p^\lambda\mathfrak c$
(so $\mathfrak l$ has $\mathfrak p$-exponent $\lambda$ and $\mathfrak l^2 \subseteq \operatorname{Ann}D_{\mathfrak
a}(L)$). Then $L' := L + \mathfrak lL^{\#\mathfrak a}$ is a proper $\mathfrak a$-valued superlattice of $L$ with
$m_{\mathfrak p,\mathfrak a}(L') \le \lambda < m$.

*Erratum:* the paper takes $\mathfrak l = \mathfrak p^\lambda$ and claims $m' = \lambda$. With
$\mathfrak l = \mathfrak p^\lambda$ the lattice $L'$ equals $L^{\#\mathfrak a}$ locally at every other prime, so it
is not $\mathfrak a$-valued unless $L$ is $\mathfrak a$-modular away from $\mathfrak p$ (example: $B =
\operatorname{diag}(4, 3)$ over $\mathbb Z$, $\mathfrak p = 2$); and $m' < \lambda$ happens when no Jordan component
has index exactly $\lambda$ (example: $B = \operatorname{diag}(4)$, $m' = 0$). The paper's Algorithm 3.8 uses the
correct $\mathfrak l = \prod_{\mathfrak q}\mathfrak q^{\lceil m_{\mathfrak q}/2\rceil}$. -/
@[kb "hanke2013algorithms" "Theorem 3.7, p. 9 (corrected)"]
theorem theorem_3_7 (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) (hval : IsAValued Q a L) {p : Ideal R}
    (hp : p.IsPrime) (hp0 : p ≠ ⊥) (hm : 2 ≤ maxScaleIndex Q a L p) :
    ∃ l : Ideal R, l ^ 2 ≤ annD Q a L ∧ multiplicity p l = (maxScaleIndex Q a L p + 1) / 2 ∧
      (satStep Q a L l).IsLattice F ∧ IsAValued Q a (satStep Q a L l) ∧ L < satStep Q a L l ∧
      maxScaleIndex Q a (satStep Q a L l) p ≤ (maxScaleIndex Q a L p + 1) / 2 ∧
      (maxScaleIndex Q a L p + 1) / 2 < maxScaleIndex Q a L p := by
  have hfin := finiteMultiplicity_annD Q hV ha ha0 hL hp hp0
  have hpr : Prime p := Ideal.prime_of_isPrime hp0 hp
  set m := maxScaleIndex Q a L p with hmdef
  set lam := (m + 1) / 2 with hlam
  obtain ⟨K, hK⟩ := pow_multiplicity_dvd p (annD Q a L)
  rw [← maxScaleIndex] at hK
  have hKp : ¬ p ∣ K := by
    rintro ⟨c, hc⟩
    apply hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self m)
    exact ⟨c, by rw [hK, hc, pow_succ, mul_assoc]⟩
  have hK0 : K ≠ 0 := by
    intro h; apply annD_ne_bot Q hV ha ha0 hL; rw [hK, h, mul_zero]; rfl
  have hpl0 : p ^ lam ≠ 0 := pow_ne_zero _ hp0
  have hl0 : p ^ lam * K ≠ 0 := mul_ne_zero hpl0 hK0
  have hl2 : (p ^ lam * K) ^ 2 ≤ annD Q a L := by
    rw [hK, mul_pow, ← pow_mul]
    exact Ideal.mul_mono (Ideal.pow_le_pow_right (by omega)) (Ideal.pow_le_self two_ne_zero)
  obtain ⟨hlat, hval', -, hann, hiff⟩ := theorem_3_7_step Q hV ha ha0 hL hval hl2
  refine ⟨p ^ lam * K, hl2, ?_, hlat, hval', hiff.2 ?_, ?_, by omega⟩
  · rw [multiplicity_mul hpr (FiniteMultiplicity.of_prime_left hpr hl0), multiplicity_pow_self_of_prime hpr,
      multiplicity_eq_zero_of_not_dvd hKp, add_zero]
  · intro hle
    rw [hK, ← Ideal.dvd_iff_le, mul_dvd_mul_iff_right hK0] at hle
    have h1 : p ^ lam * p ∣ p ^ lam * 1 := by
      rw [mul_one, ← pow_succ]; exact (pow_dvd_pow p (by omega)).trans hle
    exact hpr.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hpl0).1 h1))
  · have hfin' := finiteMultiplicity_annD Q hV ha ha0 hlat hp hp0
    rw [maxScaleIndex, ← Nat.lt_succ_iff, hfin'.multiplicity_lt_iff_not_dvd]
    intro hdvd
    have h1 := hdvd.trans (Ideal.dvd_iff_le.2 hann)
    rw [pow_succ] at h1
    exact hKp ((mul_dvd_mul_iff_left hpl0).1 h1)

/-- An $\mathfrak a$-maximal lattice is $\mathfrak a$-saturated (by `theorem_3_7`: otherwise
$L + \mathfrak lL^{\#\mathfrak a}$ is a proper $\mathfrak a$-valued superlattice). -/
theorem isASaturated_of_isAMaximal (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) (hmax : IsAMaximal Q a L) :
    IsASaturated Q a L := by
  rw [isASaturated_iff Q hV ha ha0 hL]
  refine ⟨hmax.1, fun p hp hp0 => ?_⟩
  by_contra h
  obtain ⟨l, -, -, -, hv', hlt, -⟩ := theorem_3_7 Q hV ha ha0 hL hmax.1 hp hp0 (by omega)
  exact hlt.ne (hmax.2 _ hlt.le hv').symm

/-- **Algorithm 3.8** (Hanke 2013, pp. 9–10), correctness and termination: every $\mathfrak a$-valued lattice $L$ in
a non-degenerate space lies in an $\mathfrak a$-saturated lattice $L' \supseteq L$. *Proof*: step 3 of the
algorithm replaces $L$ by the proper $\mathfrak a$-valued superlattice $L + \mathfrak lL^{\#\mathfrak a}$
(`theorem_3_7_step`, `theorem_3_7`) as long as $L$ is not saturated; all these lattices lie between $L$ and
$L^{\#\mathfrak a}$, a Noetherian module, so the iteration stops, at a saturated lattice. Formally: a maximal element
of the $\mathfrak a$-valued lattices containing $L$ exists (`exists_isAMaximal`) and is saturated
(`isASaturated_of_isAMaximal`). (Steps 1–2, choosing a lattice and scaling it to be $\mathfrak a$-valued: `algorithm_3_8_step1`,
`algorithm_3_8_step2`, `algorithm_3_8_exists`, in `Algorithm32.lean`.) -/
@[kb "hanke2013algorithms" "Algorithm 3.8, pp. 9-10 (an a-saturated superlattice exists)"]
theorem algorithm_3_8 (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) (hval : IsAValued Q a L) :
    ∃ L' : Submodule R V, L ≤ L' ∧ L'.IsLattice F ∧ IsASaturated Q a L' := by
  obtain ⟨L', hLL', hmax⟩ := exists_isAMaximal Q hV ha ha0 hL hval
  have hle : L' ≤ aDual Q a L := ((lemma_2_2 Q).1 hmax.1).trans (aDual_anti Q hLL')
  have hlat : L'.IsLattice F := isLattice_of_le_of_le hL (isLattice_aDual Q hV ha ha0 hL) hLL' hle
  exact ⟨L', hLL', hlat, isASaturated_of_isAMaximal Q hV ha ha0 hlat hmax⟩

end Saturation

end QuadFormsKB.Hanke2013Algorithms
