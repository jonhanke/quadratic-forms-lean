/-
# Local densities over $\mathbb{Q}$: counts mod $p^k$, solution types, $\beta_p(m)$

**Layer:** $\mathbb{Q}$ (integral forms `QuadForm ℤ n`, counts in $(\mathbb{Z}/p^k)^n$). **Defines** $r_{p^k}(m)$
(`repCount`, Hanke 2004, pp. 356–357), the Zero/Good/Bad types of Def. 3.1 (p. 358) relative to the unimodular
coordinates $S_0$ (`IsZeroType`, `IsGoodType`, `IsBadType`, `repCountOf`), and the local density
$\beta_p(m) = \lim_k r_{p^k}(m)/p^{k(n-1)}$ (`localDensity`, (5.1)–(5.2), p. 368, with the corrected exponent).
**Proves** the type decomposition (`repCount_eq_add_types`), Lemma 3.2 for diagonal forms (`repCountGood_add_diag`),
the map $\pi_Z$ (`repCountZero_eq`, p. 359) and corrected Remark 3.1.1 (`isGoodType_diag_iff_hessian`).
**Depends on** `QuadFormsKB.Defs.Integral` only. Indices are 0-based (`Fin n`).
-/
import Mathlib
import QuadFormsKB.Defs.Integral

namespace QuadFormsKB.LocalDensity

open QuadForm Matrix

variable {n : ℕ}

/-- **The number of solutions mod $p^k$:** $r_{p^k}(m)$ is the number of vectors
$\vec{x} = (x_0, \dots, x_{n-1}) \in (\mathbb{Z}/p^k\mathbb{Z})^n$ with $Q(\vec{x}) \equiv m \pmod{p^k}$
(Hanke 2004, $r_{\mathfrak{p}^k,Q}(m) = \#R_{\mathfrak{p}^k,Q}(m)$, pp. 356–357). Here $p$ is any natural
number; it is a prime in every result about it. -/
noncomputable def repCount (Q : QuadForm ℤ n) (p k : ℕ) (m : ℤ) : ℕ :=
  Nat.card {x : Fin n → ZMod (p ^ k) // Q.evalIn (ZMod (p ^ k)) x = (m : ZMod (p ^ k))}

/-- **Zero type** (Hanke 2004, Def. 3.1, p. 358): $\vec{x} \in (\mathbb{Z}/p^k\mathbb{Z})^n$ is of Zero type
if $\vec{x} \equiv \vec{0} \pmod p$, i.e. $p \mid x_i$ for every $i$. -/
def IsZeroType (p k : ℕ) (x : Fin n → ZMod (p ^ k)) : Prop :=
  ∀ i, (p : ZMod (p ^ k)) ∣ x i

/-- **Good type** (Hanke 2004, Def. 3.1, p. 358), relative to the set $S_0$ of **unimodular
coordinates** of a local Jordan splitting (2.3) of $Q$ at $p$ (the coordinates of the components with
$\nu_j = 0$): $\vec{x}$ is of Good type if it is **not** of Zero type and $x_i \not\equiv 0 \pmod p$ for
some $i \in S_0$. (Def. 3.1 asks that $\pi^{\nu_j}\vec{x}_j \not\equiv \vec{0} \pmod p$ for some component $j$;
this fails automatically when $\nu_j \ge 1$, so only the unimodular components matter.)

*Update*: The basis-free reformulation of Remark 3.1.1 is valid only for
odd $p$ (`isGoodType_diag_iff_hessian` below); at $p = 2$ no criterion in terms of $B$ and $Q \bmod 2$
alone reproduces Def. 3.1, so the type is defined from the Jordan splitting. -/
def IsGoodType (S₀ : Finset (Fin n)) (p k : ℕ) (x : Fin n → ZMod (p ^ k)) : Prop :=
  ¬ IsZeroType p k x ∧ ∃ i ∈ S₀, ¬ (p : ZMod (p ^ k)) ∣ x i

/-- **Bad type** (Hanke 2004, Def. 3.1, p. 358; characterized on p. 360): not Zero type and not
Good type, i.e. $\vec{x} \not\equiv \vec{0}$ but $\vec{x}_{S_0} \equiv \vec{0} \pmod p$. -/
def IsBadType (S₀ : Finset (Fin n)) (p k : ℕ) (x : Fin n → ZMod (p ^ k)) : Prop :=
  ¬ IsZeroType p k x ∧ ¬ IsGoodType S₀ p k x

/-- **Solutions of a given type:** $r^{\mathrm{T}}_{p^k}(m)$, the number of solutions of
$Q(\vec{x}) \equiv m \pmod{p^k}$ satisfying the predicate `T` (Hanke 2004, p. 358:
$r^{\mathrm{Zero}}$, $r^{\mathrm{Good}}$, $r^{\mathrm{Bad}}$). -/
noncomputable def repCountOf (Q : QuadForm ℤ n) (p k : ℕ) (m : ℤ)
    (T : (Fin n → ZMod (p ^ k)) → Prop) : ℕ :=
  Nat.card {x : Fin n → ZMod (p ^ k) // Q.evalIn (ZMod (p ^ k)) x = (m : ZMod (p ^ k)) ∧ T x}

/-- **The local density** $\beta_p(m)$ (Hanke 2004, (5.1)–(5.2), p. 368): the limit of
$r_{p^k}(m) / p^{k(n-1)}$ as $k \to \infty$ (defined as Lean's `limUnder`; it is a genuine limit,
attained for large $k$, when $Q$ is nondegenerate and $m \ne 0$: `localDensity_eventually_eq`).

*Normalization.* This matches Siegel's definition (5.1),
$\beta_p(m) = \lim_{U \to \{m\}} \mathrm{Vol}(Q^{-1}(U))/\mathrm{Vol}(U)$ with $\mathrm{Vol}(\mathbb{Z}_p) = 1$:
taking $U = m + p^k\mathbb{Z}_p$ gives $r_{p^k}(m)\,p^{-kn} / p^{-k}$. *Erratum* (confirmed by the author 2026-10-15): The paper's (5.2) prints
the denominator as $q^{(n-1)(\nu-1)}$; the correct one, used here, is $q^{\nu(n-1)}$. -/
noncomputable def localDensity (Q : QuadForm ℤ n) (p : ℕ) (m : ℤ) : ℝ :=
  Filter.limUnder Filter.atTop fun k : ℕ => (repCount Q p k m : ℝ) / (p : ℝ) ^ (k * (n - 1))

/-! ### Blueprint: the reduction procedure of §3 -/

/-- **Every solution has exactly one type:** $r_{p^k}(m) = r^{\mathrm{Zero}} + r^{\mathrm{Good}} +
r^{\mathrm{Bad}}$ (Hanke 2004, Def. 3.1, p. 358): the three types partition the solutions, for any
choice of $S_0$, since Zero type takes precedence. -/
@[kb "hanke2004" "Def. 3.1, p. 358"]
theorem repCount_eq_add_types (Q : QuadForm ℤ n) (S₀ : Finset (Fin n)) (p k : ℕ) [Fact p.Prime]
    (m : ℤ) :
    repCount Q p k m = repCountOf Q p k m (IsZeroType p k) +
      repCountOf Q p k m (IsGoodType S₀ p k) + repCountOf Q p k m (IsBadType S₀ p k) := by
  classical
  have : NeZero (p^k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  unfold repCount repCountOf
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not (fun x => IsZeroType p k x), Finset.filter_filter, add_assoc]
  congr 1
  rw [← Finset.card_filter_add_card_filter_not (fun x => IsGoodType S₀ p k x), Finset.filter_filter, Finset.filter_filter]
  congr 1
  · apply congrArg
    apply Finset.filter_congr
    intro x _
    simp only [IsGoodType]; tauto
  · apply congrArg
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    simp only [IsBadType]
    tauto

/-- **Good-type solutions lift uniformly** (Hanke 2004, Lemma 3.2, eq. (3.1), p. 358), stated here for
**diagonal** forms $Q = \langle a_0, \dots, a_{n-1} \rangle$ (a local Jordan splitting with all components
1-dimensional; the unimodular coordinates are $S_0 = \{i : p \nmid a_i\}$): for
$k \ge 2\,\mathrm{ord}_p(2) + 1$ (i.e. $k \ge 1$ for odd $p$, $k \ge 3$ for $p = 2$) and $l \ge 0$,
$r^{\mathrm{Good}}_{p^{k+l}}(m) = p^{(n-1)l}\, r^{\mathrm{Good}}_{p^k}(m)$.

*Proof* (pp. 358–359). For a Good-type solution mod $p^k$ choose $i \in S_0$ with $p \nmid x_i$, lift the
other $n - 1$ coordinates arbitrarily ($p^{(n-1)l}$ ways) and solve $a_i x^2 \equiv m' \pmod{p^{k+l}}$
with $x \equiv x_i \pmod{p^k}$: Hensel's lemma gives exactly one solution since $a_i x_i$ is a unit and
$k \ge 2\,\mathrm{ord}_p(2) + 1$. (Make the choice of $i$ canonical, e.g. the least such $i$, so that each
lift is counted once.) -/
@[kb "hanke2004" "Lemma 3.2, eq. (3.1), p. 358"]
theorem repCountGood_add_diag (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (m : ℤ) (k l : ℕ)
    (hk : 2 * (if p = 2 then 1 else 0) + 1 ≤ k) :
    repCountOf (QuadForm.diag a) p (k + l) m
        (IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ a i) p (k + l)) =
      p ^ ((n - 1) * l) * repCountOf (QuadForm.diag a) p k m
        (IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ a i) p k) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hk1 : 1 ≤ k := by split_ifs at hk <;> omega
  have fibsum : ∀ {G H : Type} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H) (_hf : Function.Surjective f) (F : H → ℕ), (∑ x, F (f x)) * Fintype.card H = Fintype.card G * ∑ y, F y := by
    intro G H _ _ _ _ _ f hf F
    classical
    have hfib : ∀ h : H, (Finset.univ.filter (fun g => f g = h)).card = (Finset.univ.filter (fun g => f g = 0)).card := fun h =>
      AddMonoidHom.card_fiber_eq_of_mem_range f (hf h) ⟨0, map_zero f⟩
    have e1 : ∑ x, F (f x) = (Finset.univ.filter (fun g => f g = 0)).card * ∑ y, F y := by
      rw [← Finset.sum_fiberwise Finset.univ f (fun x => F (f x)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => F y), Finset.sum_const, smul_eq_mul, hfib]
      intro x hx; rw [(Finset.mem_filter.1 hx).2]
    have e2 : Fintype.card G = (Finset.univ.filter (fun g => f g = 0)).card * Fintype.card H := by
      rw [← Finset.card_univ, ← Finset.card_univ (α := H), Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (by simp)]
      rw [Finset.sum_congr rfl (fun y _ => hfib y)]
      simp [mul_comm]
    rw [e1, e2]; ring
  have rootcount : ∀ {A : Type} [CommRing A] [Fintype A] [DecidableEq A] (β : A) (_ : IsUnit β) (c : A),
      (Finset.univ.filter (fun u => IsUnit u ∧ β * u^2 = c)).card =
        if (∃ u, IsUnit u ∧ β * u^2 = c) then (Finset.univ.filter (fun s : A => s^2 = 1)).card else 0 := by
    intro A _ _ _ β hβ c
    classical
    split_ifs with h
    · obtain ⟨u0, hu0, hc⟩ := h
      symm
      refine Finset.card_bij' (fun s _ => u0 * s) (fun u _ => hu0.unit⁻¹ * u) ?_ ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        refine ⟨hu0.mul (IsUnit.of_mul_eq_one s (by rw [← hs]; ring)), ?_⟩
        rw [← hc, mul_pow, hs]; ring
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        obtain ⟨hu, hc'⟩ := hu
        have h1 : β * (hu0.unit⁻¹ * u) ^ 2 * u0^2 = β * u0 ^ 2 := by
          rw [hc, ← hc']
          have : (↑hu0.unit⁻¹ : A) * u0 = 1 := hu0.val_inv_mul
          linear_combination (β * u^2 * (↑hu0.unit⁻¹ * u0 + 1)) * this
        have h2 := (hβ.mul (hu0.pow 2)).mul_left_cancel (a := β * u0^2) (b := (hu0.unit⁻¹ * u) ^ 2) (c := 1)
        apply h2
        linear_combination h1
      · intro s _; rw [← mul_assoc, hu0.val_inv_mul, one_mul]
      · intro u _; rw [← mul_assoc, hu0.mul_val_inv, one_mul]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u _ hu; exact h ⟨u, hu⟩
  have lemG : ∀ {R S : Type} [CommRing R] [CommRing S] [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S] (π : R →+* S) (_ : Function.Surjective π) (_ : ∀ x, IsUnit (π x) → IsUnit x) (_ : (Finset.univ.filter (fun s : R => s^2 = 1)).card = (Finset.univ.filter (fun s : S => s^2 = 1)).card) (α : R) (_ : IsUnit α) (c : R), (Finset.univ.filter (fun u => IsUnit u ∧ α * u^2 = c)).card = (Finset.univ.filter (fun v => IsUnit v ∧ π α * v^2 = π c)).card := by
    intro R S _ _ _ _ _ _ π hπ hunit hT α hα c
    classical
    have hα' : IsUnit (π α) := hα.map π
    have hunit' : ∀ x, IsUnit (π x) ↔ IsUnit x := fun x => ⟨hunit x, fun h => h.map π⟩
    have hsum : ∀ {A : Type} [CommRing A] [Fintype A] [DecidableEq A] (β : A), (∑ c, (Finset.univ.filter (fun u => IsUnit u ∧ β * u^2 = c)).card) = (Finset.univ.filter (fun u : A => IsUnit u)).card := by
      intro A _ _ _ β
      rw [Finset.card_eq_sum_card_fiberwise (f := fun u => β * u^2) (t := Finset.univ) (by simp)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.filter_filter]
    have hE : ∀ {A : Type} [CommRing A] [Fintype A] [DecidableEq A] (β : A) (_ : IsUnit β), (Finset.univ.filter (fun c => ∃ u, IsUnit u ∧ β * u^2 = c)).card * (Finset.univ.filter (fun s : A => s^2 = 1)).card = (Finset.univ.filter (fun u : A => IsUnit u)).card := by
      intro A _ _ _ β hβ
      rw [← hsum β, Finset.card_eq_sum_ones, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [rootcount β hβ c]; split_ifs <;> simp
    have hU : (Finset.univ.filter (fun u : R => IsUnit u)).card * Fintype.card S = Fintype.card R * (Finset.univ.filter (fun u : S => IsUnit u)).card := by
      have := fibsum π.toAddMonoidHom hπ (fun y => if IsUnit y then 1 else 0)
      simp only [Finset.card_filter]
      convert this using 3
      simp [hunit']
    have hP : (Finset.univ.filter (fun c => ∃ u, IsUnit u ∧ π α * u^2 = π c)).card * Fintype.card S = Fintype.card R * (Finset.univ.filter (fun c => ∃ u, IsUnit u ∧ π α * u^2 = c)).card := by
      have := fibsum π.toAddMonoidHom hπ (fun y => if (∃ u, IsUnit u ∧ π α * u^2 = y) then 1 else 0)
      simp only [Finset.card_filter]
      exact this
    have hsub : Finset.univ.filter (fun c => ∃ u, IsUnit u ∧ α * u^2 = c) ⊆ Finset.univ.filter (fun c => ∃ u, IsUnit u ∧ π α * u^2 = π c) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      obtain ⟨u, hu, rfl⟩ := hc
      exact ⟨π u, hu.map π, by simp⟩
    have hTpos : 0 < (Finset.univ.filter (fun s : R => s^2 = 1)).card := Finset.card_pos.2 ⟨1, by simp⟩
    have hSpos : 0 < Fintype.card S := Fintype.card_pos
    have heq : Finset.univ.filter (fun c => ∃ u, IsUnit u ∧ α * u^2 = c) = Finset.univ.filter (fun c => ∃ u, IsUnit u ∧ π α * u^2 = π c) := by
      apply Finset.eq_of_subset_of_card_le hsub
      have h1 := hE α hα
      have h2 := hE (π α) hα'
      rw [← hT] at h2
      have : (Finset.univ.filter (fun c => ∃ u, IsUnit u ∧ π α * u^2 = π c)).card * Fintype.card S * (Finset.univ.filter (fun s : R => s^2 = 1)).card ≤ (Finset.univ.filter (fun c => ∃ u, IsUnit u ∧ α * u^2 = c)).card * Fintype.card S * (Finset.univ.filter (fun s : R => s^2 = 1)).card := by
        rw [hP, mul_assoc, h2, mul_right_comm, h1, hU]
      exact le_of_mul_le_mul_right (le_of_mul_le_mul_right this hTpos) hSpos
    have hc := congrArg (fun s => c ∈ s) heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [rootcount α hα c, rootcount (π α) hα' (π c), hT]
    simp only [hc]
  have C1 : ∀ {R : Type} [CommRing R] [Fintype R] [DecidableEq R] (b : Fin n → R) (m : R) (S : Finset (Fin n)),
      Fintype.card R * (Finset.univ.filter fun x : Fin n → R => ∑ i, b i * x i^2 = m ∧ ∃ i ∈ S, IsUnit (x i)).card
      = (Finset.univ.filter fun w : Fin n × (Fin n → R) × R => w.1 ∈ S ∧ (∀ i' ∈ S, i' < w.1 → ¬IsUnit (w.2.1 i')) ∧ IsUnit w.2.2 ∧ b w.1 * w.2.2^2 + ∑ j, b j * (Function.update w.2.1 w.1 0 j)^2 = m).card := by
    intro R _ _ _ b m S
    classical
    have hupd : ∀ (x : Fin n → R) (i : Fin n) (u : R), ∑ j, b j * Function.update x i u j ^ 2 = b i * u ^ 2 + ∑ j, b j * Function.update x i 0 j ^ 2 := by
      intro x i u
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [Function.update_self]
      rw [Finset.sum_congr rfl (g := fun j => b j * Function.update x i 0 j ^ 2)]
      · ring
      · intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [mul_comm, ← Finset.card_univ, ← Finset.card_product]
    symm
    refine Finset.card_bij (fun w _ => (Function.update w.2.1 w.1 w.2.2, w.2.1 w.1)) ?_ ?_ ?_
    · rintro ⟨i, x, u⟩ hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true] at hw ⊢
      obtain ⟨hi, _, hu, heq⟩ := hw
      refine ⟨by rw [hupd]; exact heq, i, hi, by simpa using hu⟩
    · rintro ⟨i, x, u⟩ hw ⟨i', x', u'⟩ hw' h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
      simp only [Prod.mk.injEq] at h ⊢
      obtain ⟨h1, h2⟩ := h
      have hii : i = i' := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · apply hw'.2.1 i hw.1 hlt
          have := congrFun h1 i
          rw [Function.update_self, Function.update_of_ne hne] at this
          rw [← this]; exact hw.2.2.1
        · apply hw.2.1 i' hw'.1 hlt
          have := congrFun h1 i'
          rw [Function.update_self, Function.update_of_ne (Ne.symm hne)] at this
          rw [this]; exact hw'.2.2.1
      subst hii
      refine ⟨rfl, ?_, ?_⟩
      · funext j
        by_cases hj : j = i
        · subst hj; exact h2
        · have := congrFun h1 j
          rwa [Function.update_of_ne hj, Function.update_of_ne hj] at this
      · have := congrFun h1 i
        rwa [Function.update_self, Function.update_self] at this
    · rintro ⟨y, t⟩ hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true] at hy
      obtain ⟨hQ, hex⟩ := hy
      have hne : (S.filter fun i => IsUnit (y i)).Nonempty := by
        obtain ⟨i, hi, hu⟩ := hex; exact ⟨i, by simp [hi, hu]⟩
      set i := (S.filter fun i => IsUnit (y i)).min' hne with hi_def
      have hiS := Finset.min'_mem _ hne
      rw [← hi_def] at hiS
      simp only [Finset.mem_filter] at hiS
      refine ⟨(i, Function.update y i t, y i), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hiS.1, ?_, hiS.2, ?_⟩
        · intro i' hi' hlt hu
          rw [Function.update_of_ne (ne_of_lt hlt)] at hu
          have := Finset.min'_le (S.filter fun i => IsUnit (y i)) i' (by simp [hi', hu])
          rw [← hi_def] at this
          exact absurd hlt (not_lt.2 this)
        · simp only [Function.update_idem]
          rw [← hupd, Function.update_eq_self]; exact hQ
      · simp
  have C2 : ∀ {R : Type} [CommRing R] [Fintype R] [DecidableEq R] (b : Fin n → R) (m : R) (S : Finset (Fin n)),
      (Finset.univ.filter fun w : Fin n × (Fin n → R) × R => w.1 ∈ S ∧ (∀ i' ∈ S, i' < w.1 → ¬IsUnit (w.2.1 i')) ∧ IsUnit w.2.2 ∧ b w.1 * w.2.2^2 + ∑ j, b j * (Function.update w.2.1 w.1 0 j)^2 = m).card
      = ∑ i, ∑ x : Fin n → R, if (i ∈ S ∧ ∀ i' ∈ S, i' < i → ¬IsUnit (x i')) then (Finset.univ.filter fun u => IsUnit u ∧ b i * u^2 = m - ∑ j, b j * (Function.update x i 0 j)^2).card else 0 := by
    intro R _ _ _ b m S
    classical
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [eq_sub_iff_add_eq]
      split_ifs <;> first | rfl | (exfalso; tauto)
    · refine Finset.sum_eq_zero fun u _ => ?_
      exact if_neg (by rintro ⟨h1, h2, _⟩; exact h ⟨h1, h2⟩)
  have Todd : ∀ j, p ≠ 2 → 1 ≤ j → (Finset.univ.filter (fun s : ZMod (p^j) => s^2 = 1)).card = 2 := by
    intro j hp2 hj
    have hpZ : Prime (p:ℤ) := Nat.prime_iff_prime_int.1 hp
    have h2 : (2 : ZMod (p^j)) ≠ 0 := by
      intro h
      have : ((2:ℕ) : ZMod (p^j)) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      have h3 := Nat.le_of_dvd (by norm_num) this
      have h4 : p ≤ p^j := Nat.le_self_pow (by omega) p
      have h5 := hp.two_le
      omega
    have hset : Finset.univ.filter (fun s : ZMod (p^j) => s^2 = 1) = {1, -1} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hs
        rw [← ZMod.intCast_zmod_cast s] at hs ⊢
        set t : ℤ := s.cast
        have hd : ((p^j : ℕ) : ℤ) ∣ (t - 1) * (t + 1) := by
          have : ((t^2 : ℤ) : ZMod (p^j)) = ((1:ℤ) : ZMod (p^j)) := by push_cast; exact hs
          rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
          have := this.neg_right
          convert this using 1; ring
        push_cast at hd
        by_cases hA : (p:ℤ) ∣ t + 1
        · by_cases hB : (p:ℤ) ∣ t - 1
          · exfalso
            have : (p:ℤ) ∣ 2 := by have := dvd_sub hA hB; convert this using 1; ring
            have : p ∣ 2 := by exact_mod_cast this
            have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
            exact hp2 this
          · have hc : IsCoprime ((p:ℤ)^j) (t - 1) := ((Prime.coprime_iff_not_dvd hpZ).2 hB).pow_left
            have := hc.dvd_of_dvd_mul_left hd
            right
            have : ((t:ℤ) : ZMod (p^j)) = ((-1 : ℤ) : ZMod (p^j)) := by
              rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast
              have := this.neg_right; convert this using 1; ring
            simpa using this
        · have hc : IsCoprime ((p:ℤ)^j) (t + 1) := ((Prime.coprime_iff_not_dvd hpZ).2 hA).pow_left
          have := hc.dvd_of_dvd_mul_right hd
          left
          have : ((t:ℤ) : ZMod (p^j)) = ((1 : ℤ) : ZMod (p^j)) := by
            rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast
            have := this.neg_right; convert this using 1; ring
          simpa using this
      · rintro (rfl | rfl) <;> ring
    rw [hset, Finset.card_insert_of_notMem, Finset.card_singleton]
    simp only [Finset.mem_singleton]
    intro h; apply h2; linear_combination h
  have T2 : ∀ i : ℕ, (Finset.univ.filter (fun s : ZMod (2^(i+3)) => s^2 = 1)).card = 4 := by
    intro i
    set h : ZMod (2^(i+3)) := ((2^(i+2) : ℕ) : ZMod (2^(i+3))) with hh
    have h2h : 2 * h = 0 := by
      have e : (2:ZMod (2^(i+3))) * h = ((2^(i+3) : ℕ) : ZMod (2^(i+3))) := by rw [hh]; push_cast; ring
      rw [ZMod.natCast_self] at e; exact e
    have hhh : h * h = 0 := by
      have : h * h = 2 * h * 2^(i+1) := by rw [hh]; push_cast; ring
      rw [this, h2h, zero_mul]
    have hne : ∀ a b : ℕ, a < 2^(i+3) → b < 2^(i+3) → a ≠ b → ((a : ℕ) : ZMod (2^(i+3))) ≠ (b : ℕ) := by
      intro a b ha hb hab heq
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at heq
      exact hab heq
    have hP : 2^(i+3) = 2 * 2^(i+2) := by ring
    have hP2 : 4 ≤ 2^(i+2) := by
      calc 4 = 2^2 := by norm_num
        _ ≤ 2^(i+2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hset : Finset.univ.filter (fun s : ZMod (2^(i+3)) => s^2 = 1) = {1, -1, 1 + h, -1 + h} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hs
        rw [← ZMod.intCast_zmod_cast s] at hs ⊢
        set t : ℤ := s.cast
        have hd : ((2^(i+3) : ℕ) : ℤ) ∣ (t - 1) * (t + 1) := by
          have : ((t^2 : ℤ) : ZMod (2^(i+3))) = ((1:ℤ) : ZMod (2^(i+3))) := by push_cast; exact hs
          rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
          have := this.neg_right
          convert this using 1; ring
        push_cast at hd
        have hodd : ¬ (2:ℤ) ∣ t := by
          rintro ⟨c, hc⟩
          have : (2:ℤ) ∣ (t-1)*(t+1) := dvd_trans (dvd_pow_self 2 (by omega)) hd
          rw [hc] at this
          have : (2:ℤ) ∣ 1 := by
            have h3 := (dvd_mul_right (2:ℤ) (2*c*c))
            have := dvd_sub h3 this
            convert this using 1; ring
          omega
        obtain ⟨a, ha⟩ : ∃ a, t = 2 * a + 1 := ⟨t / 2, by omega⟩
        have hd2 : (2:ℤ)^(i+1) ∣ a * (a + 1) := by
          rw [ha] at hd
          have : (2:ℤ)^(i+3) = 4 * 2^(i+1) := by ring
          rw [this, show (2 * a + 1 - 1) * (2 * a + 1 + 1) = 4 * (a * (a+1)) by ring] at hd
          exact (mul_dvd_mul_iff_left (by norm_num)).1 hd
        have key : ∀ b : ℤ, ∀ c : ZMod (2^(i+3)), (t : ZMod (2^(i+3))) = c + h * (b : ZMod (2^(i+3))) → (t : ZMod (2^(i+3))) = c ∨ (t : ZMod (2^(i+3))) = c + h := by
          intro b c hb
          rcases Int.emod_two_eq b with hr | hr
          · left; rw [hb, ← Int.emod_add_mul_ediv b 2, hr]; push_cast; linear_combination ((b / 2 : ℤ) : ZMod (2^(i+3))) * h2h
          · right; rw [hb, ← Int.emod_add_mul_ediv b 2, hr]; push_cast; linear_combination ((b / 2 : ℤ) : ZMod (2^(i+3))) * h2h
        have hpZ : Prime (2:ℤ) := Int.prime_two
        by_cases hA : (2:ℤ) ∣ a
        · have hc : IsCoprime ((2:ℤ)^(i+1)) (a + 1) := ((Prime.coprime_iff_not_dvd hpZ).2 (by omega)).pow_left
          obtain ⟨b, hb⟩ := hc.dvd_of_dvd_mul_right hd2
          have : (t : ZMod (2^(i+3))) = 1 + h * (b : ZMod (2^(i+3))) := by
            rw [ha, hb, hh]; push_cast; ring
          rcases key b 1 this with h1 | h1
          · left; exact h1
          · right; right; left; exact h1
        · have hc : IsCoprime ((2:ℤ)^(i+1)) a := ((Prime.coprime_iff_not_dvd hpZ).2 hA).pow_left
          obtain ⟨b, hb⟩ := hc.dvd_of_dvd_mul_left hd2
          have : (t : ZMod (2^(i+3))) = -1 + h * (b : ZMod (2^(i+3))) := by
            rw [show a = (a + 1) - 1 by ring, hb] at ha
            rw [ha, hh]; push_cast; ring
          rcases key b (-1) this with h1 | h1
          · right; left; exact h1
          · right; right; right; exact h1
      · rintro (rfl | rfl | rfl | rfl)
        · ring
        · ring
        · linear_combination h2h + hhh
        · linear_combination -h2h + hhh
    rw [hset]
    have e1 : (-1 : ZMod (2^(i+3))) = ((2^(i+3) - 1 : ℕ) : ZMod (2^(i+3))) := by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]; simp
    have e2 : (1 + h : ZMod (2^(i+3))) = ((2^(i+2) + 1 : ℕ) : ZMod (2^(i+3))) := by rw [hh]; push_cast; ring
    have e3 : (-1 + h : ZMod (2^(i+3))) = ((2^(i+2) - 1 : ℕ) : ZMod (2^(i+3))) := by
      rw [hh, Nat.cast_sub (by omega)]; push_cast; ring
    have e0 : (1 : ZMod (2^(i+3))) = ((1 : ℕ) : ZMod (2^(i+3))) := by simp
    rw [e2, e3, e1, e0]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact hne _ _ (by omega) (by omega) (by omega)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne _ _ (by omega) (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne _ _ (by omega) (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega)⟩
  have hchar : ∀ K, 1 ≤ K → ∀ (x : ZMod (p^K)), (p : ZMod (p^K)) ∣ x ↔ ¬ IsUnit x := by
    intro K hK x
    have : NeZero (p^K) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hpd : p ∣ p^K := dvd_pow_self p (by omega)
    have h1 : (p : ZMod (p^K)) ∣ x ↔ p ∣ x.val := by
      constructor
      · rintro ⟨y, rfl⟩
        rw [ZMod.val_mul, (Nat.dvd_mod_iff hpd)]
        exact Dvd.dvd.mul_right (by rw [ZMod.val_natCast, (Nat.dvd_mod_iff hpd)]) _
      · rintro ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [← ZMod.natCast_zmod_val x, ht]; push_cast; ring
    rw [h1, ← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.coprime_pow_right_iff (by omega),
      Nat.coprime_comm, hp.coprime_iff_not_dvd, not_not]
  set S : Finset (Fin n) := Finset.univ.filter fun i => ¬ (p : ℤ) ∣ a i with hS
  have hintunit : ∀ j, 1 ≤ j → ∀ β : ℤ, ¬ (p:ℤ) ∣ β → IsUnit (β : ZMod (p^j)) := by
    intro j hj β hβ
    rw [← not_not (a := IsUnit _), ← hchar j hj]
    rintro ⟨y, hy⟩
    apply hβ
    rw [← ZMod.intCast_zmod_cast y, show ((p : ZMod (p^j)) = ((p:ℤ) : ZMod (p^j))) by simp, ← Int.cast_mul, ZMod.intCast_eq_intCast_iff_dvd_sub] at hy
    have h1 : (p:ℤ) ∣ (p:ℤ) * (y.cast : ℤ) - β := dvd_trans (by push_cast; exact dvd_pow_self (p:ℤ) (by omega)) hy
    have := dvd_sub (dvd_mul_right (p:ℤ) (y.cast : ℤ)) h1
    simpa using this
  have hgood : ∀ j, 1 ≤ j → ∀ x : Fin n → ZMod (p^j), IsGoodType S p j x ↔ ∃ i ∈ S, IsUnit (x i) := by
    intro j hj x
    unfold IsGoodType IsZeroType
    simp only [hchar j hj, not_not]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun hall => ?_, h⟩
      obtain ⟨i, _, hi⟩ := h
      exact hall i hi
  have hdiag : ∀ (N : ℕ) (x : Fin n → ZMod N), (QuadForm.diag a).evalIn (ZMod N) x = ∑ i, (a i : ZMod N) * x i ^ 2 := by
    intro N x
    simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have hrep : ∀ j, 1 ≤ j → repCountOf (QuadForm.diag a) p j m (IsGoodType S p j) = (Finset.univ.filter fun x : Fin n → ZMod (p^j) => ∑ i, (a i : ZMod (p^j)) * x i^2 = (m : ZMod (p^j)) ∧ ∃ i ∈ S, IsUnit (x i)).card := by
    intro j hj
    unfold repCountOf
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    apply Finset.filter_congr
    intro x _
    rw [hdiag, hgood j hj]
  have hT : ∀ j, 2 * (if p = 2 then 1 else 0) + 1 ≤ j → (Finset.univ.filter (fun s : ZMod (p^j) => s^2 = 1)).card = if p = 2 then 4 else 2 := by
    intro j hj
    split_ifs at hj ⊢ with h2
    · subst h2
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
      exact T2 i
    · exact Todd j h2 (by omega)
  have hdvd : p^k ∣ p^(k+l) := pow_dvd_pow p (Nat.le_add_right k l)
  set π := ZMod.castHom hdvd (ZMod (p^k)) with hπ
  have hπsurj : Function.Surjective π := ZMod.castHom_surjective hdvd
  have hπunit : ∀ x, IsUnit (π x) ↔ IsUnit x := by
    intro x
    refine ⟨fun h => ?_, fun h => h.map π⟩
    by_contra hx
    rw [← hchar (k+l) (by omega)] at hx
    obtain ⟨y, rfl⟩ := hx
    apply (hchar k hk1 _).1 _ h
    rw [map_mul, map_natCast]
    exact dvd_mul_right _ _
  have hN : ∀ β : ℤ, ¬ (p:ℤ) ∣ β → ∀ c : ZMod (p^(k+l)), (Finset.univ.filter (fun u => IsUnit u ∧ (β : ZMod (p^(k+l))) * u^2 = c)).card = (Finset.univ.filter (fun v => IsUnit v ∧ (β : ZMod (p^k)) * v^2 = π c)).card := by
    intro β hβ c
    have := lemG π hπsurj (fun x => (hπunit x).1) (by rw [hT k hk, hT (k+l) (by omega)]) (β : ZMod (p^(k+l))) (hintunit _ (by omega) β hβ) c
    rw [this, map_intCast]
  have hcardF : ∀ j, Fintype.card (Fin n → ZMod (p^j)) = (p^j)^n := by
    intro j; rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have h1K := C1 (fun i => (a i : ZMod (p^(k+l)))) (m : ZMod (p^(k+l))) S
  have h1k := C1 (fun i => (a i : ZMod (p^k))) (m : ZMod (p^k)) S
  rw [C2 (fun i => (a i : ZMod (p^(k+l)))) (m : ZMod (p^(k+l))) S, ZMod.card] at h1K
  rw [C2 (fun i => (a i : ZMod (p^k))) (m : ZMod (p^k)) S, ZMod.card] at h1k
  rw [hrep (k+l) (by omega), hrep k hk1]
  set F : Fin n → (Fin n → ZMod (p^k)) → ℕ := fun i y => if (i ∈ S ∧ ∀ i' ∈ S, i' < i → ¬IsUnit (y i')) then (Finset.univ.filter fun u => IsUnit u ∧ (a i : ZMod (p^k)) * u^2 = (m : ZMod (p^k)) - ∑ j, (a j : ZMod (p^k)) * (Function.update y i 0 j)^2).card else 0 with hF
  let f : (Fin n → ZMod (p^(k+l))) →+ (Fin n → ZMod (p^k)) := AddMonoidHom.compLeft π.toAddMonoidHom (Fin n)
  have hf : ∀ x, f x = fun i => π (x i) := fun x => rfl
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨y, hy⟩ := (Function.Surjective.comp_left hπsurj (α := Fin n)) z
    exact ⟨y, hy⟩
  have hupdπ : ∀ (x : Fin n → ZMod (p^(k+l))) i j, π (Function.update x i 0 j) = Function.update (fun i => π (x i)) i 0 j := by
    intro x i j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  have hsummand : ∀ i (x : Fin n → ZMod (p^(k+l))), (if (i ∈ S ∧ ∀ i' ∈ S, i' < i → ¬IsUnit (x i')) then (Finset.univ.filter fun u => IsUnit u ∧ (a i : ZMod (p^(k+l))) * u^2 = (m : ZMod (p^(k+l))) - ∑ j, (a j : ZMod (p^(k+l))) * (Function.update x i 0 j)^2).card else 0) = F i (f x) := by
    intro i x
    simp only [hF, hf, hπunit]
    split_ifs with h
    · have hai : ¬ (p:ℤ) ∣ a i := by have := h.1; rw [hS] at this; simpa using this
      rw [hN (a i) hai]
      simp only [map_sub, map_sum, map_mul, map_pow, map_intCast, hupdπ]
    · rfl
  have h1k' : p^k * (Finset.univ.filter fun x : Fin n → ZMod (p^k) => ∑ i, (a i : ZMod (p^k)) * x i^2 = (m : ZMod (p^k)) ∧ ∃ i ∈ S, IsUnit (x i)).card = ∑ i, ∑ y, F i y := h1k
  have key : p^(k+l) * (Finset.univ.filter fun x : Fin n → ZMod (p^(k+l)) => ∑ i, (a i : ZMod (p^(k+l))) * x i^2 = (m : ZMod (p^(k+l))) ∧ ∃ i ∈ S, IsUnit (x i)).card * (p^k)^n = (p^(k+l))^n * (p^k * (Finset.univ.filter fun x : Fin n → ZMod (p^k) => ∑ i, (a i : ZMod (p^k)) * x i^2 = (m : ZMod (p^k)) ∧ ∃ i ∈ S, IsUnit (x i)).card) := by
    rw [h1K, h1k', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (fun x _ => hsummand i x)]
    have := fibsum f hfsurj (F i)
    rwa [hcardF, hcardF] at this
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n-1, by omega⟩
    have arith : ∀ GK Gk : ℕ, p^(k+l) * GK * (p^k)^(n'+1) = (p^(k+l))^(n'+1) * (p^k * Gk) → GK = p^((n'+1-1)*l) * Gk := by
      intro GK Gk h
      apply Nat.eq_of_mul_eq_mul_left (show 0 < p^(k+l) * (p^k)^(n'+1) by have := hp.pos; positivity)
      rw [Nat.add_sub_cancel]
      calc p^(k+l) * (p^k)^(n'+1) * GK = p^(k+l) * GK * (p^k)^(n'+1) := by ring
        _ = (p^(k+l))^(n'+1) * (p^k * Gk) := h
        _ = _ := by ring
    exact arith _ _ key

/-- **Remark 3.1.1 for odd $p$** (Hanke 2004, p. 358, corrected): for a diagonal form and odd $p$,
$\vec{x}$ is of Good type iff it is not of Zero type and $B(\vec{x}, \vec{e}_j) \not\equiv 0 \pmod p$ for
some $j$, i.e. some entry of $H\vec{x}$ is nonzero mod $p$ ($H$ the Hessian). This is the
basis-free description $\vec{x} \notin L^{p} = \{\vec{x} : B(\vec{x}, L) \subseteq p\mathbb{Z}_p\}$.

*Update*: Remark 3.1.1 prints $B(\vec{x}, L) \subseteq \mathfrak{o}_\mathfrak{p}$; it
should be $\subseteq \mathfrak{p}$, and the reformulation holds only for odd $p$ (at $p = 2$:
$Q = x_0^2 + x_1^2$, $\vec{x} = (1,1)$ is Good, but $Q(\vec{x})$ and all $B(\vec{x}, \cdot)$ vanish mod 2).
*Proof:* $(H\vec{x})_j = 2 a_j x_j$ and $2$ is a unit mod odd $p$. -/
@[kb "hanke2004" "Remark 3.1.1, p. 358 (corrected)"]
theorem isGoodType_diag_iff_hessian (a : Fin n → ℤ) (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hk : 1 ≤ k) (x : Fin n → ZMod (p ^ k)) :
    IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ a i) p k x ↔
      ¬ IsZeroType p k x ∧ ∃ j, ¬ (p : ZMod (p ^ k)) ∣
        ((QuadForm.diag a).hessian.map (Int.castRingHom (ZMod (p ^ k))) *ᵥ x) j := by
  have hpp : p.Prime := Fact.out
  have hdvd : p ∣ p ^ k := dvd_pow_self p (by omega)
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  let φ := ZMod.castHom hdvd (ZMod p)
  have key : ∀ y : ZMod (p ^ k), (p : ZMod (p ^ k)) ∣ y ↔ φ y = 0 := by
    intro y
    constructor
    · rintro ⟨c, rfl⟩
      rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]
    · intro h
      have h1 : φ y = ((y.val : ℕ) : ZMod p) := by
        rw [ZMod.castHom_apply, ZMod.cast_eq_val]
      rw [h1, ZMod.natCast_eq_zero_iff] at h
      obtain ⟨c, hc⟩ := h
      refine ⟨(c : ZMod (p ^ k)), ?_⟩
      rw [← ZMod.natCast_zmod_val y, hc]
      push_cast; ring
  have hent : ∀ j, ((QuadForm.diag a).hessian.map (Int.castRingHom (ZMod (p ^ k))) *ᵥ x) j = 2 * (a j : ZMod (p ^ k)) * x j := by
    intro j
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
    · simp [QuadForm.hessian, QuadForm.diag]; ring
    · intro b _ hb
      simp [QuadForm.hessian, QuadForm.diag, Ne.symm hb]
    · simp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2:ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have := hpp.two_le; omega
  unfold IsGoodType
  refine and_congr Iff.rfl ?_
  simp only [hent, key, map_mul, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [φ, map_intCast, map_ofNat, mul_eq_zero, h2, false_or, not_or, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **Zero-type reduction** (Hanke 2004, §3, the map $\pi_Z$, p. 359): for $k \ge 2$, Zero-type solutions
mod $p^k$ exist only if $p^2 \mid m$, and then $r^{\mathrm{Zero}}_{p^k}(m) = p^n\, r_{p^{k-2}}(m/p^2)$
(the map $\vec{x} \mapsto p^{-1}\vec{x} \bmod p^{k-2}$ is surjective with multiplicity $q^n = p^n$). -/
@[kb "hanke2004" "§3, map π_Z, p. 359"]
theorem repCountZero_eq (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (m : ℤ) (k : ℕ) (hk : 2 ≤ k) :
    repCountOf Q p k m (IsZeroType p k) =
      if (p : ℤ) ^ 2 ∣ m then p ^ n * repCount Q p (k - 2) (m / p ^ 2) else 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 - 2 = j by omega]
  have hfiber : ∀ {G H : Type} [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H] (f : G →+ H) (_hf : Function.Surjective f) (P : H → Prop), Nat.card {g // P (f g)} * Nat.card H = Nat.card G * Nat.card {h // P h} := by
    intro G H _ _ _ _ f hf P
    classical
    have := Fintype.ofFinite G
    have := Fintype.ofFinite H
    have hfib : ∀ h : H, (Finset.univ.filter (fun g => f g = h)).card = (Finset.univ.filter (fun g => f g = 0)).card := fun h =>
      AddMonoidHom.card_fiber_eq_of_mem_range f (hf h) ⟨0, map_zero f⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype]
    have h1 := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter (fun g => P (f g))) (t := Finset.univ.filter P) (f := f) (by intro x hx; simpa using hx)
    have h2 := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset G)) (t := Finset.univ) (f := f) (by intro x hx; simp)
    rw [h1, ← Finset.card_univ (α := G), h2]
    have h3 : ∀ b ∈ Finset.univ.filter P, ((Finset.univ.filter (fun g => P (f g))).filter (fun a => f a = b)).card = (Finset.univ.filter (fun g => f g = 0)).card := by
      intro b hb
      rw [← hfib b, Finset.filter_filter]
      congr 1
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hb, h⟩
    rw [Finset.sum_congr rfl h3]
    have h4 : ∀ b ∈ (Finset.univ : Finset H), ((Finset.univ : Finset G).filter (fun a => f a = b)).card = (Finset.univ.filter (fun g => f g = 0)).card := fun b _ => hfib b
    rw [Finset.sum_congr rfl h4]
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    ring
  have hp := (Fact.out : p.Prime)
  have hp0 : 0 < p := hp.pos
  have hmap : ∀ (N : ℕ) (v : Fin n → ℤ), Q.evalIn (ZMod N) (fun i => ((v i : ℤ) : ZMod N)) = ((Q.evalIn ℤ v : ℤ) : ZMod N) := by
    intro N v
    simp [QuadForm.evalIn]
  have hhom : ∀ (c : ℤ) (v : Fin n → ℤ), Q.evalIn ℤ (fun i => c * v i) = c^2 * Q.evalIn ℤ v := by
    intro c v
    simp only [QuadForm.evalIn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp <;> ring
  have key : ∀ y : Fin n → ZMod (p^(j+1)), Q.evalIn (ZMod (p^(j+2))) (fun i => ((p * (y i).val : ℕ) : ZMod (p^(j+2)))) = (((p:ℤ)^2 * Q.evalIn ℤ (fun i => ((y i).val : ℤ)) : ℤ) : ZMod (p^(j+2))) := by
    intro y
    rw [← hhom, ← hmap]
    congr 1
    ext i
    push_cast
    rfl
  have : NeZero (p^(j+1)) := ⟨by positivity⟩
  have : NeZero (p^(j+2)) := ⟨by positivity⟩
  have hb : ∀ a : ZMod (p^(j+1)), p * a.val < p^(j+2) := fun a => by
    have := Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) hp0
    rwa [← pow_succ'] at this
  have hA : repCountOf Q p (j+2) m (IsZeroType p (j+2)) = Nat.card {y : Fin n → ZMod (p^(j+1)) // (((p:ℤ)^2 * Q.evalIn ℤ (fun i => ((y i).val : ℤ)) : ℤ) : ZMod (p^(j+2))) = m} := by
    symm
    refine Nat.card_eq_of_bijective (fun y => ⟨fun i => ((p * (y.1 i).val : ℕ) : ZMod (p^(j+2))), by rw [key]; exact y.2, fun i => ⟨((y.1 i).val : ZMod (p^(j+2))), by push_cast; rfl⟩⟩) ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩ ⟨y', hy'⟩ h
      simp only [Subtype.mk.injEq] at h ⊢
      funext i
      have h1 := congrFun h i
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hb _), Nat.mod_eq_of_lt (hb _)] at h1
      exact ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left hp0 h1)
    · rintro ⟨x, hx1, hx2⟩
      obtain ⟨c, hc⟩ : ∃ c : Fin n → ZMod (p^(j+2)), ∀ i, x i = p * c i :=
        ⟨fun i => (hx2 i).choose, fun i => (hx2 i).choose_spec⟩
      have hxy : (fun i => ((p * (((c i).val : ZMod (p^(j+1)))).val : ℕ) : ZMod (p^(j+2)))) = x := by
        funext i
        rw [hc i, ZMod.val_natCast, ← Nat.mul_mod_mul_left, ← pow_succ', ZMod.natCast_mod]
        push_cast
        simp
      refine ⟨⟨fun i => ((c i).val : ZMod (p^(j+1))), ?_⟩, ?_⟩
      · rw [← key, hxy]; exact hx1
      · simp only [Subtype.mk.injEq]; exact hxy
  rw [hA]
  split_ifs with hm
  · obtain ⟨m', rfl⟩ := hm
    have hp2 : (p:ℤ)^2 ≠ 0 := by positivity
    rw [Int.mul_ediv_cancel_left _ hp2]
    have hdvd : p^j ∣ p^(j+1) := pow_dvd_pow p (Nat.le_succ j)
    let π : (Fin n → ZMod (p^(j+1))) →+ (Fin n → ZMod (p^j)) :=
      AddMonoidHom.compLeft (ZMod.castHom hdvd (ZMod (p^j))).toAddMonoidHom (Fin n)
    have hπ : ∀ y, π y = fun i => (((y i).val : ℤ) : ZMod (p^j)) := by
      intro y; funext i
      change ZMod.castHom hdvd _ (y i) = _
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, Int.cast_natCast]
    have hsurj : Function.Surjective π := by
      intro z
      obtain ⟨y, hy⟩ := (Function.Surjective.comp_left (ZMod.castHom_surjective hdvd) (α := Fin n)) z
      exact ⟨y, hy⟩
    have hiff : ∀ y : Fin n → ZMod (p^(j+1)), ((((p:ℤ)^2 * Q.evalIn ℤ (fun i => ((y i).val : ℤ)) : ℤ) : ZMod (p^(j+2))) = (((p:ℤ)^2 * m' : ℤ) : ZMod (p^(j+2)))) ↔ Q.evalIn (ZMod (p^j)) (π y) = (m' : ZMod (p^j)) := by
      intro y
      rw [hπ, hmap, ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.intCast_eq_intCast_iff_dvd_sub, ← mul_sub]
      push_cast
      rw [pow_add, mul_comm ((p:ℤ)^j), mul_dvd_mul_iff_left hp2]
    have hc := hfiber π hsurj (fun z => Q.evalIn (ZMod (p^j)) z = (m' : ZMod (p^j)))
    have hcard : ∀ N : ℕ, Nat.card (Fin n → ZMod N) = N ^ n := by
      intro N; rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rw [hcard, hcard] at hc
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    unfold repCount
    have hpos : 0 < (p^j)^n := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hc]
    ring
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨y, hy⟩
    apply hm
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hy
    have h2 : (p:ℤ)^2 ∣ m - p^2 * Q.evalIn ℤ (fun i => ((y i).val : ℤ)) :=
      dvd_trans (pow_dvd_pow (p:ℤ) (show 2 ≤ j + 2 by omega)) (by exact_mod_cast hy)
    have := h2.add (dvd_mul_right _ (Q.evalIn ℤ (fun i => ((y i).val : ℤ))))
    simpa using this

end QuadFormsKB.LocalDensity
