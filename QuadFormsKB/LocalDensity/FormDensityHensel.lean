/-
# A counting Hensel lemma for quadratic maps over a DVR

**Layer:** DVR. The engine behind the stabilization of densities of forms by forms (`FormDensityStab.lean`).

**Setting.** $\iota, \kappa$ finite index sets, $F : R^\iota \to R^\kappa$ a *quadratic map* with differential $D$:
$F(\vec x + c\,\vec w) = F(\vec x) + c\, D_{\vec x}(\vec w) + c^2 F(\vec w)$ with $D_{\vec x}$ $R$-linear; a target
$\vec t \in R^\kappa$; $S_N = \{\vec x \in (R/\pi^N)^\iota : F(\vec x) \equiv \vec t \bmod \pi^N\}$.

**Proves** (`card_sol_succ`): if $K \ge 2d + 1$ and the differential at every solution mod $\pi^K$ has image
containing $\pi^d R^\kappa$, then $\#S_{K+1} \cdot q^{|\kappa|} = q^{|\iota|} \cdot \#S_K$.

*Proof* (a multivariable form of Hanke 2004, Lemma 3.2, as in `Lemma32.lean`, and of Siegel's Hilfssatz on
$A_{p^{t+1}} = p^{\ldots} A_{p^t}$ [unverified]). Put $a = K - d$. Group $S_K$ and $S_{K+1}$ by the class mod $\pi^a$
(`fiberSigma`). In a class containing a solution $\vec x_0$ mod $\pi^K$, $F$ is affine on $\vec x_0 + \pi^a R^\iota$
modulo $\pi^{K+1}$ (since $2a \ge K + 1$), so the fibre mod $\pi^K$ is a translate of $\ker(D_{\vec x_0} \bmod \pi^d)$ and
the fibre mod $\pi^{K+1}$ a translate of $\ker(D_{\vec x_0} \bmod \pi^{d+1})$ (the image hypothesis makes the
translate exist). Finally $\#\ker_{d+1}\cdot q^{|\kappa|} = \#\{\vec y \bmod \pi^{d+1} : D\vec y \equiv 0 \bmod \pi^d\}
= \#\ker_d \cdot q^{|\iota|}$ (`card_ker_succ`, `card_succ_of_shift`). Reduction mod $\pi^K$ itself does *not* have
uniform fibres when $d > 0$. No restriction on the residue characteristic: dyadic primes are included.
**Depends on** `FormDensity.lean`.
-/
import QuadFormsKB.LocalDensity.FormDensity

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ι κ : Type*}

/-! ### Reduction and lifting of vectors indexed by an arbitrary type -/

/-- Reduction of an `ι`-vector of `R` mod `π ^ N`. -/
def redI (π : R) (N : ℕ) (x : ι → R) : ι → R ⧸ Ideal.span {π ^ N} :=
  fun i => Ideal.Quotient.mk _ (x i)

/-- A (chosen) lift to `R` of an `ι`-vector mod `π ^ N`. -/
noncomputable def liftI (π : R) (N : ℕ) (x : ι → R ⧸ Ideal.span {π ^ N}) : ι → R :=
  fun i => Function.surjInv Ideal.Quotient.mk_surjective (x i)

theorem redI_liftI (π : R) (N : ℕ) (x : ι → R ⧸ Ideal.span {π ^ N}) : redI π N (liftI π N x) = x := by
  funext i
  exact Function.surjInv_eq Ideal.Quotient.mk_surjective (x i)

theorem redI_eq_iff (π : R) (N : ℕ) (x y : ι → R) :
    redI π N x = redI π N y ↔ ∀ i, π ^ N ∣ x i - y i := by
  simp only [redI, funext_iff, Ideal.Quotient.eq, Ideal.mem_span_singleton]

theorem liftI_redI (π : R) (N : ℕ) (x : ι → R) :
    ∃ w : ι → R, liftI π N (redI π N x) = x + π ^ N • w := by
  have h : ∀ i, π ^ N ∣ liftI π N (redI π N x) i - x i :=
    (redI_eq_iff π N _ _).mp (redI_liftI π N _)
  refine ⟨fun i => Classical.choose (h i), funext fun i => ?_⟩
  have := Classical.choose_spec (h i)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← this]; ring

theorem exists_eq_add_of_redI_eq (π : R) (N : ℕ) {x y : ι → R} (h : redI π N x = redI π N y) :
    ∃ w : ι → R, x = y + π ^ N • w := by
  rw [redI_eq_iff] at h
  refine ⟨fun i => Classical.choose (h i), funext fun i => ?_⟩
  have := Classical.choose_spec (h i)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← this]; ring

/-- A predicate stable under one direction of shifts by `π ^ b R^ι` is stable under both. -/
theorem shift_iff {π : R} {b : ℕ} {P : (ι → R) → Prop} (hP : ∀ x y, P x → P (x + π ^ b • y))
    (x y : ι → R) : P (x + π ^ b • y) ↔ P x := by
  refine ⟨fun h => ?_, hP x y⟩
  have := hP _ (-y) h
  rwa [smul_neg, add_neg_cancel_right] at this

/-- **Fibration over classes mod `π ^ a`** (the sigma form of `fiber_equiv` in `Lemma32.lean`, for `ι`-vectors):
the classes mod `π ^ N` satisfying `P'` are in bijection with pairs (a class `c` mod `π ^ a` satisfying `P`,
a class `y` mod `π ^ b` with `P' (c + π ^ a y)`), `N = a + b`. -/
theorem fiberSigma (π : R) (hπ : π ≠ 0) (a b N : ℕ) (hN : a + b = N)
    (P P' : (ι → R) → Prop)
    (hP : ∀ x y, P x → P (x + π ^ a • y))
    (hP'P : ∀ x, P' x → P x)
    (hP' : ∀ x y, P' x → P' (x + π ^ N • y)) :
    Nonempty ({x : ι → R ⧸ Ideal.span {π ^ N} // P' (liftI π N x)} ≃
      Σ c : {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)},
        {y : ι → R ⧸ Ideal.span {π ^ b} // P' (liftI π a c.1 + π ^ a • liftI π b y)}) := by
  classical
  have hpa : π ^ a ≠ 0 := pow_ne_zero _ hπ
  have hNab : π ^ N = π ^ a * π ^ b := by rw [← hN, pow_add]
  let φ : {x : ι → R ⧸ Ideal.span {π ^ N} // P' (liftI π N x)} →
      {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)} := fun x =>
    ⟨redI π a (liftI π N x.1), by
      obtain ⟨w, hw⟩ := liftI_redI π a (liftI π N x.1)
      rw [hw]; exact hP _ _ (hP'P _ x.2)⟩
  have hfib : ∀ c : {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)},
      Nonempty ({x // φ x = c} ≃
        {y : ι → R ⧸ Ideal.span {π ^ b} // P' (liftI π a c.1 + π ^ a • liftI π b y)}) := by
    intro c
    let ψ : {y : ι → R ⧸ Ideal.span {π ^ b} // P' (liftI π a c.1 + π ^ a • liftI π b y)} →
        {x // φ x = c} := fun y =>
      ⟨⟨redI π N (liftI π a c.1 + π ^ a • liftI π b y.1), by
        obtain ⟨w, hw⟩ := liftI_redI π N (liftI π a c.1 + π ^ a • liftI π b y.1)
        rw [hw]; exact hP' _ _ y.2⟩, by
        apply Subtype.ext
        show redI π a (liftI π N (redI π N _)) = c.1
        obtain ⟨w, hw⟩ := liftI_redI π N (liftI π a c.1 + π ^ a • liftI π b y.1)
        rw [hw]
        refine Eq.trans ((redI_eq_iff π a _ (liftI π a c.1)).mpr fun i => ?_) (redI_liftI π a c.1)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hNab]
        exact ⟨liftI π b y.1 i + π ^ b * w i, by ring⟩⟩
    refine ⟨(Equiv.ofBijective ψ ⟨?_, ?_⟩).symm⟩
    · intro y y' h
      have h1 := congrArg (fun z => z.1.1) h
      simp only [ψ] at h1
      rw [redI_eq_iff] at h1
      apply Subtype.ext
      rw [← redI_liftI π b y.1, ← redI_liftI π b y'.1, redI_eq_iff]
      intro i
      have := h1 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hNab] at this
      rw [show liftI π a c.1 i + π ^ a * liftI π b y.1 i -
          (liftI π a c.1 i + π ^ a * liftI π b y'.1 i) =
          π ^ a * (liftI π b y.1 i - liftI π b y'.1 i) by ring] at this
      exact (mul_dvd_mul_iff_left hpa).mp this
    · rintro ⟨⟨x, hx⟩, hφ⟩
      have h0 : redI π a (liftI π N x) = redI π a (liftI π a c.1) := by
        rw [redI_liftI]; exact congrArg Subtype.val hφ
      rw [redI_eq_iff] at h0
      let w : ι → R := fun i => Classical.choose (h0 i)
      have hw : ∀ i, liftI π N x i = liftI π a c.1 i + π ^ a * w i := fun i => by
        have := Classical.choose_spec (h0 i); rw [← this]; ring
      obtain ⟨w', hw'⟩ := liftI_redI π b w
      have hmem : P' (liftI π a c.1 + π ^ a • liftI π b (redI π b w)) := by
        have : liftI π a c.1 + π ^ a • liftI π b (redI π b w) = liftI π N x + π ^ N • w' := by
          funext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw', hw, hNab]; ring
        rw [this]; exact hP' _ _ hx
      refine ⟨⟨redI π b w, hmem⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show redI π N _ = x
      rw [← redI_liftI π N x, redI_eq_iff]
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw', hw, hNab]
      exact ⟨w' i, by ring⟩
  exact ⟨(Equiv.sigmaFiberEquiv φ).symm.trans (Equiv.sigmaCongrRight fun c => (hfib c).some)⟩

/-- **Translation:** for `P` stable under `π ^ b R^ι`, the classes `y` mod `π ^ b` with `P (y - z)` are in
bijection with those with `P y`. -/
theorem shiftEquiv (π : R) (b : ℕ) (P : (ι → R) → Prop) (hP : ∀ x y, P x → P (x + π ^ b • y))
    (z : ι → R) :
    Nonempty ({y : ι → R ⧸ Ideal.span {π ^ b} // P (liftI π b y - z)} ≃
      {y : ι → R ⧸ Ideal.span {π ^ b} // P (liftI π b y)}) := by
  refine ⟨Equiv.subtypeEquiv (Equiv.subRight (redI π b z)) fun y => ?_⟩
  simp only [Equiv.subRight_apply]
  have h : redI π b (liftI π b (y - redI π b z)) = redI π b (liftI π b y - z) := by
    rw [redI_liftI]
    funext i
    simp only [redI, Pi.sub_apply, map_sub]
    rw [show (Ideal.Quotient.mk _ (liftI π b y i) : R ⧸ Ideal.span {π ^ b}) = y i from
      congrFun (redI_liftI π b y) i]
  obtain ⟨w, hw⟩ := exists_eq_add_of_redI_eq π b h
  rw [hw, shift_iff hP]

/-! ### Counting -/

section Count

variable [Finite (IsLocalRing.ResidueField R)]

theorem finite_vec (π : R) (hπ : Irreducible π) (N : ℕ) [Finite ι] :
    Finite (ι → R ⧸ Ideal.span {π ^ N}) := by
  have := finite_quot_pow π hπ N
  infer_instance

theorem natCard_vec (π : R) (hπ : Irreducible π) (N : ℕ) [Fintype ι] :
    Nat.card (ι → R ⧸ Ideal.span {π ^ N}) = q R ^ (N * Fintype.card ι) := by
  rw [Nat.card_fun, card_quot_pow π hπ, Nat.card_eq_fintype_card, pow_mul]

/-- **Lifting a shift-stable predicate one level:** if `P` is stable under `π ^ d R^ι`, then
$\#\{\vec y \bmod \pi^{d+1} : P\} = \#\{\vec y \bmod \pi^d : P\} \cdot q^{|\iota|}$. -/
theorem card_succ_of_shift [Fintype ι] (π : R) (hπ : Irreducible π) (d : ℕ) (P : (ι → R) → Prop)
    (hP : ∀ x y, P x → P (x + π ^ d • y)) :
    Nat.card {y : ι → R ⧸ Ideal.span {π ^ (d + 1)} // P (liftI π (d + 1) y)} =
      Nat.card {y : ι → R ⧸ Ideal.span {π ^ d} // P (liftI π d y)} * q R ^ Fintype.card ι := by
  classical
  have hP' : ∀ x y, P x → P (x + π ^ (d + 1) • y) := by
    intro x y hx
    rw [pow_succ, mul_smul]; exact hP _ _ hx
  obtain ⟨e⟩ := fiberSigma π hπ.ne_zero d 1 (d + 1) rfl P P hP (fun _ h => h) hP'
  have := finite_vec (ι := ι) π hπ d
  have := finite_vec (ι := ι) π hπ 1
  have e' := e.trans (Equiv.sigmaCongrRight fun c => Equiv.subtypeUnivEquiv fun y => hP _ _ c.2)
  have : Fintype {c : ι → R ⧸ Ideal.span {π ^ d} // P (liftI π d c)} := Fintype.ofFinite _
  rw [Nat.card_congr e', Nat.card_sigma, Finset.sum_const, natCard_vec π hπ 1, one_mul, smul_eq_mul,
    Finset.card_univ, ← Nat.card_eq_fintype_card]

/-- **Kernels one level up** for an $R$-linear $D : R^\iota \to R^\kappa$ whose image contains $\pi^d R^\kappa$:
$\#\{\vec y \bmod \pi^{d+1} : D\vec y \equiv 0 \bmod \pi^d\} = \#\{\vec y \bmod \pi^{d+1} : D\vec y \equiv 0 \bmod \pi^{d+1}\}
\cdot q^{|\kappa|}$. The bijection is $(\vec y, \vec c) \mapsto \vec y + E(\vec c)$ with $D E(\vec c) = \pi^d \vec c$. -/
theorem card_ker_succ [Fintype ι] [Fintype κ] (π : R) (hπ : Irreducible π) (d : ℕ)
    (D : (ι → R) →ₗ[R] (κ → R)) (hD : ∀ c, ∃ w, D w = π ^ d • c) :
    Nat.card {y : ι → R ⧸ Ideal.span {π ^ (d + 1)} // ∀ j, π ^ d ∣ D (liftI π (d + 1) y) j} =
      Nat.card {y : ι → R ⧸ Ideal.span {π ^ (d + 1)} // ∀ j, π ^ (d + 1) ∣ D (liftI π (d + 1) y) j} *
        q R ^ Fintype.card κ := by
  classical
  have hπ0 := hπ.ne_zero
  choose E hE using hD
  -- `D` of a reduced-and-lifted vector
  have hDred : ∀ (N : ℕ) (z : ι → R), ∃ w : ι → R, D (liftI π N (redI π N z)) = D z + π ^ N • D w := by
    intro N z
    obtain ⟨w, hw⟩ := liftI_redI π N z
    exact ⟨w, by rw [hw, map_add, map_smul]⟩
  have hc : ∀ c : κ → R ⧸ Ideal.span {π ^ 1}, ∀ c' : κ → R ⧸ Ideal.span {π ^ 1},
      (∀ j, π ^ (d + 1) ∣ π ^ d * (liftI π 1 c j - liftI π 1 c' j)) → c = c' := by
    intro c c' h
    rw [← redI_liftI π 1 c, ← redI_liftI π 1 c', redI_eq_iff]
    intro j
    have := h j
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)] at this
    simpa using this
  let Φ : {y : ι → R ⧸ Ideal.span {π ^ (d + 1)} // ∀ j, π ^ (d + 1) ∣ D (liftI π (d + 1) y) j} ×
      (κ → R ⧸ Ideal.span {π ^ 1}) →
      {y : ι → R ⧸ Ideal.span {π ^ (d + 1)} // ∀ j, π ^ d ∣ D (liftI π (d + 1) y) j} := fun p =>
    ⟨redI π (d + 1) (liftI π (d + 1) p.1.1 + E (liftI π 1 p.2)), by
      intro j
      obtain ⟨w, hw⟩ := hDred (d + 1) (liftI π (d + 1) p.1.1 + E (liftI π 1 p.2))
      rw [hw, map_add, hE]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine dvd_add (dvd_add ((pow_dvd_pow π (Nat.le_succ d)).trans (p.1.2 j))
        (dvd_mul_right _ _)) ((pow_dvd_pow π (Nat.le_succ d)).trans (dvd_mul_right _ _))⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨⟨y, hy⟩, c⟩ ⟨⟨y', hy'⟩, c'⟩ h
      have h1 := congrArg Subtype.val h
      simp only [Φ] at h1
      obtain ⟨w, hw⟩ := exists_eq_add_of_redI_eq π (d + 1) h1
      have hD1 := congrArg D hw
      rw [map_add, map_add, map_add, map_smul, hE, hE] at hD1
      have hcc : c = c' := by
        apply hc
        intro j
        have := congrFun hD1 j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
        have e2 : π ^ d * (liftI π 1 c j - liftI π 1 c' j) =
            (D (liftI π (d + 1) y') j - D (liftI π (d + 1) y) j) + π ^ (d + 1) * D w j := by
          linear_combination this
        rw [e2]
        exact dvd_add (dvd_sub (hy' j) (hy j)) (dvd_mul_right _ _)
      subst hcc
      have hyy : y = y' := by
        rw [← redI_liftI π (d + 1) y, ← redI_liftI π (d + 1) y', redI_eq_iff]
        intro i
        have := congrFun hw i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
        exact ⟨w i, by linear_combination this⟩
      subst hyy
      rfl
    · rintro ⟨y, hy⟩
      have hy' := hy
      choose g hg using hy'
      have hgD : D (liftI π (d + 1) y) = π ^ d • g := funext fun j => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact hg j
      set c : κ → R ⧸ Ideal.span {π ^ 1} := redI π 1 g
      obtain ⟨v, hv⟩ := liftI_redI π 1 g
      have hy0 : ∀ j, π ^ (d + 1) ∣
          D (liftI π (d + 1) (redI π (d + 1) (liftI π (d + 1) y - E (liftI π 1 c)))) j := by
        intro j
        obtain ⟨w, hw⟩ := hDred (d + 1) (liftI π (d + 1) y - E (liftI π 1 c))
        rw [hw, map_sub, hgD, hE, hv]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        refine ⟨-(v j) + D w j, ?_⟩
        rw [pow_succ]; ring
      refine ⟨⟨⟨_, hy0⟩, c⟩, ?_⟩
      apply Subtype.ext
      simp only [Φ]
      obtain ⟨w, hw⟩ := liftI_redI π (d + 1) (liftI π (d + 1) y - E (liftI π 1 c))
      rw [hw, ← redI_liftI π (d + 1) y, redI_eq_iff, redI_liftI]
      intro i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact ⟨w i, by ring⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod, natCard_vec π hπ 1, one_mul]

end Count

/-! ### The counting Hensel lemma -/

section Hensel

variable [Finite (IsLocalRing.ResidueField R)] [Fintype ι] [Fintype κ]

/-- **Counting Hensel lemma for quadratic maps** (multivariable Hanke 2004, Lemma 3.2; Siegel 1935,
Hilfssatz 13 [unverified]). Let $F : R^\iota \to R^\kappa$ satisfy
$F(\vec x + c\vec w) = F(\vec x) + c\,D_{\vec x}\vec w + c^2 F(\vec w)$ with $D_{\vec x}$ linear, let $\vec t \in R^\kappa$,
$K \ge 2d + 1$, and suppose that at every $\vec x$ with $F(\vec x) \equiv \vec t \bmod \pi^K$ the image of $D_{\vec x}$
contains $\pi^d R^\kappa$. Then the solution counts satisfy $\#S_{K+1}\, q^{|\kappa|} = q^{|\iota|}\, \#S_K$. -/
@[kb "siegel1935" "Hilfssatz 13 [unverified]"]
theorem card_sol_succ (π : R) (hπ : Irreducible π) (F : (ι → R) → (κ → R))
    (D : (ι → R) → (ι → R) →ₗ[R] (κ → R))
    (hF : ∀ x w (c : R), F (x + c • w) = F x + c • D x w + c ^ 2 • F w) (t : κ → R) (d K : ℕ)
    (hK : 2 * d + 1 ≤ K)
    (hD : ∀ x, (∀ j, π ^ K ∣ F x j - t j) → ∀ c, ∃ w, D x w = π ^ d • c) :
    Nat.card {x : ι → R ⧸ Ideal.span {π ^ (K + 1)} // ∀ j, π ^ (K + 1) ∣ F (liftI π (K + 1) x) j - t j} *
        q R ^ Fintype.card κ =
      q R ^ Fintype.card ι *
        Nat.card {x : ι → R ⧸ Ideal.span {π ^ K} // ∀ j, π ^ K ∣ F (liftI π K x) j - t j} := by
  classical
  have hπ0 := hπ.ne_zero
  set Sol : ℕ → (ι → R) → Prop := fun N x => ∀ j, π ^ N ∣ F x j - t j with hSol
  have hSolShift : ∀ N x y, Sol N x → Sol N (x + π ^ N • y) := by
    intro N x y hx j
    rw [hF]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show F x j + π ^ N * D x y j + (π ^ N) ^ 2 * F y j - t j =
      (F x j - t j) + π ^ N * (D x y j + π ^ N * F y j) by ring]
    exact dvd_add (hx j) (dvd_mul_right _ _)
  set a := K - d with ha
  have hKa : K = a + d := by omega
  set P : (ι → R) → Prop := fun x => ∃ y, Sol K (x + π ^ a • y) with hPdef
  have hP : ∀ x y, P x → P (x + π ^ a • y) := by
    rintro x y ⟨y', hy'⟩
    refine ⟨y' - y, ?_⟩
    convert hy' using 1
    funext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hKP : ∀ x, Sol K x → P x := fun x hx => ⟨0, by simpa using hx⟩
  have hK1K : ∀ x, Sol (K + 1) x → Sol K x := fun x hx j => (pow_dvd_pow π (Nat.le_succ K)).trans (hx j)
  obtain ⟨eK⟩ := fiberSigma π hπ0 a d K hKa.symm P (Sol K) hP hKP (hSolShift K)
  obtain ⟨eK1⟩ := fiberSigma π hπ0 a (d + 1) (K + 1) (by omega) P (Sol (K + 1)) hP
    (fun x hx => hKP x (hK1K x hx)) (hSolShift (K + 1))
  have := finite_vec (ι := ι) π hπ a
  have := finite_vec (ι := ι) π hπ d
  have := finite_vec (ι := ι) π hπ (d + 1)
  -- the per-class identity
  have hclass : ∀ c : {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)},
      Nat.card {y : ι → R ⧸ Ideal.span {π ^ (d + 1)} //
          Sol (K + 1) (liftI π a c.1 + π ^ a • liftI π (d + 1) y)} * q R ^ Fintype.card κ =
        q R ^ Fintype.card ι * Nat.card {y : ι → R ⧸ Ideal.span {π ^ d} //
          Sol K (liftI π a c.1 + π ^ a • liftI π d y)} := by
    rintro ⟨c, y0, hy0⟩
    set x0 := liftI π a c + π ^ a • y0 with hx0
    choose τ hτ using hy0
    obtain ⟨w0, hw0⟩ := hD x0 (fun j => ⟨τ j, hτ j⟩) τ
    have hexp : ∀ v : ι → R, liftI π a c + π ^ a • v = x0 + π ^ a • (v - y0) := by
      intro v; funext i; simp only [hx0, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hFexp : ∀ (v : ι → R) (j : κ), F (liftI π a c + π ^ a • v) j - t j =
        π ^ K * τ j + π ^ a * D x0 (v - y0) j + (π ^ a) ^ 2 * F (v - y0) j := by
      intro v j
      rw [hexp, hF]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination hτ j
    have hpow : ∀ e, π ^ (a + e) = π ^ a * π ^ e := fun e => pow_add π a e
    -- the condition mod π^K
    have hcondK : ∀ v : ι → R, Sol K (liftI π a c + π ^ a • v) ↔
        (fun u => ∀ j, π ^ d ∣ D x0 u j) (v - y0) := by
      intro v
      simp only [hSol, hFexp]
      refine forall_congr' fun j => ?_
      rw [add_assoc, dvd_add_right (dvd_mul_right _ _), dvd_add_left
        ((pow_dvd_pow π (by omega : K ≤ 2 * a)).trans (by rw [pow_mul']; exact dvd_mul_right _ _)),
        hKa, hpow, mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)]
    have hcondK1 : ∀ v : ι → R, Sol (K + 1) (liftI π a c + π ^ a • v) ↔
        (fun u => ∀ j, π ^ (d + 1) ∣ D x0 u j) (v - (y0 - w0)) := by
      intro v
      simp only [hSol, hFexp]
      refine forall_congr' fun j => ?_
      have hsplit : π ^ K * τ j + π ^ a * D x0 (v - y0) j = π ^ a * D x0 (v - (y0 - w0)) j := by
        rw [show v - (y0 - w0) = (v - y0) + w0 by abel, map_add, hw0, hKa, pow_add]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [dvd_add_left ((pow_dvd_pow π (by omega : K + 1 ≤ 2 * a)).trans
        (by rw [pow_mul']; exact dvd_mul_right _ _)), hsplit,
        show K + 1 = a + (d + 1) by omega, hpow, mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)]
    have hstab : ∀ e, ∀ x y : ι → R, (∀ j, π ^ e ∣ D x0 x j) → ∀ j, π ^ e ∣ D x0 (x + π ^ e • y) j := by
      intro e x y hx j
      rw [map_add, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact dvd_add (hx j) (dvd_mul_right _ _)
    obtain ⟨sK⟩ := shiftEquiv π d (fun u => ∀ j, π ^ d ∣ D x0 u j) (hstab d) y0
    obtain ⟨sK1⟩ := shiftEquiv π (d + 1) (fun u => ∀ j, π ^ (d + 1) ∣ D x0 u j) (hstab (d + 1)) (y0 - w0)
    rw [Nat.card_congr ((Equiv.subtypeEquivRight fun y => hcondK1 _).trans sK1),
      Nat.card_congr ((Equiv.subtypeEquivRight fun y => hcondK _).trans sK)]
    have hA := card_succ_of_shift (ι := ι) π hπ d (fun u => ∀ j, π ^ d ∣ D x0 u j) (hstab d)
    have hB := card_ker_succ π hπ d (D x0) (hD x0 (fun j => ⟨τ j, hτ j⟩))
    rw [← hB, hA, mul_comm]
  -- sum over the classes
  have : ∀ c : {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)},
      Finite {y : ι → R ⧸ Ideal.span {π ^ (d + 1)} //
        Sol (K + 1) (liftI π a c.1 + π ^ a • liftI π (d + 1) y)} := fun _ => inferInstance
  have : ∀ c : {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)},
      Finite {y : ι → R ⧸ Ideal.span {π ^ d} // Sol K (liftI π a c.1 + π ^ a • liftI π d y)} :=
    fun _ => inferInstance
  have : Fintype {c : ι → R ⧸ Ideal.span {π ^ a} // P (liftI π a c)} := Fintype.ofFinite _
  rw [Nat.card_congr eK1, Nat.card_congr eK, Nat.card_sigma, Nat.card_sigma, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => hclass c

end Hensel

end QuadFormsKB.LocalDensity.DVR
