/-
# Local densities over a DVR: 1-dimensional and binary unimodular blocks at dyadic primes (Plan A1–A2)

**Layer:** DVR ($R$ a discrete valuation ring with uniformizer $\pi$, finite residue field of size $q$, $2 \ne 0$,
$e = \mathrm{ord}_\pi 2$, so $2 = \pi^e v$ with $v$ a unit). At a **dyadic** prime ($e \ge 1$, $q = 2^f$) these are the
blocks that force $\pi \mid N$: a 1-dimensional block $u x^2$ has level $\pi^{2e}$, and a binary block
$ax^2 + bxy + cy^2$ with $b = \pi^\mu\beta$, $\mu \ge 1$ has level $\pi^{2\mu}$ (`DVRLevelBlocks.lean`).

**A1 (1-dimensional blocks, diagonal forms).**
* `DVR.localDensity_unit_diag`: for $Q = \langle u_0, \dots, u_{n-1}\rangle$ with all $u_i$ units and $m$ a unit,
  $\beta_\pi(m) = r_{\pi^{2e+1}}(m)/q^{(2e+1)(n-1)}$ — a count over $(R/\pi^{2e+1})^n$ (Lemma 3.2 at $t = e$).
* What it depends on: $u_i$ and $m$ only **mod $\pi^{2e+1}$** (`DVR.repCount_congr_coeff`,
  `DVR.localDensity_unit_diag_congr`) and only through their **square classes** (`DVR.repCount_diag_mul_sq`,
  `DVR.repCount_mul_sq_unit`, `DVR.localDensity_diag_mul_sq`, `DVR.localDensity_mul_sq_unit`); over a number field the
  unit square classes are exactly the classes mod $\pi^{2e+1}$ (local square theorem; `NFDyadicBad.lean`).
* **Closed form for $n = 1$** (`DVR.repCount_unary_eq`, `DVR.localDensity_unary_unit`, `DVR.localDensity_unary`): for
  $u$ a unit and $\pi^a \,\|\, m$,
  $$\beta_\pi(u x^2;\, m) = \begin{cases} 2\,q^{\,e + a/2} & a \text{ even and } m/(u\pi^a) \text{ is a square mod } \pi^{2e+1},\\
  0 & \text{otherwise.}\end{cases}$$
  The key step is `DVR.dvd_sq_sub_sq_iff`: for $y$ a unit, $x^2 \equiv y^2 \pmod{\pi^{2e+1}}$ iff $x \equiv \pm y \pmod{\pi^{e+1}}$,
  two distinct classes, each with $q^e$ lifts. At $\pi \nmid 2$ ($e = 0$) this is the familiar $1 + \chi(m/u)$. For
  complete $R$ (e.g. $\mathfrak o_\mathfrak p$) and $\pi \mid 2$, "square mod $\pi^{2e+1}$" is "square in $R$"
  (`DVR.isSquare_of_pow_dvd_sub_one`: $U^{(2e+1)} \subseteq R^{\times 2}$, the local square theorem;
  `DVR.localDensity_unary_unit_complete`, `DVR.localDensity_unary_complete`).

**A2 (binary blocks with $1 \le \mu \le e$).** `DVR.isJordanFormW_binForm`, `DVR.gradBound_binForm`: a block
$ax^2 + bxy + cy^2$ with norm exponent $0$ and $b = \pi^\mu\beta$ is a normal form with gradient bound $\mu$, so its
Good-type counts are determined at level $2\mu + 1$ and (`DVR.localDensity_unit_binForm`)
$\beta_\pi(m) = r_{\pi^{2\mu+1}}(m)/q^{2\mu+1}$ for units $m$, depending only on $a, b, c, m \bmod \pi^{2\mu+1}$
(`DVR.localDensity_unit_binForm_congr`). For $\mu = 0$ this is level $1$ (`DVRDyadicTable.lean`).

**Depends on** `DyadicClosed.lean`, `DyadicArf.lean` (Hensel–Artin–Schreier, for the complete case).
-/
import QuadFormsKB.LocalDensity.DyadicClosed
import QuadFormsKB.LocalDensity.DyadicArf

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-! ### Counts depend only on the coefficients and $m$ mod $\pi^K$; square classes -/

/-- **Counts mod $\pi^K$ depend only on the coefficients and $m$ mod $\pi^K$**: if $c_{ij} \equiv c'_{ij}$ and
$m \equiv m' \pmod{\pi^K}$, then $r_{\pi^K}(Q, m) = r_{\pi^K}(Q', m')$, for every type predicate. -/
theorem repCountOf_congr_coeff (Q Q' : QuadForm R n) (π : R) (K : ℕ)
    (hc : ∀ i j, π ^ K ∣ Q.coeff i j - Q'.coeff i j) {m m' : R} (hm : π ^ K ∣ m - m')
    (T : (Fin n → R ⧸ Ideal.span {π ^ K}) → Prop) :
    repCountOf Q π K m T = repCountOf Q' π K m' T := by
  have hev : ∀ x : Fin n → R ⧸ Ideal.span {π ^ K},
      Q.evalIn (R ⧸ Ideal.span {π ^ K}) x = Q'.evalIn (R ⧸ Ideal.span {π ^ K}) x := by
    intro x
    unfold QuadForm.evalIn
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Ideal.Quotient.algebraMap_eq, (mk_eq_mk_iff π K _ _).2 (hc i j)]
  have hmm : Ideal.Quotient.mk (Ideal.span {π ^ K}) m = Ideal.Quotient.mk _ m' := (mk_eq_mk_iff π K _ _).2 hm
  unfold repCountOf
  simp only [hev, hmm]

/-- Total counts version of `repCountOf_congr_coeff`. -/
theorem repCount_congr_coeff (Q Q' : QuadForm R n) (π : R) (K : ℕ)
    (hc : ∀ i j, π ^ K ∣ Q.coeff i j - Q'.coeff i j) {m m' : R} (hm : π ^ K ∣ m - m') :
    repCount Q π K m = repCount Q' π K m' := by
  have h := repCountOf_congr_coeff Q Q' π K hc hm (fun _ => True)
  unfold repCountOf at h; unfold repCount
  simpa using h

/-- **Square classes of the coefficients**: $\langle a_i s_i^2\rangle$ and $\langle a_i\rangle$ have the same counts at every
level when all $s_i$ are units (the change of variables $x_i \mapsto s_i x_i$). -/
theorem repCount_diag_mul_sq (a s : Fin n → R) (hs : ∀ i, IsUnit (s i)) (π : R) (k : ℕ) (m : R) :
    repCount (QuadForm.diag fun i => a i * s i ^ 2) π k m = repCount (QuadForm.diag a) π k m := by
  refine dvr_repCount_eq_of_unimodular _ _ (Matrix.diagonal s) π ?_ (fun x => ?_) k m
  · rw [Matrix.det_diagonal]; exact IsUnit.prod_univ_iff.2 hs
  · show (QuadForm.diag _).evalIn R x = (QuadForm.diag a).evalIn R _
    rw [evalIn_diag, evalIn_diag]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mulVec_diagonal]; ring

/-- **Square classes of $m$**: $r_{\pi^k}(t^2 m) = r_{\pi^k}(m)$ for a unit $t$ (the bijection $\vec x \mapsto t\vec x$). -/
theorem repCount_mul_sq_unit (Q : QuadForm R n) (π : R) (k : ℕ) {t : R} (ht : IsUnit t) (m : R) :
    repCount Q π k (t ^ 2 * m) = repCount Q π k m := by
  set A := R ⧸ Ideal.span {π ^ k}
  set τ : A := Ideal.Quotient.mk _ t
  have hτ : IsUnit τ := ht.map _
  obtain ⟨τ', hτ'⟩ := hτ.exists_right_inv
  have hτ'' : τ' * τ = 1 := by rw [mul_comm]; exact hτ'
  let f : (Fin n → A) ≃ (Fin n → A) :=
    { toFun := fun x i => τ * x i
      invFun := fun x i => τ' * x i
      left_inv := fun x => by funext i; simp only; rw [← mul_assoc, hτ'', one_mul]
      right_inv := fun x => by funext i; simp only; rw [← mul_assoc, hτ', one_mul] }
  unfold repCount
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv f fun x => ?_)
  show _ ↔ Q.evalIn A (fun i => τ * x i) = _
  rw [evalIn_const_mul, map_mul, map_pow]
  constructor
  · intro h; rw [h]
  · intro h
    exact (hτ.pow 2).mul_left_cancel h

/-! ### A1: unit densities of diagonal forms at level $2e + 1$ -/

section Diag

variable [Finite (IsLocalRing.ResidueField R)]

/-- **Unit densities of unit diagonal forms at every prime** (Hanke 2004, Remark 3.4.1(a), p. 361, and Lemma 3.2 at
$t = e$; the dyadic "mod $4\mathfrak p$" of p. 359): for $Q = \langle u_0, \dots, u_{n-1}\rangle$, all $u_i$ units, and $m$ a
unit, $\beta_\pi(m) = r_{\pi^{2e+1}}(m)/q^{(2e+1)(n-1)}$. At a dyadic prime every $u_i x_i^2$ is a 1-dimensional unimodular
block, the case where Hanke 2004, p. 362 leaves the computation to "a case-by-case basis". -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361; Lemma 3.2, p. 358 (dyadic, 1-dimensional blocks)"]
theorem localDensity_unit_diag (u : Fin n → R) (π : R) (hπ : Irreducible π) (hu : ∀ i, ¬ π ∣ u i) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {m : R} (hm : ¬ π ∣ m) :
    localDensity (QuadForm.diag u) π m =
      (repCount (QuadForm.diag u) π (2 * e + 1) m : ℝ) / (q R : ℝ) ^ ((2 * e + 1) * (n - 1)) := by
  have hJ := isJordanFormW_diag_unit u hπ hu
  exact localDensity_unit_unimodular _ π hπ ∅ hJ e (gradBound_ord_two hJ e he) m hm _ le_rfl

/-- **The unit densities of a unit diagonal form depend only on the $u_i$ and $m$ mod $\pi^{2e+1}$.** -/
theorem localDensity_unit_diag_congr (u u' : Fin n → R) (π : R) (hπ : Irreducible π) (hu : ∀ i, ¬ π ∣ u i)
    (hu' : ∀ i, ¬ π ∣ u' i) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2)
    (huu : ∀ i, π ^ (2 * e + 1) ∣ u i - u' i) {m m' : R} (hm : ¬ π ∣ m) (hm' : ¬ π ∣ m')
    (hmm : π ^ (2 * e + 1) ∣ m - m') :
    localDensity (QuadForm.diag u) π m = localDensity (QuadForm.diag u') π m' := by
  rw [localDensity_unit_diag u π hπ hu e he hm, localDensity_unit_diag u' π hπ hu' e he hm',
    repCount_congr_coeff _ _ π _ (fun i j => ?_) hmm]
  simp only [QuadForm.diag, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact huu i
  · simp

/-- **Densities depend only on the square classes of the coefficients**: $\beta_\pi(\langle a_i s_i^2\rangle, m) =
\beta_\pi(\langle a_i\rangle, m)$ for units $s_i$ (any $a_i$, any $m$). -/
theorem localDensity_diag_mul_sq (a s : Fin n → R) (hs : ∀ i, IsUnit (s i)) (π : R) (m : R) :
    localDensity (QuadForm.diag fun i => a i * s i ^ 2) π m = localDensity (QuadForm.diag a) π m := by
  unfold localDensity
  simp only [repCount_diag_mul_sq a s hs]

/-- **Densities depend only on the square class of $m$**: $\beta_\pi(t^2 m) = \beta_\pi(m)$ for a unit $t$ (any $Q$). -/
theorem localDensity_mul_sq_unit (Q : QuadForm R n) (π : R) {t : R} (ht : IsUnit t) (m : R) :
    localDensity Q π (t ^ 2 * m) = localDensity Q π m := by
  unfold localDensity
  simp only [repCount_mul_sq_unit Q π _ ht]

end Diag

/-! ### A1: the closed form for $n = 1$ -/

/-- **Square roots mod $\pi^{2e+1}$** (the dyadic heart of the 1-dimensional case): for $2 = \pi^e v$ with $v$ a unit and
$y$ a unit, $\pi^{2e+1} \mid (X - y)(X + y)$ iff $X \equiv y$ or $X \equiv -y \pmod{\pi^{e+1}}$. *Proof:* write
$X - y = \pi^s\zeta$; then $X + y = \pi^s\zeta + \pi^e vy$; if $s < e$ the product has valuation $2s < 2e + 1$, and if $s = e$ the
product is $\pi^{2e}\zeta(\zeta + vy)$, so $\pi \mid \zeta + vy$, i.e. $\pi^{e+1} \mid X + y$. -/
theorem dvd_sq_sub_sq_iff {π : R} (hπ : Irreducible π) {e : ℕ} {v : R} (h2 : 2 = π ^ e * v)
    {X y : R} :
    π ^ (2 * e + 1) ∣ (X - y) * (X + y) ↔ π ^ (e + 1) ∣ X - y ∨ π ^ (e + 1) ∣ X - (-y) := by
  have hsum : X + y = (X - y) + π ^ e * (v * y) := by rw [← mul_assoc, ← h2]; ring
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h1'⟩ := hcon
    have hz : X - y ≠ 0 := fun h0 => h1 (h0 ▸ dvd_zero _)
    obtain ⟨s, ζ, hζ, hζu⟩ := dvr_eq_pow_mul_unit hπ hz
    have hs : s ≤ e := by
      by_contra hlt
      exact h1 (hζ ▸ dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) ζ)
    by_cases hse : s = e
    · subst hse
      have hprod : (X - y) * (X + y) = π ^ (2 * s) * (ζ * (ζ + v * y)) := by rw [hsum, hζ]; ring
      rw [hprod, pow_succ] at h
      have h3 : π ∣ ζ * (ζ + v * y) := (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 h
      have h4 : π ∣ ζ + v * y := (hπ.prime.dvd_or_dvd h3).resolve_left (dvr_not_dvd_of_isUnit hπ hζu)
      apply h1'
      rw [sub_neg_eq_add, hsum, hζ, show π ^ s * ζ + π ^ s * (v * y) = π ^ s * (ζ + v * y) by ring, pow_succ]
      exact mul_dvd_mul_left _ h4
    · obtain ⟨d, hd⟩ : ∃ d, e = s + (d + 1) := ⟨e - s - 1, by omega⟩
      have hu : IsUnit (ζ + π ^ (d + 1) * (v * y)) := by
        refine dvr_isUnit_of_not_dvd hπ fun hd' => dvr_not_dvd_of_isUnit hπ hζu ?_
        have := dvd_sub hd' (show π ∣ π ^ (d + 1) * (v * y) from
          dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _)
        rwa [add_sub_cancel_right] at this
      have hprod : (X - y) * (X + y) = π ^ (2 * s) * (ζ * (ζ + π ^ (d + 1) * (v * y))) := by
        rw [hsum, hζ, hd, pow_add]; ring
      rw [hprod] at h
      exact dvr_not_pow_succ_dvd hπ (hζu.mul hu) (2 * s) ((pow_dvd_pow π (by omega)).trans h)
  · rintro (h | h)
    · have h' : π ^ e ∣ X + y := by
        rw [hsum]; exact dvd_add ((pow_dvd_pow π (by omega)).trans h) (dvd_mul_right _ _)
      rw [show 2 * e + 1 = (e + 1) + e by ring, pow_add]; exact mul_dvd_mul h h'
    · rw [sub_neg_eq_add] at h
      have h' : π ^ e ∣ X - y := by
        have : X - y = (X + y) - π ^ e * (v * y) := by rw [hsum]; ring
        rw [this]; exact dvd_sub ((pow_dvd_pow π (by omega)).trans h) (dvd_mul_right _ _)
      rw [show 2 * e + 1 = e + (e + 1) by ring, pow_add]; exact mul_dvd_mul h' h

/-- The value of a 1-dimensional form: $\langle u\rangle(x) = u x_0^2$. -/
theorem evalIn_unary {S : Type*} [CommRing S] [Algebra R S] (u : R) (x : Fin 1 → S) :
    (QuadForm.diag ![u]).evalIn S x = algebraMap R S u * x 0 ^ 2 := by
  rw [evalIn_diag, Fin.sum_univ_one]; rfl

/-- `repCount` of a 1-dimensional form as a count over $R/\pi^k$ itself. -/
theorem repCount_unary_eq_card (u : R) (π : R) (k : ℕ) (m : R) :
    repCount (QuadForm.diag ![u]) π k m = Nat.card {z : R ⧸ Ideal.span {π ^ k} //
      Ideal.Quotient.mk _ u * z ^ 2 = Ideal.Quotient.mk _ m} := by
  unfold repCount
  refine Nat.card_congr ((Equiv.funUnique (Fin 1) _).subtypeEquiv fun x => ?_)
  rw [evalIn_unary, Ideal.Quotient.algebraMap_eq]
  rfl

section Unary

variable [Finite (IsLocalRing.ResidueField R)]

/-- **The 1-dimensional count at level $2e+1$** (dyadic or not): for $u, y$ units with $u y^2 \equiv m \pmod{\pi^{2e+1}}$,
$r_{\pi^{2e+1}}(u x^2;\, m) = 2q^e$ (the classes $x \equiv \pm y \bmod \pi^{e+1}$, each with $q^e$ lifts). -/
theorem repCount_unary_eq (π : R) (hπ : Irreducible π) {e : ℕ} {v : R} (hv : IsUnit v) (h2 : 2 = π ^ e * v)
    {u m y : R} (hu : IsUnit u) (hy : IsUnit y) (hsol : π ^ (2 * e + 1) ∣ u * y ^ 2 - m) :
    repCount (QuadForm.diag ![u]) π (2 * e + 1) m = 2 * q R ^ e := by
  classical
  have hπ0 := hπ.ne_zero
  set K := 2 * e + 1
  set N := e + 1
  set c : R ⧸ Ideal.span {π ^ K} → R ⧸ Ideal.span {π ^ N} := coordMap π K 0 N
  have hc : ∀ z, c z = Ideal.Quotient.mk _ (qlift z) := fun z => by
    simp only [c, coordMap, divPow_zero]
  have key : ∀ z : R ⧸ Ideal.span {π ^ K}, (Ideal.Quotient.mk _ u * z ^ 2 = Ideal.Quotient.mk _ m) ↔
      (c z = Ideal.Quotient.mk _ y ∨ c z = Ideal.Quotient.mk _ (-y)) := by
    intro z
    rw [hc, mk_eq_mk_iff, mk_eq_mk_iff, ← dvd_sq_sub_sq_iff hπ h2]
    conv_lhs => rw [← mk_qlift z, ← map_pow, ← map_mul, mk_eq_mk_iff]
    have e1 : u * qlift z ^ 2 - m = u * ((qlift z - y) * (qlift z + y)) + (u * y ^ 2 - m) := by ring
    rw [e1, dvd_add_left hsol, hu.dvd_mul_left]
  have hne : (Ideal.Quotient.mk (Ideal.span {π ^ N}) y) ≠ Ideal.Quotient.mk _ (-y) := by
    rw [Ne, mk_eq_mk_iff, sub_neg_eq_add, ← two_mul, h2, pow_succ, mul_assoc]
    intro hd
    exact dvr_not_dvd_of_isUnit hπ (hv.mul hy) ((mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)).1 hd)
  have hfib : ∀ b, Nat.card {z // c z = b} = q R ^ e := by
    intro b
    obtain ⟨f⟩ := coordFibre_nonempty π hπ0 (K := K) N 0 e (by omega) b
    rw [← natCard_quot_pow π hπ e, ← Nat.card_congr f]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun z => by simp only [pow_zero, one_dvd, true_and]; rfl)
  have := finite_quot_pow π hπ K
  rw [repCount_unary_eq_card, Nat.card_congr (Equiv.subtypeEquivRight key),
    natCard_split _ (fun z => c z = Ideal.Quotient.mk _ y) (fun z => c z = Ideal.Quotient.mk _ (-y))
      (fun z => c z = Ideal.Quotient.mk _ y) (fun z => by tauto)
      (fun z => by constructor <;> intro h <;> [exact ⟨Or.inr h, fun h' => hne (h'.symm.trans h)⟩;
        exact h.1.resolve_left h.2]),
    hfib, hfib]
  ring

/-- No solutions of $u x^2 \equiv m \pmod{\pi^K}$ when $m/u$ is not a square mod $\pi^K$. -/
theorem repCount_unary_eq_zero (u π : R) (K : ℕ) {m : R} (hno : ¬ ∃ y, π ^ K ∣ u * y ^ 2 - m) :
    repCount (QuadForm.diag ![u]) π K m = 0 := by
  rw [repCount_unary_eq_card, Nat.card_eq_zero]; left
  refine ⟨fun ⟨z, hz⟩ => hno ⟨qlift z, ?_⟩⟩
  rw [← mk_qlift z, ← map_pow, ← map_mul, mk_eq_mk_iff] at hz
  exact hz

open Classical in
/-- **The 1-dimensional count at level $2e+1$, unit $m$**: $r_{\pi^{2e+1}}(ux^2;\, m) = 2q^e$ if $m/u$ is a square mod
$\pi^{2e+1}$, else $0$. -/
theorem repCount_unary_unit (π : R) (hπ : Irreducible π) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2)
    {u m : R} (hu : ¬ π ∣ u) (hm : ¬ π ∣ m) :
    repCount (QuadForm.diag ![u]) π (2 * e + 1) m =
      if ∃ y, π ^ (2 * e + 1) ∣ u * y ^ 2 - m then 2 * q R ^ e else 0 := by
  split_ifs with h
  · obtain ⟨y, hy⟩ := h
    obtain ⟨v, hv2, hv⟩ := dvr_exact hπ he.1 he.2
    refine repCount_unary_eq π hπ hv hv2 (dvr_isUnit_of_not_dvd hπ hu) (dvr_isUnit_of_not_dvd hπ fun hpy => hm ?_) hy
    have h1 : π ∣ u * y ^ 2 - m := (dvd_pow_self π (by omega)).trans hy
    have h2 : π ∣ u * y ^ 2 := dvd_mul_of_dvd_right (dvd_pow hpy (by norm_num)) u
    have := dvd_sub h2 h1
    rwa [sub_sub_cancel] at this
  · exact repCount_unary_eq_zero u π _ h

open Classical in
/-- **$\beta_\pi(u x^2;\, m)$ for a unit $m$, every prime** (dyadic of any ramification included): with $e = \mathrm{ord}_\pi 2$,
$$\beta_\pi(m) = \begin{cases} 2q^e & m/u \text{ is a square mod } \pi^{2e+1},\\ 0 & \text{otherwise.}\end{cases}$$
At $\pi \nmid 2$ this is $1 + \left(\frac{m/u}{\pi}\right)$; at $\mathbb Z_2$ it is $4$ or $0$ ($m/u \equiv 1 \bmod 8$ or not). Over a
number field "square mod $\pi^{2e+1}$" is "square in $F_\mathfrak p$" (`NF.localDensity_unary_unit`). -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361; p. 362 (dyadic case-by-case: n = 1, closed form)"]
theorem localDensity_unary_unit (π : R) (hπ : Irreducible π) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2)
    {u m : R} (hu : ¬ π ∣ u) (hm : ¬ π ∣ m) :
    localDensity (QuadForm.diag ![u]) π m =
      if ∃ y, π ^ (2 * e + 1) ∣ u * y ^ 2 - m then 2 * (q R : ℝ) ^ e else 0 := by
  have hu' : ∀ i, ¬ π ∣ (![u] : Fin 1 → R) i := fun i => by fin_cases i; exact hu
  rw [localDensity_unit_diag _ π hπ hu' e he hm, repCount_unary_unit π hπ e he hu hm]
  split_ifs <;> simp

/-- $\pi^{a-b} \mid m/\pi^b$ when $\pi^a \mid m$ and $b \le a$. -/
theorem pow_dvd_divPow {π : R} (hπ : π ≠ 0) {a b : ℕ} {m : R} (hb : b ≤ a) (h : π ^ a ∣ m) :
    π ^ (a - b) ∣ divPow π b m := by
  have hm := eq_mul_divPow ((pow_dvd_pow π hb).trans h)
  rw [hm, show a = b + (a - b) by omega, pow_add] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero b hπ)).1 h

/-- $m/\pi^a$ is a unit when $\pi^a \,\|\, m$. -/
theorem not_dvd_divPow_self {π : R} {a : ℕ} {m : R} (hda : π ^ a ∣ m) (ha : ¬ π ^ (a + 1) ∣ m) :
    ¬ π ∣ divPow π a m := fun h => ha (by
  rw [eq_mul_divPow hda, pow_succ]; exact mul_dvd_mul_left _ h)

/-- For a unit $u$ and $\pi \mid m$ there are no primitive solutions of $u x^2 \equiv m \pmod{\pi^k}$, $k \ge 1$. -/
theorem repCountOf_nonZero_unary_of_dvd (π : R) (hπ : Irreducible π) {u m : R} (hu : ¬ π ∣ u) (hm : π ∣ m)
    {k : ℕ} (hk : 1 ≤ k) :
    repCountOf (QuadForm.diag ![u]) π k m (fun x => ¬ IsZeroType π k x) = 0 := by
  unfold repCountOf
  rw [Nat.card_eq_zero]; left
  refine ⟨fun ⟨x, hx, hnz⟩ => hnz fun i => ?_⟩
  fin_cases i
  rw [evalIn_unary, Ideal.Quotient.algebraMap_eq, ← mk_qlift (x 0), ← map_pow, ← map_mul,
    mk_eq_mk_iff] at hx
  have h1 : π ∣ u * qlift (x 0) ^ 2 := by
    have := dvd_add ((dvd_pow_self π (by omega)).trans hx) hm
    rwa [sub_add_cancel] at this
  have h2 : π ∣ qlift (x 0) :=
    hπ.prime.dvd_of_dvd_pow ((hπ.prime.dvd_or_dvd h1).resolve_left hu)
  exact (mk_dvd_iff π hk (x 0)).2 h2

open Classical in
/-- **$\beta_\pi(u x^2;\, m)$ for every $m \ne 0$, every prime** (the closed form of the dyadic recursion for $n = 1$): with
$\pi^a \,\|\, m$ and $e = \mathrm{ord}_\pi 2$,
$$\beta_\pi(m) = \begin{cases} 2q^{\,e + a/2} & a \text{ even and } (m/\pi^a)/u \text{ is a square mod } \pi^{2e+1},\\
0 & \text{otherwise.}\end{cases}$$
*Proof:* `localDensity_eq_dyadicFormula_J` with $L = 0$, $K = 2e + 1$, $c_1 = q$; only the term $j = a/2$ survives. -/
@[kb "hanke2004" "§3, (5.7), p. 369; p. 362 (dyadic, n = 1, closed form)"]
theorem localDensity_unary (π : R) (hπ : Irreducible π) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2)
    {u : R} (hu : ¬ π ∣ u) {a : ℕ} {m : R} (hda : π ^ a ∣ m) (ha : ¬ π ^ (a + 1) ∣ m) :
    localDensity (QuadForm.diag ![u]) π m =
      if Even a ∧ ∃ y, π ^ (2 * e + 1) ∣ u * y ^ 2 - divPow π a m then 2 * (q R : ℝ) ^ (e + a / 2)
      else 0 := by
  have hu' : ∀ i, ¬ π ∣ (![u] : Fin 1 → R) i := fun i => by fin_cases i; exact hu
  have hJ := isJordanFormW_diag_unit _ hπ hu'
  rw [localDensity_eq_dyadicFormula_J _ π hπ ∅ 0 hJ e he 0 (fun _ => le_rfl) (2 * e + 1) (by omega) hda ha,
    dyadicFormula, Finset.sum_range_succ]
  have hzf : zeroFactor R 1 = q R := by simp [zeroFactor]
  have hprim : ∀ m', primDensityAt (QuadForm.diag ![u]) π (2 * e + 1) m' =
      (repCountOf (QuadForm.diag ![u]) π (2 * e + 1) m' (fun x => ¬ IsZeroType π (2 * e + 1) x) : ℝ) := by
    intro m'; simp [primDensityAt]
  have hlow : ∀ j, 2 * j < a → primDensityAt (QuadForm.diag ![u]) π (2 * e + 1) (divPow π (2 * j) m) = 0 := by
    intro j hj
    rw [hprim, repCountOf_nonZero_unary_of_dvd π hπ hu _ (by omega), Nat.cast_zero]
    exact (dvd_pow_self π (by omega)).trans (pow_dvd_divPow hπ.ne_zero hj.le hda)
  rw [Finset.sum_eq_zero fun j hj => by
    rw [Finset.mem_range] at hj; rw [hlow j (by omega), mul_zero], zero_add, hzf]
  by_cases hev : Even a
  · obtain ⟨b, rfl⟩ := hev
    have h2b : 2 * ((b + b) / 2) = b + b := by omega
    have hunit := not_dvd_divPow_self hda ha
    rw [h2b, hprim, ← repCount_eq_nonZero_of_not_dvd _ π hπ (by omega) hunit,
      repCount_unary_unit π hπ e he hu hunit]
    simp only [show (b + b) / 2 = b by omega, Even.add_self, true_and]
    split_ifs <;> push_cast <;> ring
  · have hodd : a % 2 = 1 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hev)
    rw [hlow _ (by omega), mul_zero]
    simp [hev]

end Unary

/-! ### The complete case: square mod $\pi^{2e+1}$ = square -/

/-- **Local square theorem over a complete dyadic DVR** (O'Meara 63:1 [unverified]): if $\pi \mid 2 \ne 0$,
$2 = \pi^e v$ and $x \equiv 1 \pmod{\pi^{2e+1}}$, then $x$ is a square. *Proof:* $x = 1 - 4t$ with $\pi \mid t$
($4 = \pi^{2e}v^2$), and `isSquare_one_sub_four_mul_iff` with $\bar t = 0 = 0^2 + 0$. -/
theorem isSquare_of_pow_dvd_sub_one [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R}
    (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) {e : ℕ} {v : R} (hv : IsUnit v)
    (h2e : 2 = π ^ e * v) {x : R} (hx : π ^ (2 * e + 1) ∣ x - 1) : IsSquare x := by
  obtain ⟨c, hc⟩ := hx
  obtain ⟨w, hw⟩ := (hv.pow 2).exists_right_inv
  set t := -(π * c) * w with ht
  have hx1 : x = 1 - 4 * t := by
    have h4 : (4 : R) = π ^ (2 * e) * v ^ 2 := by
      rw [show (4 : R) = 2 * 2 by norm_num, h2e]; ring
    rw [ht, h4]
    linear_combination hc - (π ^ (2 * e) * (π * c)) * hw
  have hres : IsLocalRing.residue R t = 0 := by
    rw [residue_eq_zero_iff_dvd hπ]
    exact ⟨-(c * w), by rw [ht]; ring⟩
  rw [hx1, isSquare_one_sub_four_mul_iff hπ h2 h20, hres]
  exact ⟨0, by ring⟩

/-- **Square mod $\pi^{2e+1}$ iff square, for units of a complete dyadic DVR**: for units $u, m$,
$(\exists y,\ u y^2 \equiv m \bmod \pi^{2e+1}) \iff (\exists y,\ u y^2 = m)$, i.e. $m/u \in R^{\times 2}$. -/
theorem exists_sq_mod_iff_exists_sq [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R}
    (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2)
    {u m : R} (hu : ¬ π ∣ u) (hm : ¬ π ∣ m) :
    (∃ y, π ^ (2 * e + 1) ∣ u * y ^ 2 - m) ↔ ∃ y, u * y ^ 2 = m := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨v, hv2, hv⟩ := dvr_exact hπ he.1 he.2
    have hyu : IsUnit y := dvr_isUnit_of_not_dvd hπ fun hpy => hm (by
      have h1 : π ∣ u * y ^ 2 - m := (dvd_pow_self π (by omega)).trans hy
      have h2' : π ∣ u * y ^ 2 := dvd_mul_of_dvd_right (dvd_pow hpy (by norm_num)) u
      have := dvd_sub h2' h1
      rwa [sub_sub_cancel] at this)
    have huy : IsUnit (u * y ^ 2) := (dvr_isUnit_of_not_dvd hπ hu).mul (hyu.pow 2)
    obtain ⟨w, hw⟩ := huy.exists_right_inv
    have hx : π ^ (2 * e + 1) ∣ m * w - 1 := by
      have : m * w - 1 = -((u * y ^ 2 - m) * w) := by linear_combination hw
      rw [this, dvd_neg]; exact dvd_mul_of_dvd_left hy w
    obtain ⟨z, hz⟩ := isSquare_of_pow_dvd_sub_one hπ h2 h20 hv hv2 hx
    refine ⟨y * z, ?_⟩
    have : m = m * w * (u * y ^ 2) := by linear_combination -m * hw
    rw [this, hz]; ring
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [hy, sub_self]; exact dvd_zero _⟩

section UnaryComplete

variable [Finite (IsLocalRing.ResidueField R)] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

open Classical in
/-- **$\beta_\pi(u x^2;\, m)$ for a unit $m$ over a complete dyadic DVR** (e.g. $\mathfrak o_\mathfrak p$, $\mathfrak p \mid 2$, any
ramification): $\beta_\pi(m) = 2q^e$ if $m/u$ is a square in $R$, and $0$ otherwise. -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361; p. 362 (dyadic, n = 1, square classes)"]
theorem localDensity_unary_unit_complete (π : R) (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0)
    (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {u m : R} (hu : ¬ π ∣ u) (hm : ¬ π ∣ m) :
    localDensity (QuadForm.diag ![u]) π m = if ∃ y, u * y ^ 2 = m then 2 * (q R : ℝ) ^ e else 0 := by
  rw [localDensity_unary_unit π hπ e he hu hm]
  simp only [exists_sq_mod_iff_exists_sq hπ h2 h20 e he hu hm]

open Classical in
/-- **$\beta_\pi(u x^2;\, m)$ for every $m \ne 0$ over a complete dyadic DVR**: with $\pi^a \,\|\, m$,
$\beta_\pi(m) = 2q^{e + a/2}$ if $a$ is even and $(m/\pi^a)/u$ is a square in $R$, and $0$ otherwise. -/
@[kb "hanke2004" "§3, (5.7), p. 369; p. 362 (dyadic, n = 1, square classes)"]
theorem localDensity_unary_complete (π : R) (hπ : Irreducible π) (h2 : π ∣ 2) (h20 : (2 : R) ≠ 0)
    (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {u : R} (hu : ¬ π ∣ u) {a : ℕ} {m : R} (hda : π ^ a ∣ m)
    (ha : ¬ π ^ (a + 1) ∣ m) :
    localDensity (QuadForm.diag ![u]) π m =
      if Even a ∧ ∃ y, u * y ^ 2 = divPow π a m then 2 * (q R : ℝ) ^ (e + a / 2) else 0 := by
  rw [localDensity_unary π hπ e he hu hda ha]
  simp only [exists_sq_mod_iff_exists_sq hπ h2 h20 e he hu (not_dvd_divPow_self hda ha)]

end UnaryComplete

/-! ### A2: binary blocks with scale exponent $\mu$ -/

/-- **A binary block with norm exponent $0$ is a normal form** (at $\pi \mid 2$): `PairBlockW π 0 a b c` makes
$ax^2 + bxy + cy^2$ a normal form `IsJordanFormW` with the single pair $(0, 1)$ and $w = 0$. -/
theorem isJordanFormW_binForm {π : R} (hπ2 : π ∣ 2) {a b c : R} (h : PairBlockW π 0 a b c) :
    IsJordanFormW (binForm a b c) π {((0 : Fin 2), (1 : Fin 2))} 0 := by
  refine ⟨fun _ => hπ2, by simp, by simp, ?_, ?_, ?_⟩
  · intro i j hij hP
    fin_cases i <;> fin_cases j <;> simp_all
  · intro e he
    simp only [Finset.mem_singleton] at he
    subst he
    exact ⟨rfl, by simpa [binForm] using h⟩
  · intro i hi
    exact absurd (show IsPaired _ i from ⟨(0, 1), by simp, by fin_cases i <;> simp⟩) hi

/-- **Gradient bound $\mu$ for a binary block** with $b = \pi^\mu\beta$, $\beta$ a unit (`GradBound`, `DVRDyadic.lean`): so
Lemma 3.2 holds for it from level $2\mu + 1$ (`DVR.repCountGood_add_of_gradBound`), for every $\mu \le e$. -/
theorem gradBound_binForm {π : R} (hπ : Irreducible π) {a b c β : R} {μ : ℕ} (hb : b = π ^ μ * β)
    (hβ : IsUnit β) : GradBound (binForm a b c) π {((0 : Fin 2), (1 : Fin 2))} 0 μ := by
  refine ⟨fun i _ hi => absurd (show IsPaired _ i from ⟨(0, 1), by simp, by fin_cases i <;> simp⟩) hi, ?_⟩
  intro p hp _
  simp only [Finset.mem_singleton] at hp
  subst hp
  have : (binForm a b c).coeff 0 1 = b := by simp [binForm]
  rw [this, hb]
  exact dvr_not_pow_succ_dvd hπ hβ μ

section Binary

variable [Finite (IsLocalRing.ResidueField R)]

/-- **Unit densities of a binary block at level $2\mu + 1$** (Hanke 2004, Lemma 3.2, p. 358 and Remark 3.4.1(a),
p. 361, at dyadic $\pi$ with the scale exponent of the corrected normal form): for $ax^2 + bxy + cy^2$ with
`PairBlockW π 0 a b c` and $b = \pi^\mu\beta$, $\beta$ a unit, and $m$ a unit,
$$\beta_\pi(m) = \frac{r_{\pi^{2\mu+1}}(m)}{q^{2\mu+1}}.$$
For $\mu = 0$ (unit middle coefficient) this is level $1$ and $\beta_\pi(m) = 1 - \varepsilon/q$
(`DVR.localDensity_unit_pairSum`); for $1 \le \mu \le e$ (possible with $w = 0$ only at ramified dyadic primes,
`DVR.PairBlockW.mu_eq`) the block has level $\pi^{2\mu}$ and the count is needed mod $\pi^{2\mu+1}$. This is the
already recorded update candidate to p. 359 ("since $b$ is a unit, we may even lift these solutions when $k = 1$"; see
`DVR.repCountGood_add_of_gradBound`), made explicit for one block. -/
@[kb "hanke2004" "Lemma 3.2, p. 358; Remark 3.4.1(a), p. 361 (dyadic binary blocks, level 2μ+1)"]
theorem localDensity_unit_binForm (π : R) (hπ : Irreducible π) (hπ2 : π ∣ 2) {a b c β : R} {μ : ℕ}
    (h : PairBlockW π 0 a b c) (hb : b = π ^ μ * β) (hβ : IsUnit β) {m : R} (hm : ¬ π ∣ m) :
    localDensity (binForm a b c) π m = (repCount (binForm a b c) π (2 * μ + 1) m : ℝ) / (q R : ℝ) ^ (2 * μ + 1) := by
  have := localDensity_unit_unimodular (binForm a b c) π hπ _ (isJordanFormW_binForm hπ2 h) μ
    (gradBound_binForm hπ hb hβ) m hm (2 * μ + 1) le_rfl
  simpa using this

/-- **The unit densities of a binary block depend only on $a, b, c, m$ mod $\pi^{2\mu+1}$.** -/
theorem localDensity_unit_binForm_congr (π : R) (hπ : Irreducible π) (hπ2 : π ∣ 2) {a b c a' b' c' β β' : R}
    {μ : ℕ} (h : PairBlockW π 0 a b c) (h' : PairBlockW π 0 a' b' c') (hb : b = π ^ μ * β) (hβ : IsUnit β)
    (hb' : b' = π ^ μ * β') (hβ' : IsUnit β') (ha : π ^ (2 * μ + 1) ∣ a - a') (hbb : π ^ (2 * μ + 1) ∣ b - b')
    (hc : π ^ (2 * μ + 1) ∣ c - c') {m m' : R} (hm : ¬ π ∣ m) (hm' : ¬ π ∣ m')
    (hmm : π ^ (2 * μ + 1) ∣ m - m') :
    localDensity (binForm a b c) π m = localDensity (binForm a' b' c') π m' := by
  rw [localDensity_unit_binForm π hπ hπ2 h hb hβ hm, localDensity_unit_binForm π hπ hπ2 h' hb' hβ' hm',
    repCount_congr_coeff _ _ π _ (fun i j => ?_) hmm]
  fin_cases i <;> fin_cases j <;> simp [binForm, ha, hbb, hc]

end Binary

end QuadFormsKB.LocalDensity.DVR
