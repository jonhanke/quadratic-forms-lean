/-
# Local densities over a DVR: the type decomposition and the reduction maps of §3

**Layer:** DVR. **Proves** over $R$: the decomposition into Zero/Good/Bad types (Hanke 2004, Def. 3.1, p. 358;
`DVR.repCount_eq_add_types`) and the counting identities of the maps $\pi_Z$ (p. 359; `DVR.repCountZero_eq`),
$\pi_{B'}$ and $\pi_{B''}$ (p. 360; `DVR.repCountBadI_eq`, `DVR.repCountBadII_eq`) for $Q$ in normal form
`IsJordanFormW`, with all counts as explicit bijections (finiteness of $R/\pi$ only for the type decomposition).
**Depends on** `DyadicJordan.lean`. The $\mathbb{Q}$ versions are in `Basic.lean`, `Reduction.lean` and
`JordanReduction.lean`.
-/
import QuadFormsKB.LocalDensity.DyadicJordan

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-! ### Counting toolkit over `R ⧸ (π ^ k)` (no finiteness assumed) -/

/-- A chosen lift to $R$ of a class mod $\pi^k$. -/
noncomputable def qlift {π : R} {k : ℕ} (a : R ⧸ Ideal.span {π ^ k}) : R :=
  (Ideal.Quotient.mk_surjective a).choose

theorem mk_qlift {π : R} {k : ℕ} (a : R ⧸ Ideal.span {π ^ k}) :
    Ideal.Quotient.mk _ (qlift a) = a :=
  (Ideal.Quotient.mk_surjective a).choose_spec

/-- Congruence mod $\pi^k$ as divisibility. -/
theorem mk_eq_mk_iff (π : R) (k : ℕ) (a b : R) :
    Ideal.Quotient.mk (Ideal.span {π ^ k}) a = Ideal.Quotient.mk _ b ↔ π ^ k ∣ a - b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

theorem dvd_qlift_mk_sub (π : R) (k : ℕ) (r : R) :
    π ^ k ∣ qlift (Ideal.Quotient.mk (Ideal.span {π ^ k}) r) - r :=
  (mk_eq_mk_iff π k _ _).1 (mk_qlift _)

open Classical in
/-- A chosen quotient $r / \pi^e$ (junk value $0$ if $\pi^e \nmid r$). -/
noncomputable def divPow (π : R) (e : ℕ) (r : R) : R :=
  if h : π ^ e ∣ r then h.choose else 0

theorem eq_mul_divPow {π : R} {e : ℕ} {r : R} (h : π ^ e ∣ r) : r = π ^ e * divPow π e r := by
  rw [divPow, dif_pos h]; exact h.choose_spec

theorem divPow_zero (π r : R) : divPow π 0 r = r := by
  have := eq_mul_divPow (π := π) (e := 0) (r := r) (by simp)
  rw [pow_zero, one_mul] at this
  exact this.symm

/-- The coordinate map $(R/\pi^K) \to (R/\pi^N)$, $a \mapsto (\text{lift}(a)/\pi^e) \bmod \pi^N$. -/
noncomputable def coordMap (π : R) (K e N : ℕ) (a : R ⧸ Ideal.span {π ^ K}) :
    R ⧸ Ideal.span {π ^ N} :=
  Ideal.Quotient.mk _ (divPow π e (qlift a))

/-- For $N \ge 1$: $\pi \mid (r \bmod \pi^N)$ in $R/\pi^N$ iff $\pi \mid r$. -/
theorem mk_dvd_mk_iff (π : R) {N : ℕ} (hN : 1 ≤ N) (r : R) :
    Ideal.Quotient.mk (Ideal.span {π ^ N}) π ∣ Ideal.Quotient.mk _ r ↔ π ∣ r := by
  constructor
  · rintro ⟨c, hc⟩
    rw [← mk_qlift c, ← map_mul, mk_eq_mk_iff] at hc
    have h1 : π ∣ r - π * qlift c := (dvd_pow_self π (by omega)).trans hc
    have := h1.add (dvd_mul_right π (qlift c))
    simpa using this
  · rintro ⟨c, rfl⟩
    rw [map_mul]; exact dvd_mul_right _ _

theorem mk_dvd_iff (π : R) {K : ℕ} (hK : 1 ≤ K) (a : R ⧸ Ideal.span {π ^ K}) :
    Ideal.Quotient.mk _ π ∣ a ↔ π ∣ qlift a := by
  conv_lhs => rw [← mk_qlift a]
  exact mk_dvd_mk_iff π hK _

/-- **Fibres of a coordinate map** ($\pi \ne 0$, $K = N + e + t$): the classes $a$ mod $\pi^K$ with
$\pi^e \mid a$ and $a/\pi^e \equiv b \pmod{\pi^N}$ are in bijection with $R/\pi^t$, via
$c \mapsto \pi^e(\tilde b + \pi^N \tilde c)$. -/
theorem coordFibre_nonempty (π : R) (hπ : π ≠ 0) {K : ℕ} (N e t : ℕ) (hK : K = N + e + t)
    (b : R ⧸ Ideal.span {π ^ N}) :
    Nonempty ({a : R ⧸ Ideal.span {π ^ K} // π ^ e ∣ qlift a ∧ coordMap π K e N a = b} ≃
      R ⧸ Ideal.span {π ^ t}) := by
  subst hK
  have hmem : ∀ c : R ⧸ Ideal.span {π ^ t},
      π ^ e ∣ qlift (Ideal.Quotient.mk (Ideal.span {π ^ (N + e + t)})
          (π ^ e * (qlift b + π ^ N * qlift c))) ∧
        coordMap π (N + e + t) e N (Ideal.Quotient.mk (Ideal.span {π ^ (N + e + t)})
          (π ^ e * (qlift b + π ^ N * qlift c))) = b := by
    intro c
    have h1 := dvd_qlift_mk_sub π (N + e + t) (π ^ e * (qlift b + π ^ N * qlift c))
    have hd : π ^ e ∣ qlift (Ideal.Quotient.mk (Ideal.span {π ^ (N + e + t)})
          (π ^ e * (qlift b + π ^ N * qlift c))) := by
      have h0 : π ^ e ∣ π ^ (N + e + t) := pow_dvd_pow _ (by omega)
      have := (h0.trans h1).add (dvd_mul_right (π ^ e) (qlift b + π ^ N * qlift c))
      simpa using this
    refine ⟨hd, ?_⟩
    rw [coordMap, ← mk_qlift b, mk_eq_mk_iff]
    rw [eq_mul_divPow hd] at h1
    have h3 : π ^ (N + t) ∣ divPow π e (qlift (Ideal.Quotient.mk (Ideal.span {π ^ (N + e + t)})
          (π ^ e * (qlift b + π ^ N * qlift c)))) - (qlift b + π ^ N * qlift c) := by
      rw [← mul_dvd_mul_iff_left (pow_ne_zero e hπ), mul_sub, ← pow_add]
      rw [show e + (N + t) = N + e + t by ring]
      exact h1
    have h4 := ((pow_dvd_pow π (by omega : N ≤ N + t)).trans h3).add
      (dvd_mul_right (π ^ N) (qlift c))
    rw [mk_qlift]
    convert h4 using 1; ring
  refine ⟨(Equiv.ofBijective (fun c => ⟨_, hmem c⟩) ⟨?_, ?_⟩).symm⟩
  · intro c c' h
    have h' := congrArg Subtype.val h
    simp only at h'
    rw [mk_eq_mk_iff] at h'
    have h5 : π ^ (e + N) * π ^ t ∣ π ^ (e + N) * (qlift c - qlift c') := by
      rw [← pow_add, show e + N + t = N + e + t by ring]
      convert h' using 1; ring
    have h6 := (mul_dvd_mul_iff_left (pow_ne_zero _ hπ)).1 h5
    rw [← mk_qlift c, ← mk_qlift c', mk_eq_mk_iff]
    exact h6
  · rintro ⟨a, hd, hb⟩
    set r := divPow π e (qlift a) with hr
    have har := eq_mul_divPow hd
    rw [coordMap, ← hr, ← mk_qlift b, mk_eq_mk_iff] at hb
    obtain ⟨s, hs⟩ := hb
    refine ⟨Ideal.Quotient.mk _ s, ?_⟩
    apply Subtype.ext
    simp only
    conv_rhs => rw [← mk_qlift a]
    rw [mk_eq_mk_iff]
    have h7 := dvd_qlift_mk_sub π t s
    have h8 : π ^ e * (qlift b + π ^ N * qlift (Ideal.Quotient.mk (Ideal.span {π ^ t}) s)) - qlift a
        = π ^ (e + N) * (qlift (Ideal.Quotient.mk (Ideal.span {π ^ t}) s) - s) := by
      rw [har, ← hr, show r = qlift b + π ^ N * s by linear_combination hs]; ring
    rw [h8, show N + e + t = (e + N) + t by ring, pow_add]
    exact mul_dvd_mul_left _ h7

/-- **Counting through a map with uniform fibres** (any cardinalities, via `Nat.card`). -/
theorem natCard_eq_of_fibres {A B C : Type*} (f : A → B) (e : ∀ b, {a // f a = b} ≃ C) :
    Nat.card A = Nat.card B * Nat.card C := by
  rw [← Nat.card_prod]
  exact Nat.card_congr ((Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaEquivProd B C)))

/-- **Coordinatewise fibration count**: if each coordinate map $g_j$ (on the domain $D_j$) has all
fibres in bijection with $C_j$, then the vectors $\vec{x}$ with $\vec{x} \in \prod D_j$ and
$P(g(\vec{x}))$ number $\#\{P\} \cdot \prod_j \#C_j$. -/
theorem natCard_pi_fibres {α β : Type*} (D : Fin n → α → Prop) (g : Fin n → α → β)
    (C : Fin n → Type*) (e : ∀ j b, Nonempty ({a // D j a ∧ g j a = b} ≃ C j))
    (P : (Fin n → β) → Prop) :
    Nat.card {x : Fin n → α // (∀ j, D j (x j)) ∧ P (fun j => g j (x j))} =
      Nat.card {y // P y} * ∏ j, Nat.card (C j) := by
  rw [← Nat.card_pi]
  refine natCard_eq_of_fibres
    (fun x => (⟨fun j => g j (x.1 j), x.2.2⟩ : {y // P y})) fun y => ?_
  refine (Equiv.subtypeEquivRight (q := fun x => (fun j => g j (x.1 j)) = y.1) ?_).trans ?_
  · intro x; rw [Subtype.ext_iff]
  refine (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun x : Fin n → α => (∀ j, D j (x j)) ∧ P (fun j => g j (x j)))
    (fun x => (fun j => g j (x j)) = y.1)).trans ?_
  refine (Equiv.subtypeEquivRight (q := fun x : Fin n → α => ∀ j, D j (x j) ∧ g j (x j) = y.1 j)
    ?_).trans ?_
  · intro x
    constructor
    · rintro ⟨⟨hD, -⟩, hg⟩ j; exact ⟨hD j, congrFun hg j⟩
    · intro h
      have hg : (fun j => g j (x j)) = y.1 := funext fun j => (h j).2
      exact ⟨⟨fun j => (h j).1, hg ▸ y.2⟩, hg⟩
  exact Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun j => (e j (y.1 j)).some)

/-- **$\#(R/\pi^t) = q^t$** for a uniformizer $\pi$ (no finiteness assumption: both sides are $0$ when
the residue field is infinite and $t \ge 1$). -/
theorem natCard_quot_pow (π : R) (hπ : Irreducible π) (t : ℕ) :
    Nat.card (R ⧸ Ideal.span {π ^ t}) = q R ^ t := by
  induction t with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    have : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.2 rfl
    exact Nat.card_unique
  | succ t ih =>
    have h1 : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by
      rw [pow_one, ← hπ.maximalIdeal_eq]; rfl
    rw [natCard_eq_of_fibres (coordMap π (t + 1) 0 t) (C := R ⧸ Ideal.span {π ^ 1}) fun b =>
      (Equiv.subtypeEquivRight (fun a => by simp)).trans
        (coordFibre_nonempty π hπ.ne_zero t 0 1 (by ring) b).some, ih, h1, pow_succ]

/-- **Reduction of $Q$ mod an ideal**: $Q(\vec{X} \bmod I) = Q(\vec{X}) \bmod I$. -/
theorem evalIn_mk (Q : QuadForm R n) (I : Ideal R) (X : Fin n → R) :
    Q.evalIn (R ⧸ I) (fun j => Ideal.Quotient.mk I (X j)) = Ideal.Quotient.mk I (Q.evalIn R X) := by
  simp [QuadForm.evalIn, map_sum, apply_ite (Ideal.Quotient.mk I), Ideal.Quotient.algebraMap_eq]

/-- **Transfer of a congruence through $Q(\vec{X}) = \pi^e Q_2(\vec{Y})$**: for $\vec{x}$ mod $\pi^{N+e}$,
$Q(\vec{x}) \equiv \pi^e m' \pmod{\pi^{N+e}}$ iff $Q_2(\vec{Y}) \equiv m' \pmod{\pi^N}$. -/
theorem evalIn_eq_mk_iff (Q Q₂ : QuadForm R n) (π : R) (hπ : π ≠ 0) {K : ℕ} (N e : ℕ)
    (hK : K = N + e) (x : Fin n → R ⧸ Ideal.span {π ^ K}) (Y : Fin n → R) (m' : R)
    (hXY : Q.evalIn R (fun j => qlift (x j)) = π ^ e * Q₂.evalIn R Y) :
    Q.evalIn _ x = Ideal.Quotient.mk _ (π ^ e * m') ↔
      Q₂.evalIn (R ⧸ Ideal.span {π ^ N}) (fun j => Ideal.Quotient.mk _ (Y j)) =
        Ideal.Quotient.mk _ m' := by
  subst hK
  have hx : x = fun j => Ideal.Quotient.mk _ (qlift (x j)) := funext fun j => (mk_qlift _).symm
  rw [hx, evalIn_mk, evalIn_mk, hXY, mk_eq_mk_iff, mk_eq_mk_iff, ← mul_sub, pow_add,
    mul_comm (π ^ N), mul_dvd_mul_iff_left (pow_ne_zero _ hπ)]

/-- **Homogeneity**: $Q(c\vec{Y}) = c^2 Q(\vec{Y})$. -/
theorem evalIn_mul_left (Q : QuadForm R n) (c : R) (X Y : Fin n → R) (hXY : ∀ j, X j = c * Y j) :
    Q.evalIn R X = c ^ 2 * Q.evalIn R Y := by
  simp only [QuadForm.evalIn, Finset.mul_sum, hXY]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- In local normal form, a nonzero coefficient $c_{ij}$ ($i \le j$) lies in one block: $\nu_i = \nu_j$. -/
theorem nu_eq_of_coeff_ne_zero {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)}
    {ν : Fin n → ℕ} (hJ : IsJordanFormW Q π P ν) {i j : Fin n} (hij : i ≤ j)
    (hne : Q.coeff i j ≠ 0) : ν i = ν j := by
  obtain ⟨-, -, -, h4, h5, -⟩ := hJ
  rcases hij.eq_or_lt with rfl | hlt
  · rfl
  · by_cases hP : (i, j) ∈ P
    · exact (h5 _ hP).1
    · exact absurd (h4 i j hlt hP) hne

/-- **$Q(\vec{x}) = \pi\, Q'(\vec{x}')$** for the Bad type I substitution $x_j = \pi x'_j$ on $S_0$. -/
theorem evalIn_badI (Q Q' : QuadForm R n) (π : R) (hπ : π ≠ 0) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν)
    (hQ' : ∀ i j, (ν i = 0 → Q'.coeff i j = π * Q.coeff i j) ∧
      (ν i ≠ 0 → Q.coeff i j = π * Q'.coeff i j))
    (X Y : Fin n → R) (hXY : ∀ j, X j = π ^ (if ν j = 0 then 1 else 0) * Y j) :
    Q.evalIn R X = π * Q'.evalIn R Y := by
  simp only [QuadForm.evalIn, Finset.mul_sum, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [hXY i, hXY j]
    by_cases h0 : Q.coeff i j = 0
    · have h0' : Q'.coeff i j = 0 := by
        by_cases hν : ν i = 0
        · rw [(hQ' i j).1 hν, h0, mul_zero]
        · have := (hQ' i j).2 hν
          rw [h0] at this
          exact (mul_eq_zero.1 this.symm).resolve_left hπ
      simp [h0, h0']
    · have hν := nu_eq_of_coeff_ne_zero hJ hij h0
      by_cases h : ν i = 0
      · have hj : ν j = 0 := hν ▸ h
        rw [(hQ' i j).1 h]; simp only [h, hj, if_true]; ring
      · have hj : ν j ≠ 0 := hν ▸ h
        rw [(hQ' i j).2 h]; simp only [h, hj, if_false]; ring
  · simp

/-- **$Q(\vec{x}) = \pi^2 Q''(\vec{x}'')$** for the Bad type II substitution $x_j = \pi x''_j$ on $S_0 \cup S_1$. -/
theorem evalIn_badII (Q Q'' : QuadForm R n) (π : R) (hπ : π ≠ 0) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν)
    (hQ'' : ∀ i j, (2 ≤ ν i → Q.coeff i j = π ^ 2 * Q''.coeff i j) ∧
      (ν i < 2 → Q''.coeff i j = Q.coeff i j))
    (X Y : Fin n → R) (hXY : ∀ j, X j = π ^ (if ν j ≤ 1 then 1 else 0) * Y j) :
    Q.evalIn R X = π ^ 2 * Q''.evalIn R Y := by
  simp only [QuadForm.evalIn, Finset.mul_sum, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [hXY i, hXY j]
    by_cases h0 : Q.coeff i j = 0
    · have h0' : Q''.coeff i j = 0 := by
        by_cases hν : 2 ≤ ν i
        · have := (hQ'' i j).1 hν
          rw [h0] at this
          exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero 2 hπ)
        · rw [(hQ'' i j).2 (by omega), h0]
      simp [h0, h0']
    · have hν := nu_eq_of_coeff_ne_zero hJ hij h0
      by_cases h : 2 ≤ ν i
      · have hi : ¬ ν i ≤ 1 := by omega
        have hj : ¬ ν j ≤ 1 := by omega
        rw [(hQ'' i j).1 h]; simp only [hi, hj, if_false]; ring
      · have hi : ν i ≤ 1 := by omega
        have hj : ν j ≤ 1 := by omega
        rw [(hQ'' i j).2 (by omega)]; simp only [hi, hj, if_true]; ring
  · simp

/-! ### The four statements -/

theorem repCount_eq_add_types_of_finite (Q : QuadForm R n) (π : R) (S₀ : Finset (Fin n)) (k : ℕ)
    (m : R) [Finite (R ⧸ Ideal.span {π ^ k})] :
    repCount Q π k m = repCountOf Q π k m (IsZeroType π k) +
      repCountOf Q π k m (IsGoodType S₀ π k) + repCountOf Q π k m (IsBadType S₀ π k) := by
  classical
  have := Fintype.ofFinite (R ⧸ Ideal.span {π ^ k})
  unfold repCount repCountOf
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not (fun x => IsZeroType π k x), Finset.filter_filter,
    add_assoc]
  congr 1
  rw [← Finset.card_filter_add_card_filter_not (fun x => IsGoodType S₀ π k x),
    Finset.filter_filter, Finset.filter_filter]
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

/-- **Types partition the solutions** (Hanke 2004, Def. 3.1), for a uniformizer $\pi$ and a finite residue field.

*Correction:* an earlier version was stated without `Irreducible π` and finiteness, which is false
because `Nat.card` of an infinite set is 0 (e.g. $\pi = 0$ over $\mathbb{Z}_2$: the left side is 0, the Zero-type
count is 1). The version without the finite residue field is `repCount_eq_add_types_of_finite`. -/
@[kb "hanke2004" "Def. 3.1, p. 358"]
theorem repCount_eq_add_types [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n) (π : R)
    (hπ : Irreducible π) (S₀ : Finset (Fin n)) (k : ℕ) (m : R) :
    repCount Q π k m = repCountOf Q π k m (IsZeroType π k) +
      repCountOf Q π k m (IsGoodType S₀ π k) + repCountOf Q π k m (IsBadType S₀ π k) := by
  have : Finite (R ⧸ Ideal.span {π ^ k}) := by
    apply Nat.finite_of_card_ne_zero
    rw [natCard_quot_pow π hπ]
    exact pow_ne_zero _ (Nat.card_pos (α := IsLocalRing.ResidueField R)).ne'
  exact repCount_eq_add_types_of_finite Q π S₀ k m

/-- **Zero-type reduction over $R$** (Hanke 2004, map $\pi_Z$, p. 359): if $m = \pi^2 m'$ and $k \ge 2$,
$r^{\mathrm{Zero}}_{\pi^k}(m) = q^n\, r_{\pi^{k-2}}(m')$; if $\pi^2 \nmid m$ there are none. -/
@[kb "hanke2004" "§3, map π_Z, p. 359"]
theorem repCountZero_eq (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (m m' : R)
    (hm : m = π ^ 2 * m') (k : ℕ) (hk : 2 ≤ k) :
    repCountOf Q π k m (IsZeroType π k) = q R ^ n * repCount Q π (k - 2) m' := by
  classical
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 1 + 1 := ⟨k - 2, by omega⟩
  rw [show N + 1 + 1 - 2 = N by omega]
  have hπ0 := hπ.ne_zero
  subst hm
  have key : ∀ x : Fin n → R ⧸ Ideal.span {π ^ (N + 1 + 1)},
      (Q.evalIn _ x = Ideal.Quotient.mk _ (π ^ 2 * m') ∧ IsZeroType π (N + 1 + 1) x) ↔
      ((∀ j, π ^ 1 ∣ qlift (x j)) ∧
        Q.evalIn (R ⧸ Ideal.span {π ^ N}) (fun j => coordMap π (N + 1 + 1) 1 N (x j)) =
          Ideal.Quotient.mk _ m') := by
    intro x
    have hZ : IsZeroType π (N + 1 + 1) x ↔ ∀ j, π ^ 1 ∣ qlift (x j) := by
      simp only [IsZeroType, pow_one]
      exact forall_congr' fun j => mk_dvd_iff π (by omega) (x j)
    rw [hZ, and_comm]
    refine and_congr_right fun hA => ?_
    exact evalIn_eq_mk_iff Q Q π hπ0 N 2 rfl x _ m'
      (evalIn_mul_left Q π _ _ fun j => by
        have := eq_mul_divPow (hA j); rwa [pow_one] at this)
  unfold repCountOf repCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight key),
    natCard_pi_fibres (fun _ a => π ^ 1 ∣ qlift a) (fun _ => coordMap π (N + 1 + 1) 1 N)
      (fun _ => R ⧸ Ideal.span {π ^ 1}) (fun _ b => coordFibre_nonempty π hπ0 N 1 1 rfl b)
      (fun y => Q.evalIn _ y = Ideal.Quotient.mk _ m')]
  rw [Finset.prod_congr rfl fun _ _ => natCard_quot_pow π hπ 1]
  simp only [pow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- **Bad type I over $R$** (Hanke 2004, map $\pi_{B'}$, p. 360): for $Q$ in local normal form, $m = \pi m'$,
$k \ge 2$, and $Q'$ the form with $Q'_{ij} = \pi Q_{ij}$ when $\nu_i = 0$ and $Q_{ij} = \pi Q'_{ij}$ otherwise:
the Bad solutions with $\vec{x}_{S_1} \not\equiv 0$ number $q^{s_1 + s_2}$ times the Good solutions of
$Q'(\vec{x}') \equiv m' \pmod{\pi^{k-1}}$ (Good relative to $\nu' = $ `nuI ν`). -/
@[kb "hanke2004" "§3, map π_{B'}, p. 360"]
theorem repCountBadI_eq (Q Q' : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν)
    (hQ' : ∀ i j, (ν i = 0 → Q'.coeff i j = π * Q.coeff i j) ∧ (ν i ≠ 0 → Q.coeff i j = π * Q'.coeff i j))
    (m m' : R) (hm : m = π * m') (k : ℕ) (hk : 2 ≤ k) :
    repCountOf Q π k m (fun x => IsBadType (unimodularCoords ν) π k x ∧
        ∃ i, ν i = 1 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i) =
      q R ^ ((Finset.univ.filter fun i => 1 ≤ ν i).card) *
        repCountOf Q' π (k - 1) m' (IsGoodType (unimodularCoords (nuI ν)) π (k - 1)) := by
  classical
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 1 := ⟨k - 1, by omega⟩
  have hN : 1 ≤ N := by omega
  rw [show N + 1 - 1 = N by omega]
  have hπ0 := hπ.ne_zero
  subst hm
  let eI : Fin n → ℕ := fun j => if ν j = 0 then 1 else 0
  let tI : Fin n → ℕ := fun j => if ν j = 0 then 0 else 1
  let y : (Fin n → R ⧸ Ideal.span {π ^ (N + 1)}) → Fin n → R ⧸ Ideal.span {π ^ N} :=
    fun x j => coordMap π (N + 1) (eI j) N (x j)
  have key : ∀ x : Fin n → R ⧸ Ideal.span {π ^ (N + 1)},
      (Q.evalIn _ x = Ideal.Quotient.mk _ (π * m') ∧ (IsBadType (unimodularCoords ν) π (N + 1) x ∧
        ∃ i, ν i = 1 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i)) ↔
      ((∀ j, π ^ eI j ∣ qlift (x j)) ∧ (Q'.evalIn _ (y x) = Ideal.Quotient.mk _ m' ∧
        IsGoodType (unimodularCoords (nuI ν)) π N (y x))) := by
    intro x
    have hdx : ∀ j, Ideal.Quotient.mk _ π ∣ x j ↔ π ∣ qlift (x j) :=
      fun j => mk_dvd_iff π (by omega) (x j)
    have hdy : ∀ j, ν j ≠ 0 → (Ideal.Quotient.mk _ π ∣ y x j ↔ π ∣ qlift (x j)) := by
      intro j hj
      simp only [y, coordMap, eI, hj, if_false, divPow_zero]
      exact mk_dvd_mk_iff π hN _
    have hD : (∀ j, π ^ eI j ∣ qlift (x j)) ↔ ∀ j, ν j = 0 → π ∣ qlift (x j) := by
      refine forall_congr' fun j => ?_
      by_cases h : ν j = 0 <;> simp [eI, h]
    have hT : (IsBadType (unimodularCoords ν) π (N + 1) x ∧
          ∃ i, ν i = 1 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i) ↔
        ((∀ j, π ^ eI j ∣ qlift (x j)) ∧ IsGoodType (unimodularCoords (nuI ν)) π N (y x)) := by
      rw [hD]
      constructor
      · rintro ⟨⟨hnz, hng⟩, i, hi1, hi⟩
        refine ⟨fun j hj => ?_, fun hz => ?_, i, ?_, ?_⟩
        · by_contra h
          exact hng ⟨hnz, j, by simp [unimodularCoords, hj], by rwa [hdx]⟩
        · exact hi ((hdx i).2 ((hdy i (by omega)).1 (hz i)))
        · rw [unimodularCoords, Finset.mem_filter]; simp [nuI, hi1]
        · rwa [hdy i (by omega), ← hdx]
      · rintro ⟨hA, ⟨hnz, i, hi, hpi⟩⟩
        have hi1 : ν i = 1 := by
          have h : nuI ν i = 0 := by simpa [unimodularCoords] using hi
          unfold nuI at h
          split_ifs at h with h'
          omega
        have hxi : ¬ Ideal.Quotient.mk _ π ∣ x i := by rwa [hdx, ← hdy i (by omega)]
        refine ⟨⟨fun hz => hxi (hz i), fun ⟨_, j, hj, hpj⟩ => hpj ?_⟩, i, hi1, hxi⟩
        rw [hdx]
        exact hA j (by simpa [unimodularCoords] using hj)
    have hE : (∀ j, π ^ eI j ∣ qlift (x j)) →
        (Q.evalIn _ x = Ideal.Quotient.mk _ (π * m') ↔
          Q'.evalIn _ (y x) = Ideal.Quotient.mk _ m') := by
      intro hA
      rw [show π * m' = π ^ 1 * m' by ring]
      have hXY := evalIn_badI Q Q' π hπ0 P ν hJ hQ' _ _ (fun j => eq_mul_divPow (hA j))
      exact evalIn_eq_mk_iff Q Q' π hπ0 N 1 rfl x _ m' (by rw [pow_one]; exact hXY)
    constructor
    · rintro ⟨hE', hT'⟩
      obtain ⟨hA, hG⟩ := hT.1 hT'
      exact ⟨hA, (hE hA).1 hE', hG⟩
    · rintro ⟨hA, hE', hG⟩
      exact ⟨(hE hA).2 hE', hT.2 ⟨hA, hG⟩⟩
  unfold repCountOf
  rw [Nat.card_congr (Equiv.subtypeEquivRight key),
    natCard_pi_fibres (fun j a => π ^ eI j ∣ qlift a) (fun j => coordMap π (N + 1) (eI j) N)
      (fun j => R ⧸ Ideal.span {π ^ tI j})
      (fun j b => coordFibre_nonempty π hπ0 N (eI j) (tI j)
        (by simp only [eI, tI]; split_ifs <;> omega) b)
      (fun y => Q'.evalIn _ y = Ideal.Quotient.mk _ m' ∧
        IsGoodType (unimodularCoords (nuI ν)) π N y)]
  rw [mul_comm]
  congr 1
  simp only [natCard_quot_pow π hπ, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [tI]
  split_ifs <;> omega

/-- **Bad type II over $R$** (Hanke 2004, map $\pi_{B''}$, p. 360): for $Q$ in local normal form, $m = \pi^2 m'$,
$k \ge 3$, and $Q''$ with $Q_{ij} = \pi^2 Q''_{ij}$ when $\nu_i \ge 2$ and $Q''_{ij} = Q_{ij}$ otherwise: the Bad
solutions with $\vec{x}_{S_1} \equiv 0$ number $q^{2n - s_0 - s_1}$ times the solutions of
$Q''(\vec{x}'') \equiv m' \pmod{\pi^{k-2}}$ with $\vec{x}''_{S_2} \not\equiv 0$. -/
@[kb "hanke2004" "§3, map π_{B''}, p. 360"]
theorem repCountBadII_eq (Q Q'' : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν)
    (hQ'' : ∀ i j, (2 ≤ ν i → Q.coeff i j = π ^ 2 * Q''.coeff i j) ∧ (ν i < 2 → Q''.coeff i j = Q.coeff i j))
    (m m' : R) (hm : m = π ^ 2 * m') (k : ℕ) (hk : 3 ≤ k) :
    repCountOf Q π k m (fun x => IsBadType (unimodularCoords ν) π k x ∧
        ∀ i, ν i = 1 → Ideal.Quotient.mk _ π ∣ x i) =
      q R ^ (2 * n - (Finset.univ.filter fun i => ν i ≤ 1).card) *
        repCountOf Q'' π (k - 2) m' (fun y => ∃ i, 2 ≤ ν i ∧ ¬ Ideal.Quotient.mk _ π ∣ y i) := by
  classical
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 2 := ⟨k - 2, by omega⟩
  have hN : 1 ≤ N := by omega
  rw [show N + 2 - 2 = N by omega]
  have hπ0 := hπ.ne_zero
  subst hm
  let eI : Fin n → ℕ := fun j => if ν j ≤ 1 then 1 else 0
  let tI : Fin n → ℕ := fun j => if ν j ≤ 1 then 1 else 2
  let y : (Fin n → R ⧸ Ideal.span {π ^ (N + 2)}) → Fin n → R ⧸ Ideal.span {π ^ N} :=
    fun x j => coordMap π (N + 2) (eI j) N (x j)
  have key : ∀ x : Fin n → R ⧸ Ideal.span {π ^ (N + 2)},
      (Q.evalIn _ x = Ideal.Quotient.mk _ (π ^ 2 * m') ∧
        (IsBadType (unimodularCoords ν) π (N + 2) x ∧ ∀ i, ν i = 1 → Ideal.Quotient.mk _ π ∣ x i)) ↔
      ((∀ j, π ^ eI j ∣ qlift (x j)) ∧ (Q''.evalIn _ (y x) = Ideal.Quotient.mk _ m' ∧
        ∃ i, 2 ≤ ν i ∧ ¬ Ideal.Quotient.mk _ π ∣ y x i)) := by
    intro x
    have hdx : ∀ j, Ideal.Quotient.mk _ π ∣ x j ↔ π ∣ qlift (x j) :=
      fun j => mk_dvd_iff π (by omega) (x j)
    have hdy : ∀ j, 2 ≤ ν j → (Ideal.Quotient.mk _ π ∣ y x j ↔ π ∣ qlift (x j)) := by
      intro j hj
      have : ¬ ν j ≤ 1 := by omega
      simp only [y, coordMap, eI, this, if_false, divPow_zero]
      exact mk_dvd_mk_iff π hN _
    have hD : (∀ j, π ^ eI j ∣ qlift (x j)) ↔ ∀ j, ν j ≤ 1 → π ∣ qlift (x j) := by
      refine forall_congr' fun j => ?_
      by_cases h : ν j ≤ 1 <;> simp [eI, h]
    have hT : (IsBadType (unimodularCoords ν) π (N + 2) x ∧
          ∀ i, ν i = 1 → Ideal.Quotient.mk _ π ∣ x i) ↔
        ((∀ j, π ^ eI j ∣ qlift (x j)) ∧ ∃ i, 2 ≤ ν i ∧ ¬ Ideal.Quotient.mk _ π ∣ y x i) := by
      rw [hD]
      constructor
      · rintro ⟨⟨hnz, hng⟩, h1⟩
        have hA : ∀ j, ν j ≤ 1 → π ∣ qlift (x j) := by
          intro j hj
          rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj with h0 | h0
          · by_contra h
            exact hng ⟨hnz, j, by simp [unimodularCoords, h0], by rwa [hdx]⟩
          · exact (hdx j).1 (h1 j h0)
        refine ⟨hA, ?_⟩
        by_contra hc
        push Not at hc
        apply hnz
        intro j
        by_cases hj : ν j ≤ 1
        · exact (hdx j).2 (hA j hj)
        · exact (hdx j).2 ((hdy j (by omega)).1 (hc j (by omega)))
      · rintro ⟨hA, i, hi, hpi⟩
        have hxi : ¬ Ideal.Quotient.mk _ π ∣ x i := by rwa [hdx, ← hdy i hi]
        refine ⟨⟨fun hz => hxi (hz i), fun ⟨_, j, hj, hpj⟩ => hpj ?_⟩, fun j hj => ?_⟩
        · rw [hdx]
          exact hA j (by simp [unimodularCoords] at hj; omega)
        · rw [hdx]; exact hA j (by omega)
    have hE : (∀ j, π ^ eI j ∣ qlift (x j)) →
        (Q.evalIn _ x = Ideal.Quotient.mk _ (π ^ 2 * m') ↔
          Q''.evalIn _ (y x) = Ideal.Quotient.mk _ m') := by
      intro hA
      exact evalIn_eq_mk_iff Q Q'' π hπ0 N 2 rfl x _ m'
        (evalIn_badII Q Q'' π hπ0 P ν hJ hQ'' _ _ fun j => eq_mul_divPow (hA j))
    constructor
    · rintro ⟨hE', hT'⟩
      obtain ⟨hA, hG⟩ := hT.1 hT'
      exact ⟨hA, (hE hA).1 hE', hG⟩
    · rintro ⟨hA, hE', hG⟩
      exact ⟨(hE hA).2 hE', hT.2 ⟨hA, hG⟩⟩
  unfold repCountOf
  rw [Nat.card_congr (Equiv.subtypeEquivRight key),
    natCard_pi_fibres (fun j a => π ^ eI j ∣ qlift a) (fun j => coordMap π (N + 2) (eI j) N)
      (fun j => R ⧸ Ideal.span {π ^ tI j})
      (fun j b => coordFibre_nonempty π hπ0 N (eI j) (tI j)
        (by simp only [eI, tI]; split_ifs <;> omega) b)
      (fun y => Q''.evalIn _ y = Ideal.Quotient.mk _ m' ∧
        ∃ i, 2 ≤ ν i ∧ ¬ Ideal.Quotient.mk _ π ∣ y i)]
  rw [mul_comm]
  congr 1
  simp only [natCard_quot_pow π hπ, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum : ∑ j, tI j + (Finset.univ.filter fun i => ν i ≤ 1).card = 2 * n := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (g := fun _ => 2) fun j _ => by simp only [tI]; split_ifs <;> rfl]
    simp [mul_comm]
  omega


end QuadFormsKB.LocalDensity.DVR
