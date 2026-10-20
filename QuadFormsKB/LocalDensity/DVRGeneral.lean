/-
# Local densities over a DVR: stabilization and existence of $\beta_\pi(m)$ at every prime

**Layer:** DVR. **Proves** Hanke 2004, §3 (the recursion of Lemma 3.4, p. 361) and (5.2), p. 368 (corrected):
for $Q$ nondegenerate, $R/\pi$ finite, $2 \ne 0$ and $m \ne 0$, $r_{\pi^{k+1}}(m) = q^{n-1} r_{\pi^k}(m)$ for
$k \gg 0$ (`DVR.repCount_stabilizes`) and $\beta_\pi(m)$ is attained (`DVR.localDensity_eventually_eq`), at
every prime of a number field including ramified dyadic ones. Also the reduced forms $Q'$, $Q''$ (`badIForm`,
`badIIForm`) stay in normal form (`isJordanFormW_badI_badII`, p. 360). **Depends on** `Lemma32.lean`,
`DVRReductions.lean` (and `exists_jordanFormW` from `DyadicJordan.lean`).
-/
import QuadFormsKB.LocalDensity.Lemma32
import QuadFormsKB.LocalDensity.DVRReductions

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}


/-- In local normal form, $\pi^{\min(d, \nu_i)} \mid c_{ij}$; in particular $\pi^d \mid c_{ij}$ when $d \le \nu_i$. -/
theorem IsJordanFormW.pow_dvd_coeff {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)}
    {ν : Fin n → ℕ} (hJ : IsJordanFormW Q π P ν) (i j : Fin n) (d : ℕ) (hd : d ≤ ν i) :
    π ^ d ∣ Q.coeff i j := by
  by_cases hij : i ≤ j
  · by_cases h0 : Q.coeff i j = 0
    · rw [h0]; exact dvd_zero _
    · exact (pow_dvd_pow π hd).trans (hJ.coeff_block i j hij h0).2
  · rw [Q.upper (show id j < id i from not_le.mp hij)]; exact dvd_zero _

/-- Exact division of $\pi^d b$ by $\pi^e$ ($e \le d$). -/
theorem divPow_pow_mul {π : R} (hπ : π ≠ 0) {e d : ℕ} (hed : e ≤ d) (b : R) :
    divPow π e (π ^ d * b) = π ^ (d - e) * b := by
  have h : π ^ e ∣ π ^ d * b := dvd_mul_of_dvd_left (pow_dvd_pow π hed) _
  have h1 := eq_mul_divPow h
  have h2 : π ^ d * b = π ^ e * (π ^ (d - e) * b) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hed]
  rw [h2] at h1 ⊢
  exact (mul_left_cancel₀ (pow_ne_zero e hπ) h1).symm

theorem divPow_of_zero {π : R} (hπ : π ≠ 0) (e : ℕ) : divPow π e 0 = 0 := by
  have := divPow_pow_mul hπ (le_refl e) 0
  rwa [mul_zero, mul_zero] at this

/-- **The form $Q'$ of Bad type I over $R$** (Hanke 2004, p. 360): coefficient $\pi c_{ij}$ when
$\nu_i = 0$ and $c_{ij}/\pi$ otherwise (exact division). -/
noncomputable def badIForm (Q : QuadForm R n) (π : R) (ν : Fin n → ℕ) : QuadForm R n :=
  QuadForm.ofUpper fun i j => if ν i = 0 then π * Q.coeff i j else divPow π 1 (Q.coeff i j)

/-- **The form $Q''$ of Bad type II over $R$** (Hanke 2004, p. 360): coefficient $c_{ij}/\pi^2$ when
$\nu_i \ge 2$ and $c_{ij}$ otherwise (exact division). -/
noncomputable def badIIForm (Q : QuadForm R n) (π : R) (ν : Fin n → ℕ) : QuadForm R n :=
  QuadForm.ofUpper fun i j => if 2 ≤ ν i then divPow π 2 (Q.coeff i j) else Q.coeff i j

/-- The coefficient relations of `repCountBadI_eq` hold for `badIForm`. -/
theorem badIForm_rel {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)} {ν : Fin n → ℕ}
    (hJ : IsJordanFormW Q π P ν) (i j : Fin n) :
    (ν i = 0 → (badIForm Q π ν).coeff i j = π * Q.coeff i j) ∧
      (ν i ≠ 0 → Q.coeff i j = π * (badIForm Q π ν).coeff i j) := by
  have hc : (badIForm Q π ν).coeff i j =
      if i ≤ j then (if ν i = 0 then π * Q.coeff i j else divPow π 1 (Q.coeff i j)) else 0 := rfl
  by_cases hij : i ≤ j
  · rw [hc]
    simp only [hij, ite_true]
    refine ⟨fun h => by simp [h], fun h => ?_⟩
    simp only [h, ite_false]
    have := eq_mul_divPow (hJ.pow_dvd_coeff i j 1 (by omega))
    rwa [pow_one] at this
  · have h0 : Q.coeff i j = 0 := Q.upper (show id j < id i from not_le.mp hij)
    rw [hc, h0]; simp [hij]

/-- The coefficient relations of `repCountBadII_eq` hold for `badIIForm`. -/
theorem badIIForm_rel {Q : QuadForm R n} {π : R} {P : Finset (Fin n × Fin n)} {ν : Fin n → ℕ}
    (hJ : IsJordanFormW Q π P ν) (i j : Fin n) :
    (2 ≤ ν i → Q.coeff i j = π ^ 2 * (badIIForm Q π ν).coeff i j) ∧
      (ν i < 2 → (badIIForm Q π ν).coeff i j = Q.coeff i j) := by
  have hc : (badIIForm Q π ν).coeff i j =
      if i ≤ j then (if 2 ≤ ν i then divPow π 2 (Q.coeff i j) else Q.coeff i j) else 0 := rfl
  by_cases hij : i ≤ j
  · rw [hc]
    simp only [hij, ite_true]
    refine ⟨fun h => ?_, fun h => by simp [show ¬ 2 ≤ ν i by omega]⟩
    simp only [h, ite_true]
    exact eq_mul_divPow (hJ.pow_dvd_coeff i j 2 h)
  · have h0 : Q.coeff i j = 0 := Q.upper (show id j < id i from not_le.mp hij)
    rw [hc, h0]; simp [hij]

/-- **$Q'$ and $Q''$ are again in norm-indexed normal form**, with exponents `nuI w`, `nuII w` (Hanke 2004,
p. 360, generalized; the analogue of `isJordanForm_badI_badII`). -/
theorem isJordanFormW_badI_badII (Q : QuadForm R n) (π : R) (hπ : π ≠ 0)
    (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (hJ : IsJordanFormW Q π P w) :
    IsJordanFormW (badIForm Q π w) π P (nuI w) ∧ IsJordanFormW (badIIForm Q π w) π P (nuII w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hJ
  have d1 : ∀ d, 1 ≤ d → ∀ b : R, divPow π 1 (π ^ d * b) = π ^ (d - 1) * b :=
    fun d hd b => divPow_pow_mul hπ hd b
  have d2 : ∀ d, 2 ≤ d → ∀ b : R, divPow π 2 (π ^ d * b) = π ^ (d - 2) * b :=
    fun d hd b => divPow_pow_mul hπ hd b
  have cI : ∀ i j, (badIForm Q π w).coeff i j = if i ≤ j then
      (if w i = 0 then π * Q.coeff i j else divPow π 1 (Q.coeff i j)) else 0 := fun i j => rfl
  have cII : ∀ i j, (badIIForm Q π w).coeff i j = if i ≤ j then
      (if 2 ≤ w i then divPow π 2 (Q.coeff i j) else Q.coeff i j) else 0 := fun i j => rfl
  -- divisibility of all coefficients of a pair block by `π ^ w`
  have hdivs : ∀ e ∈ P, ∀ d, d ≤ w e.1 → π ^ d ∣ Q.coeff e.1 e.1 ∧ π ^ d ∣ Q.coeff e.1 e.2 ∧
      π ^ d ∣ Q.coeff e.2 e.2 := by
    intro e he d hd
    obtain ⟨-, ha, hc, -, μ, β, hb, -, hle, -⟩ := h5 e he
    refine ⟨(pow_dvd_pow π hd).trans ha, ?_, (pow_dvd_pow π hd).trans hc⟩
    rw [hb]; exact dvd_mul_of_dvd_left (pow_dvd_pow π (hd.trans hle)) _
  refine ⟨⟨h1, h2, h3, ?_, ?_, ?_⟩, ⟨h1, h2, h3, ?_, ?_, ?_⟩⟩
  · intro i j hij hP; rw [cI, h4 i j hij hP]; simp [divPow_of_zero hπ]
  · intro e he
    obtain ⟨hw, hpb⟩ := h5 e he
    have hle : e.1 ≤ e.2 := (h2 e he).le
    rw [cI, cI, cI, if_pos le_rfl, if_pos hle, if_pos le_rfl, ← hw]
    refine ⟨by simp only [nuI, hw], ?_⟩
    by_cases h0 : w e.1 = 0
    · simp only [nuI, h0, if_true]
      have := hpb.mul hπ 1
      rw [h0, zero_add, pow_one] at this
      exact this
    · simp only [nuI, h0, if_false]
      obtain ⟨a1, a2, a3⟩ := hdivs e he 1 (Nat.one_le_iff_ne_zero.2 h0)
      have hpb' := hpb
      rw [eq_mul_divPow a1, eq_mul_divPow a2, eq_mul_divPow a3,
        show w e.1 = w e.1 - 1 + 1 by omega] at hpb'
      exact hpb'.cancel hπ 1
  · intro i hi
    obtain ⟨u, hu, hup⟩ := h6 i hi
    simp only [cI, le_refl, ite_true, nuI]
    by_cases h0 : w i = 0
    · simp only [h0, ite_true, pow_zero, one_mul] at hu ⊢
      exact ⟨u, by rw [hu]; ring, hup⟩
    · simp only [h0, ite_false]
      exact ⟨u, by rw [hu, d1 _ (Nat.one_le_iff_ne_zero.mpr h0)], hup⟩
  · intro i j hij hP; rw [cII, h4 i j hij hP]; simp [divPow_of_zero hπ]
  · intro e he
    obtain ⟨hw, hpb⟩ := h5 e he
    have hle : e.1 ≤ e.2 := (h2 e he).le
    rw [cII, cII, cII, if_pos le_rfl, if_pos hle, if_pos le_rfl, ← hw]
    refine ⟨by simp only [nuII, hw], ?_⟩
    by_cases h0 : 2 ≤ w e.1
    · simp only [nuII, h0, if_true]
      obtain ⟨a1, a2, a3⟩ := hdivs e he 2 h0
      have hpb' := hpb
      rw [eq_mul_divPow a1, eq_mul_divPow a2, eq_mul_divPow a3,
        show w e.1 = w e.1 - 2 + 2 by omega] at hpb'
      exact hpb'.cancel hπ 2
    · simp only [nuII, h0, if_false]
      exact hpb
  · intro i hi
    obtain ⟨u, hu, hup⟩ := h6 i hi
    simp only [cII, le_refl, ite_true, nuII]
    by_cases h0 : 2 ≤ w i
    · simp only [h0, ite_true]
      exact ⟨u, by rw [hu, d2 _ h0], hup⟩
    · simp only [h0, ite_false]
      exact ⟨u, hu, hup⟩

/-- **Rescaling $S_2$ undoes $Q \mapsto Q''$** over $R$ (Hanke 2004, §3, p. 360):
$Q(\vec{y}) = Q''(\vec{y}')$ with $y'_i = \pi y_i$ for $\nu_i \ge 2$ and $y'_i = y_i$ otherwise. -/
theorem eval_badIIForm_rescale (Q : QuadForm R n) (π : R) (hπ : π ≠ 0)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (Y : Fin n → R) :
    Q.eval Y = (badIIForm Q π ν).eval (fun i => if 2 ≤ ν i then π * Y i else Y i) := by
  have h1 := evalIn_badII Q (badIIForm Q π ν) π hπ P ν hJ (badIIForm_rel hJ)
    (fun j => π * Y j) (fun i => if 2 ≤ ν i then π * Y i else Y i) (fun j => by
      by_cases h : 2 ≤ ν j
      · simp [h, show ¬ ν j ≤ 1 by omega]
      · simp [h, show ν j ≤ 1 by omega])
  have h2 := evalIn_mul_left Q π (fun j => π * Y j) Y (fun j => rfl)
  rw [h2] at h1
  exact mul_left_cancel₀ (pow_ne_zero 2 hπ) h1

/-- With a finite residue field, every $R/\pi^k$ is finite. -/
theorem finite_quot_pow [Finite (IsLocalRing.ResidueField R)] (π : R) (hπ : Irreducible π) (k : ℕ) :
    Finite (R ⧸ Ideal.span {π ^ k}) := by
  apply Nat.finite_of_card_ne_zero
  rw [natCard_quot_pow π hπ]
  exact pow_ne_zero _ (Nat.card_pos (α := IsLocalRing.ResidueField R)).ne'

theorem q_pos [Finite (IsLocalRing.ResidueField R)] : 0 < q R :=
  Nat.card_pos (α := IsLocalRing.ResidueField R)

/-- **Divisibility mod $\pi^k$ descends to $R$** for exponents $e \le k$. -/
theorem pow_dvd_of_mk_dvd (π : R) (k e : ℕ) (he : e ≤ k) (m : R)
    (h : (Ideal.Quotient.mk (Ideal.span {π ^ k}) π) ^ e ∣ Ideal.Quotient.mk _ m) : π ^ e ∣ m := by
  obtain ⟨c, hc⟩ := h
  rw [← mk_qlift c, ← map_pow, ← map_mul, mk_eq_mk_iff] at hc
  have := ((pow_dvd_pow π he).trans hc).add (dvd_mul_right (π ^ e) (qlift c))
  simpa using this

/-- **Divisibility of values on vectors vanishing on low blocks** over $R$ (Hanke 2004, §3, p. 360): for
$Q$ in local normal form, $e \le 2$, and $\vec{x}$ with $\pi \mid x_i$ whenever $\nu_i < e$,
$\pi^e \mid Q(\vec{x})$ in $R/\pi^k$. -/
theorem pow_dvd_evalIn_J (Q : QuadForm R n) (π : R) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (k e : ℕ) (he : e ≤ 2)
    (x : Fin n → R ⧸ Ideal.span {π ^ k})
    (hx : ∀ i, ν i < e → Ideal.Quotient.mk _ π ∣ x i) :
    (Ideal.Quotient.mk (Ideal.span {π ^ k}) π) ^ e ∣ Q.evalIn (R ⧸ Ideal.span {π ^ k}) x := by
  unfold QuadForm.evalIn
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  split_ifs with hij
  · by_cases h0 : Q.coeff i j = 0
    · simp [h0]
    obtain ⟨hν, hd⟩ := hJ.coeff_block i j hij h0
    by_cases hlt : ν i < e
    · obtain ⟨a, ha⟩ := hx i hlt
      obtain ⟨b, hb⟩ := hx j (hν ▸ hlt)
      rw [ha, hb]
      exact (pow_dvd_pow _ he).trans ⟨algebraMap R _ (Q.coeff i j) * a * b, by ring⟩
    · obtain ⟨c, hc⟩ := (pow_dvd_pow π (show e ≤ ν i by omega)).trans hd
      rw [hc, Ideal.Quotient.algebraMap_eq, map_mul, map_pow]
      exact ⟨Ideal.Quotient.mk _ c * x i * x j, by ring⟩
  · exact dvd_zero _

/-- **No solutions of a type forcing $\pi^e \mid Q(\vec{x})$ when $\pi^e \nmid m$** ($e \le 2$). -/
theorem repCountOf_eq_zero_of_not_dvd (Q : QuadForm R n) (π : R) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (m : R) (k e : ℕ) (he : e ≤ 2) (hek : e ≤ k)
    (hme : ¬ π ^ e ∣ m) (T : (Fin n → R ⧸ Ideal.span {π ^ k}) → Prop)
    (hT : ∀ x, T x → ∀ i, ν i < e → Ideal.Quotient.mk _ π ∣ x i) :
    repCountOf Q π k m T = 0 := by
  unfold repCountOf
  rw [Nat.card_eq_zero]; left
  refine ⟨fun ⟨x, hx, hTx⟩ => hme (pow_dvd_of_mk_dvd π k e hek m ?_)⟩
  rw [← hx]; exact pow_dvd_evalIn_J Q π P ν hJ k e he x (hT x hTx)

/-- **Splitting a finite count by a predicate.** -/
theorem natCard_split {α : Type*} [Finite α] (A B C P : α → Prop) (hB : ∀ x, B x ↔ A x ∧ P x)
    (hC : ∀ x, C x ↔ A x ∧ ¬ P x) :
    Nat.card {x // A x} = Nat.card {x // B x} + Nat.card {x // C x} := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype,
    ← Finset.card_filter_add_card_filter_not (p := P), Finset.filter_filter, Finset.filter_filter]
  congr 2 <;> ext x <;> simp [hB, hC]

/-- **The kernel of multiplication by $\pi$ on $R/\pi^k$** ($k \ge 1$) has $q$ elements, so each nonempty
fibre of $a \mapsto \pi a$ has $q$ elements. -/
theorem natCard_mul_pi_fibre (π : R) (hπ : Irreducible π) (k : ℕ) (hk : 1 ≤ k)
    (b : R ⧸ Ideal.span {π ^ k}) (hb : Ideal.Quotient.mk _ π ∣ b) :
    Nat.card {a : R ⧸ Ideal.span {π ^ k} // Ideal.Quotient.mk _ π * a = b} = q R := by
  obtain ⟨c, rfl⟩ := hb
  have hπ0 := hπ.ne_zero
  have e1 : {a : R ⧸ Ideal.span {π ^ k} // Ideal.Quotient.mk _ π * a = Ideal.Quotient.mk _ π * c} ≃
      {w : R ⧸ Ideal.span {π ^ k} // π ^ (k - 1) ∣ qlift w} := by
    refine Equiv.subtypeEquiv (Equiv.subRight c) fun a => ?_
    simp only [Equiv.subRight_apply]
    rw [← sub_eq_zero, ← mul_sub]
    generalize a - c = w
    conv_lhs => rw [← mk_qlift w]
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show k - 1 = j by omega]
    rw [show π ^ k = π * π ^ j by rw [hj, pow_succ']]
    exact mul_dvd_mul_iff_left hπ0
  rw [Nat.card_congr e1]
  have := natCard_eq_of_fibres
    (fun w : {w : R ⧸ Ideal.span {π ^ k} // π ^ (k - 1) ∣ qlift w} => coordMap π k (k - 1) 1 w.1)
    (C := R ⧸ Ideal.span {π ^ 0}) fun b =>
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun w => π ^ (k - 1) ∣ qlift w)
        (fun w => coordMap π k (k - 1) 1 w = b)).trans
        (coordFibre_nonempty π hπ0 1 (k - 1) 0 (by omega) b).some
  rw [this, natCard_quot_pow π hπ, natCard_quot_pow π hπ]
  simp

/-- **Solutions vanishing mod $\pi$ on a set of coordinates** over $R$ (Hanke 2004, §3, p. 359): if
$Q'(\vec{y}) = Q(\vec{y}')$ with $y'_i = \pi y_i$ ($i \in T$), $y'_i = y_i$ otherwise, then for $k \ge 1$,
$q^{|T|} \cdot \#\{\vec{x} : Q(\vec{x}) \equiv m \bmod \pi^k,\ \vec{x}_T \equiv \vec{0}\} = r_{\pi^k}(Q', m)$. -/
theorem repCount_zeroOn_of_rescale [Finite (IsLocalRing.ResidueField R)] (Q Q' : QuadForm R n)
    (π : R) (hπ : Irreducible π) (T : Finset (Fin n))
    (hQ' : ∀ Y : Fin n → R, Q'.eval Y = Q.eval (fun i => if i ∈ T then π * Y i else Y i))
    (m : R) (k : ℕ) (hk : 1 ≤ k) :
    q R ^ T.card * repCountOf Q π k m (fun x => ∀ i ∈ T, Ideal.Quotient.mk _ π ∣ x i) =
      repCount Q' π k m := by
  classical
  have := finite_quot_pow π hπ k
  set S := R ⧸ Ideal.span {π ^ k}
  let fi : Fin n → S → S := fun i a => if i ∈ T then Ideal.Quotient.mk _ π * a else a
  let f : (Fin n → S) → (Fin n → S) := fun y i => fi i (y i)
  have hf : ∀ y, Q'.evalIn S y = Q.evalIn S (f y) := by
    intro y
    have hy : y = fun j => Ideal.Quotient.mk _ (qlift (y j)) := funext fun j => (mk_qlift _).symm
    have hfy : f y = fun j => Ideal.Quotient.mk (Ideal.span {π ^ k})
        ((fun i => if i ∈ T then π * qlift (y i) else qlift (y i)) j) := by
      funext j
      simp only [f, fi]
      split_ifs <;> simp [map_mul, mk_qlift]
    rw [hfy, evalIn_mk]
    have h1 := hQ' (fun j => qlift (y j))
    simp only [QuadForm.eval] at h1
    rw [← h1, ← evalIn_mk]
    exact congrArg _ hy
  have hfT : ∀ y, ∀ i ∈ T, Ideal.Quotient.mk _ π ∣ f y i := by
    intro y i hi
    simp only [f, fi, hi, if_true]
    exact dvd_mul_right _ _
  let F : {y : Fin n → S // Q'.evalIn S y = Ideal.Quotient.mk _ m} →
      {x : Fin n → S // Q.evalIn S x = Ideal.Quotient.mk _ m ∧ ∀ i ∈ T, Ideal.Quotient.mk _ π ∣ x i} :=
    fun y => ⟨f y.1, by rw [← hf]; exact y.2, hfT y.1⟩
  have hfib : ∀ x : {x : Fin n → S // Q.evalIn S x = Ideal.Quotient.mk _ m ∧
      ∀ i ∈ T, Ideal.Quotient.mk _ π ∣ x i}, Nat.card {y // F y = x} = q R ^ T.card := by
    intro x
    have e1 : {y // F y = x} ≃ {y : Fin n → S // ∀ i, fi i (y i) = x.1 i} :=
      { toFun := fun y => ⟨y.1.1, fun i => congrFun (congrArg Subtype.val y.2) i⟩
        invFun := fun y => ⟨⟨y.1, by rw [hf]; rw [show f y.1 = x.1 from funext y.2]; exact x.2.1⟩,
          Subtype.ext (funext y.2)⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
    rw [Nat.card_congr (e1.trans (Equiv.subtypePiEquivPi (p := fun i a => fi i a = x.1 i))),
      Nat.card_pi]
    rw [Finset.prod_congr rfl (g := fun i => if i ∈ T then q R else 1)]
    · rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    · intro i _
      by_cases hi : i ∈ T
      · simp only [fi, hi, if_true]
        exact natCard_mul_pi_fibre π hπ k hk _ (x.2.2 i hi)
      · simp only [fi, hi, if_false]
        exact Nat.card_unique
  unfold repCount repCountOf
  have : Fintype {x : Fin n → S // Q.evalIn S x = Ideal.Quotient.mk _ m ∧
      ∀ i ∈ T, Ideal.Quotient.mk _ π ∣ x i} := Fintype.ofFinite _
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv F).symm, Nat.card_sigma,
    Finset.sum_congr rfl fun x _ => hfib x, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    ← Nat.card_eq_fintype_card, mul_comm]

/-- **$\mathrm{ord}_\pi$ of a nonzero element is finite**: $\pi^e \,\|\, x$ for some $e$. -/
theorem exists_pow_dvd_not_dvd (π : R) (hπ : Irreducible π) {x : R} (hx : x ≠ 0) :
    ∃ e, π ^ e ∣ x ∧ ¬ π ^ (e + 1) ∣ x := by
  obtain ⟨e, hA⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hπ
  refine ⟨e, hA.symm.dvd, fun h => ?_⟩
  have h' : π ^ (e + 1) ∣ π ^ e := h.trans hA.dvd
  rw [pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at h'
  omega

/-- **Stabilization for forms in local normal form over $R$** (Hanke 2004, §3), when $2 \ne 0$ in $R$
(given $e = \mathrm{ord}_\pi(2)$): $r_{\pi^{k+1}}(m) = q^{n-1} r_{\pi^k}(m)$ for all large $k$.
*Proof:* as `LocalDensity.repCount_stabilizes_J` (ℤ), by strong induction on $N$ with $\pi^N \nmid m$, over
all forms in local normal form at once: Good counts stabilize for $k \ge 2e+1$ (`repCountGood_add`), Zero and
Bad counts reduce to $m/\pi^2$ or to Good counts of $Q'$ (`repCountZero_eq`, `repCountBadI_eq`,
`repCountBadII_eq`, with $Q' = $ `badIForm`, $Q'' = $ `badIIForm`). -/
theorem repCount_stabilizes_J [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n) (π : R)
    (hπ : Irreducible π) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2)
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (m : R) (hm : m ≠ 0) :
    ∃ K, ∀ k ≥ K, repCount Q π (k + 1) m = q R ^ (n - 1) * repCount Q π k m := by
  classical
  have hπ0 := hπ.ne_zero
  have hfin : ∀ k, Finite (Fin n → R ⧸ Ideal.span {π ^ k}) := fun k => by
    have := finite_quot_pow π hπ k; infer_instance
  let Stab : (ℕ → ℕ) → Prop := fun f => ∃ K, ∀ k ≥ K, f (k+1) = q R ^ (n-1) * f k
  have hStabDef : ∀ f, Stab f ↔ ∃ K, ∀ k ≥ K, f (k+1) = q R ^ (n-1) * f k := fun _ => Iff.rfl
  have hcongr : ∀ f g : ℕ → ℕ, ∀ K0, (∀ k ≥ K0, f k = g k) → Stab g → Stab f := by
    intro f g K0 hfg ⟨K, hK⟩
    refine ⟨max K K0, fun k hk => ?_⟩
    rw [hfg k (by omega), hfg (k+1) (by omega), hK k (by omega)]
  have hadd : ∀ f g : ℕ → ℕ, Stab f → Stab g → Stab (fun k => f k + g k) := by
    intro f g ⟨K, hK⟩ ⟨K', hK'⟩
    refine ⟨max K K', fun k hk => ?_⟩
    simp only
    rw [hK k (by omega), hK' k (by omega), mul_add]
  have hsub : ∀ f g h : ℕ → ℕ, (∀ k, h k = f k + g k) → Stab h → Stab g → Stab f := by
    intro f g h hh ⟨K, hK⟩ ⟨K', hK'⟩
    refine ⟨max K K', fun k hk => ?_⟩
    have e1 := hK k (by omega)
    have e2 := hK' k (by omega)
    rw [hh, hh, e2, mul_add] at e1
    omega
  have hmul : ∀ (c : ℕ) (f : ℕ → ℕ), Stab f → Stab (fun k => c * f k) := by
    intro c f ⟨K, hK⟩
    refine ⟨K, fun k hk => ?_⟩
    simp only
    rw [hK k hk]; ring
  have hcancel : ∀ (c : ℕ) (f : ℕ → ℕ), 0 < c → Stab (fun k => c * f k) → Stab f := by
    intro c f hc ⟨K, hK⟩
    refine ⟨K, fun k hk => ?_⟩
    have := hK k hk
    simp only at this
    rw [mul_left_comm] at this
    exact Nat.eq_of_mul_eq_mul_left hc this
  have hshift : ∀ (d : ℕ) (f : ℕ → ℕ), Stab f → Stab (fun k => f (k - d)) := by
    intro d f ⟨K, hK⟩
    refine ⟨K + d, fun k hk => ?_⟩
    simp only
    rw [show k + 1 - d = (k - d) + 1 by omega, hK _ (by omega)]
  have hzero : Stab (fun _ => 0) := ⟨0, fun k _ => by simp⟩
  have hGoodStab : ∀ (Q : QuadForm R n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      IsJordanFormW Q π P ν → ∀ m : R,
      Stab (fun k => repCountOf Q π k m (IsGoodType (unimodularCoords ν) π k)) := by
    intro Q P ν hJ m
    refine ⟨2 * e + 1, fun k hk => ?_⟩
    have := repCountGood_add Q π hπ P ν hJ e he m k 1 hk
    simpa using this
  clear_value Stab
  have main : ∀ N, ∀ (Q : QuadForm R n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      IsJordanFormW Q π P ν → ∀ m : R, ¬ π ^ N ∣ m → Stab (fun k => repCount Q π k m) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
    intro Q P ν hJ m hN
    have IH2 : π ^ 2 ∣ m → ∀ (Q' : QuadForm R n) (P' : Finset (Fin n × Fin n)) (ν' : Fin n → ℕ),
        IsJordanFormW Q' π P' ν' → Stab (fun k => repCount Q' π k (divPow π 2 m)) := by
      intro h2 Q' P' ν' hJ'
      have hN2 : 2 ≤ N := by
        by_contra hlt
        exact hN ((pow_dvd_pow π (by omega)).trans h2)
      refine IH (N - 2) (by omega) Q' P' ν' hJ' _ fun h => hN ?_
      rw [eq_mul_divPow h2, show N = 2 + (N - 2) by omega, pow_add]
      exact mul_dvd_mul_left _ h
    obtain ⟨hJI, hJII⟩ := isJordanFormW_badI_badII Q π hπ0 P ν hJ
    have hZero : Stab (fun k => repCountOf Q π k m (IsZeroType π k)) := by
      by_cases h2 : π ^ 2 ∣ m
      · exact hcongr _ (fun k => q R ^ n * repCount Q π (k - 2) (divPow π 2 m)) 2
          (fun k hk => repCountZero_eq Q π hπ m _ (eq_mul_divPow h2) k hk)
          (hmul _ _ (hshift 2 _ (IH2 h2 Q P ν hJ)))
      · exact hcongr _ (fun _ => 0) 2
          (fun k hk => repCountOf_eq_zero_of_not_dvd Q π P ν hJ m k 2 le_rfl hk h2 _
            (fun x hx i _ => hx i)) hzero
    have hBad : Stab (fun k => repCountOf Q π k m (IsBadType (unimodularCoords ν) π k)) := by
      by_cases h1 : π ∣ m
      · have hm1 : m = π * divPow π 1 m := by
          have := eq_mul_divPow (π := π) (e := 1) (r := m) (by rwa [pow_one]); rwa [pow_one] at this
        have hsplit : ∀ k, repCountOf Q π k m (IsBadType (unimodularCoords ν) π k) =
            repCountOf Q π k m (fun x => IsBadType (unimodularCoords ν) π k x ∧
              ∃ i, ν i = 1 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i) +
            repCountOf Q π k m (fun x => IsBadType (unimodularCoords ν) π k x ∧
              ∀ i, ν i = 1 → Ideal.Quotient.mk _ π ∣ x i) := by
          intro k
          have := hfin k
          unfold repCountOf
          exact natCard_split _ _ _ (fun x => ∃ i, ν i = 1 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i)
            (fun x => by simp only [and_assoc])
            (fun x => by simp only [and_assoc, not_exists, not_and, not_not])
        have hBI : Stab (fun k => repCountOf Q π k m (fun x => IsBadType (unimodularCoords ν) π k x ∧
            ∃ i, ν i = 1 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i)) :=
          hcongr _ _ 2 (fun k hk => repCountBadI_eq Q (badIForm Q π ν) π hπ P ν hJ (badIForm_rel hJ)
              m _ hm1 k hk)
            (hmul _ _ (hshift 1 _ (hGoodStab _ P _ hJI _)))
        have hBII : Stab (fun k => repCountOf Q π k m (fun x => IsBadType (unimodularCoords ν) π k x ∧
            ∀ i, ν i = 1 → Ideal.Quotient.mk _ π ∣ x i)) := by
          by_cases h2 : π ^ 2 ∣ m
          · set T : Finset (Fin n) := Finset.univ.filter fun i => 2 ≤ ν i with hT
            have hresc : ∀ Y : Fin n → R, Q.eval Y =
                (badIIForm Q π ν).eval (fun i => if i ∈ T then π * Y i else Y i) := by
              intro Y
              rw [eval_badIIForm_rescale Q π hπ0 P ν hJ Y]
              simp [hT]
            have hZ : Stab (fun j => repCountOf (badIIForm Q π ν) π j (divPow π 2 m)
                (fun y => ∀ i ∈ T, Ideal.Quotient.mk _ π ∣ y i)) := by
              refine hcancel (q R ^ T.card) _ (pow_pos q_pos _) ?_
              refine hcongr _ _ 1 (fun j hj => ?_) (IH2 h2 Q P ν hJ)
              exact repCount_zeroOn_of_rescale (badIIForm Q π ν) Q π hπ T hresc _ j hj
            have hR : Stab (fun j => repCountOf (badIIForm Q π ν) π j (divPow π 2 m)
                (fun y => ∃ i, 2 ≤ ν i ∧ ¬ Ideal.Quotient.mk _ π ∣ y i)) := by
              refine hsub _ _ _ (fun j => ?_) (IH2 h2 _ P _ hJII) hZ
              have := hfin j
              unfold repCount repCountOf
              exact natCard_split _ _ _ (fun y => ∃ i, 2 ≤ ν i ∧ ¬ Ideal.Quotient.mk _ π ∣ y i)
                (fun x => Iff.rfl) (fun x => by simp [hT])
            exact hcongr _ _ 3 (fun k hk => repCountBadII_eq Q (badIIForm Q π ν) π hπ P ν hJ
              (badIIForm_rel hJ) m _ (eq_mul_divPow h2) k hk) (hmul _ _ (hshift 2 _ hR))
          · refine hcongr _ _ 2 (fun k hk => ?_) hzero
            refine repCountOf_eq_zero_of_not_dvd Q π P ν hJ m k 2 le_rfl hk h2 _ ?_
            rintro x ⟨hbad, hS1⟩ i hi
            rcases (by omega : ν i = 0 ∨ ν i = 1) with h | h
            · by_contra hc
              exact hbad.2 ⟨hbad.1, i, by simp [unimodularCoords, h], hc⟩
            · exact hS1 i h
        exact hcongr _ _ 0 (fun k _ => hsplit k) (hadd _ _ hBI hBII)
      · refine hcongr _ _ 1 (fun k hk => ?_) hzero
        refine repCountOf_eq_zero_of_not_dvd Q π P ν hJ m k 1 (by norm_num) hk
          (by rwa [pow_one]) _ ?_
        rintro x hbad i hi
        by_contra hc
        exact hbad.2 ⟨hbad.1, i, by simp [unimodularCoords]; omega, hc⟩
    exact hcongr _ _ 0 (fun k _ => repCount_eq_add_types Q π hπ (unimodularCoords ν) k m)
      (hadd _ _ (hadd _ _ hZero (hGoodStab Q P ν hJ m)) hBad)
  obtain ⟨a, -, ha⟩ := exists_pow_dvd_not_dvd π hπ hm
  exact (hStabDef _).mp (main _ Q P ν hJ m ha)

/-- **Stabilization over $R$** (Hanke 2004, §3 and (5.2), p. 368): for $Q$ nondegenerate over a DVR $R$ with
finite residue field and $2 \ne 0$ in $R$, and $m \ne 0$, $r_{\pi^{k+1}}(m) = q^{n-1} r_{\pi^k}(m)$ for all large $k$.
Valid at **every** prime of a number field, including ramified dyadic primes.
*Proof:* `exists_jordanFormW` gives $Q'$ in local normal form `IsJordanFormW` with the same counts; apply
`repCount_stabilizes_J` with $e = \mathrm{ord}_\pi(2)$ (finite since $2 \ne 0$). -/
@[kb "hanke2004" "§3; (5.2), p. 368"]
theorem repCount_stabilizes [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n)
    (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π) (m : R) (hm : m ≠ 0) (h20 : (2 : R) ≠ 0) :
    ∃ K, ∀ k ≥ K, repCount Q π (k + 1) m = q R ^ (n - 1) * repCount Q π k m := by
  obtain ⟨e, he⟩ := exists_pow_dvd_not_dvd π hπ h20
  obtain ⟨Q', P, w, hJ, -, hc⟩ := exists_jordanFormW Q hQ π hπ h20
  obtain ⟨K, hK⟩ := repCount_stabilizes_J Q' π hπ e he P w hJ m hm
  exact ⟨K, fun k hk => by rw [hc, hc]; exact hK k hk⟩

/-- **Stabilization over $R$ when $\pi^2 \nmid 2$** (the printed Lemma 2.1 case: non-dyadic, or $v_\pi(2) = 1$):
`repCount_stabilizes`, since $\pi^2 \nmid 2$ implies $2 \ne 0$. -/
theorem repCount_stabilizes_of_not_sq_dvd_two [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n)
    (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π) (m : R) (hm : m ≠ 0) (h2 : ¬ π ^ 2 ∣ 2) :
    ∃ K, ∀ k ≥ K, repCount Q π (k + 1) m = q R ^ (n - 1) * repCount Q π k m :=
  repCount_stabilizes Q hQ π hπ m hm fun h => h2 (h ▸ dvd_zero _)

/-- **Stabilization implies the local density is attained** (Hanke 2004, (5.2), p. 368, corrected): if
$r_{\pi^{k+1}}(m) = q^{n-1} r_{\pi^k}(m)$ for $k \ge K$, the normalized counts are eventually equal to
`localDensity Q π m`. -/
theorem localDensity_eventually_eq_of_stab [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n)
    (π : R) (m : R)
    (hS : ∃ K, ∀ k ≥ K, repCount Q π (k + 1) m = q R ^ (n - 1) * repCount Q π k m) :
    ∀ᶠ k in Filter.atTop,
      (repCount Q π k m : ℝ) / (q R : ℝ) ^ (k * (n - 1)) = localDensity Q π m := by
  obtain ⟨K, hK⟩ := hS
  set f : ℕ → ℝ := fun k => (repCount Q π k m : ℝ) / (q R : ℝ) ^ (k * (n - 1)) with hf
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  have hstep : ∀ k ≥ K, f (k + 1) = f k := by
    intro k hk
    simp only [hf]
    rw [hK k hk]
    push_cast
    rw [show (k + 1) * (n - 1) = (n - 1) + k * (n - 1) by ring, pow_add]
    have : (q R : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hq0
    field_simp
  have hconst : ∀ k ≥ K, f k = f K := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => rw [hstep k hk, ih]
  have hT : Filter.Tendsto f Filter.atTop (nhds (f K)) := by
    apply tendsto_const_nhds.congr'
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨K, fun k hk => (hconst k hk).symm⟩
  have hL : localDensity Q π m = f K := hT.limUnder_eq
  rw [Filter.eventually_atTop]
  exact ⟨K, fun k hk => by rw [hL]; exact hconst k hk⟩

/-- **The local density is attained over $R$** (Hanke 2004, (5.2), p. 368, corrected): for $Q$ nondegenerate,
$R/\pi$ finite, $2 \ne 0$ in $R$ and $m \ne 0$, the normalized counts $r_{\pi^k}(m)/q^{k(n-1)}$ are eventually equal to
`localDensity Q π m` (in particular the limit defining $\beta_\pi(m)$ exists). Every prime of a number field. -/
@[kb "hanke2004" "(5.2), p. 368"]
theorem localDensity_eventually_eq [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n)
    (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π) (m : R) (hm : m ≠ 0) (h20 : (2 : R) ≠ 0) :
    ∀ᶠ k in Filter.atTop, (repCount Q π k m : ℝ) / (q R : ℝ) ^ (k * (n - 1)) = localDensity Q π m :=
  localDensity_eventually_eq_of_stab Q π m (repCount_stabilizes Q hQ π hπ m hm h20)

/-- **The local density is attained over $R$ when $\pi^2 \nmid 2$** (special case of
`localDensity_eventually_eq`). -/
theorem localDensity_eventually_eq_of_not_sq_dvd_two [Finite (IsLocalRing.ResidueField R)]
    (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π) (m : R) (hm : m ≠ 0)
    (h2 : ¬ π ^ 2 ∣ 2) :
    ∀ᶠ k in Filter.atTop, (repCount Q π k m : ℝ) / (q R : ℝ) ^ (k * (n - 1)) = localDensity Q π m :=
  localDensity_eventually_eq Q hQ π hπ m hm fun h => h2 (h ▸ dvd_zero _)

end QuadFormsKB.LocalDensity.DVR
