/-
# O'Meara §95: facts about quadratic spaces over a local field used in 95:1 and 95:2

**Setting.** $F$ is a number field, $\mathfrak p$ (`v`) a finite place and $K = F_\mathfrak p$ (`v.adicCompletion F`)
O'Meara's local field (every local field of characteristic $0$ is such a completion). $(V, Q)$ is a
finite-dimensional quadratic space over $K$ (Mathlib `QuadraticForm K V`), regular meaning
`(QuadraticMap.associated Q).Nondegenerate`, with O'Meara's bilinear form $B$ = `bil Q`. $K$ is *dyadic* when
$|2|_\mathfrak p < 1$ (`Valued.v (2 : K) < 1`).

**Proves** (abstract-space versions of results of O'Meara §63 that the library has for diagonal forms)
* `S95.exists_isotropic_of_five_le` (63:19): a regular space of dimension $n \ge 5$ is isotropic;
* `S95.isSquare_prod_of_anisotropic` (63:17, the part used in step 1 of the proof of 95:1: "Note that $dV = 1$"):
  for an orthogonal base $e_0, \dots, e_3$ of an anisotropic quaternary space, $Q(e_0)\cdots Q(e_3)$ is a square;
* `S95.exists_Q_eq_of_four_le` (63:18): a regular space of dimension $n \ge 4$ is universal;
* `S95.exists_not_isSquare_mul` (63:9 in the dyadic case, $(\dot F : \dot F^2) \ge 8$): given at most four
  non-zero $\alpha_i$ there is $\xi \in \dot F$ with every $\xi\alpha_i$ a non-square;
* `S95.exists_ternary_rep` (step 2 of the proof of 95:1, p. 281): over a dyadic field, for at most four non-zero
  $\alpha_i$ an anisotropic quaternary space has a regular ternary subspace $U$ representing every $\alpha_i$
  ($V \cong \langle -\xi\rangle \perp U$, $dU = -\xi$, so $\langle -\alpha_i\rangle \perp U$ has non-square
  discriminant and is isotropic).
-/
import QuadFormsKB.Literature.OMeara.Sec82Isom
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.Literature.HasseNorm.SquareClasses
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF

open QuadraticMap Module NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace S95

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type*} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Invertible (2 : v.adicCompletion F)]
variable (Q : QuadraticForm (v.adicCompletion F) V)

local notation "Kv" => v.adicCompletion F

/-- Value of a vector combination of a pairwise orthogonal family. -/
lemma Q_comb {m : ℕ} (w : Fin m → V) (horth : ∀ i j, i ≠ j → bil Q (w i) (w j) = 0) (c : Fin m → Kv) :
    Q (∑ i, c i • w i) = ∑ i, Q (w i) * c i ^ 2 := by
  rw [Q_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [bil_self]; ring
  · intro j _ hj; rw [horth i j (Ne.symm hj)]; ring
  · simp

/-- An orthogonal family of vectors with non-zero norms is linearly independent. -/
lemma comb_ne_zero {m : ℕ} (w : Fin m → V) (horth : ∀ i j, i ≠ j → bil Q (w i) (w j) = 0)
    (hne : ∀ i, Q (w i) ≠ 0) {c : Fin m → Kv} (hc : c ≠ 0) : ∑ i, c i • w i ≠ 0 := by
  intro h
  apply hc
  funext j
  have h1 : bil Q (∑ i, c i • w i) (w j) = 0 := by rw [h]; simp [bil]
  rw [bil_sum_left, Finset.sum_eq_single j] at h1
  · rw [bil_smul_left, bil_self] at h1
    simpa [hne j] using h1
  · intro i _ hi
    rw [bil_smul_left, horth i j hi, mul_zero]
  · simp

/-- An isotropic diagonal form on an orthogonal family gives an isotropic vector. -/
lemma exists_isotropic_of_family {m : ℕ} (w : Fin m → V) (horth : ∀ i j, i ≠ j → bil Q (w i) (w j) = 0)
    (hne : ∀ i, Q (w i) ≠ 0) (hiso : (QuadForm.diag (fun i => Q (w i))).IsotropicIn Kv) :
    ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  obtain ⟨c, hc0, hc⟩ := hiso
  rw [QuadForm.evalIn_diag] at hc
  refine ⟨∑ i, c i • w i, comb_ne_zero v Q w horth hne hc0, ?_⟩
  rw [Q_comb v Q w horth]
  simpa using hc

/-- A representing diagonal form on an orthogonal family gives a vector with the given value. -/
lemma exists_Q_eq_of_family {m : ℕ} (w : Fin m → V) (horth : ∀ i j, i ≠ j → bil Q (w i) (w j) = 0)
    (α : Kv) (hrep : (QuadForm.diag (fun i => Q (w i))).RepresentsIn Kv α) : ∃ x : V, Q x = α := by
  obtain ⟨c, hc⟩ := hrep
  rw [QuadForm.evalIn_diag] at hc
  refine ⟨∑ i, c i • w i, ?_⟩
  rw [Q_comb v Q w horth]
  simpa using hc

/-- A regular space has an orthogonal basis of non-isotropic vectors. -/
lemma exists_orth_basis (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    ∃ e : Basis (Fin (finrank Kv V)) Kv V, (∀ i j, i ≠ j → bil Q (e i) (e j) = 0) ∧ ∀ i, Q (e i) ≠ 0 := by
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := QuadraticMap.associated Q) ⟨fun x y => bil_comm Q x y⟩
  refine ⟨e, fun i j hij => he hij, fun i h0 => ?_⟩
  have h1 : ∀ y, bil Q (e i) y = 0 := by
    intro y
    have : ∀ j, bil Q (e i) (e j) = 0 := fun j => by
      by_cases hij : i = j
      · subst hij; rw [bil_self]; exact h0
      · exact he hij
    have h2 : QuadraticMap.associated Q (e i) = 0 := e.ext this
    simpa using LinearMap.congr_fun h2 y
  have := hQ.1 (e i) h1
  exact e.ne_zero i this

/-- An anisotropic form is regular. -/
lemma nondeg_of_anisotropic {W : Type*} [AddCommGroup W] [Module Kv W] (Q' : QuadraticForm Kv W)
    (hQ : Q'.Anisotropic) : (QuadraticMap.associated Q').Nondegenerate := by
  refine ⟨fun x hx => hQ x ?_, fun x hx => hQ x ?_⟩
  · have := hx x; rwa [← bil_self]
  · have := hx x; rwa [← bil_self]

/-- In an anisotropic space an orthogonal family of four vectors has square product of norms. -/
lemma isSquare_prod_of_family (hQ : Q.Anisotropic) (w : Fin 4 → V)
    (horth : ∀ i j, i ≠ j → bil Q (w i) (w j) = 0) (hne : ∀ i, Q (w i) ≠ 0) :
    IsSquare (∏ i, Q (w i)) := by
  by_contra hns
  have hd : ¬ IsSquare (Q (w 0) * Q (w 1) * Q (w 2) * Q (w 3)) := by
    simpa [Fin.prod_univ_four] using hns
  obtain ⟨x, hx0, hx⟩ := exists_isotropic_of_family v Q w horth hne
    (LocalRankFive.isotropic_four_of_not_isSquare v _ hne hd)
  exact hx0 (hQ x hx)

/-- **A regular space of dimension $n \ge 5$ over $F_\mathfrak p$ is isotropic** (O'Meara 63:19, for an abstract
space). -/
theorem exists_isotropic_of_five_le (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 5 ≤ finrank (v.adicCompletion F) V) : ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  obtain ⟨e, ho, hne⟩ := exists_orth_basis v Q hQ
  exact exists_isotropic_of_family v Q (fun i : Fin 5 => e (Fin.castLE hn i))
    (fun i j hij => ho _ _ (fun h => hij (Fin.castLE_injective hn h))) (fun i => hne _)
    (LocalRankFive.isotropic_diag_five v _ (fun i => hne _))

/-- **$dV = 1$ for an anisotropic quaternary space** (O'Meara 63:17, as used in step 1 of the proof of 95:1,
p. 281): for an orthogonal base $e_0, \dots, e_3$, the product $Q(e_0)Q(e_1)Q(e_2)Q(e_3)$ is a square. -/
theorem isSquare_prod_of_anisotropic (hQ : Q.Anisotropic) (e : Basis (Fin 4) (v.adicCompletion F) V)
    (horth : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) : IsSquare (∏ i, Q (e i)) :=
  isSquare_prod_of_family v Q hQ e horth (fun i h0 => e.ne_zero i (hQ _ h0))

/-- **A regular space of dimension $n \ge 4$ over $F_\mathfrak p$ is universal** (O'Meara 63:18, for an abstract
space): every $\alpha \in F_\mathfrak p$ is a value $Q(x)$. -/
theorem exists_Q_eq_of_four_le (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : 4 ≤ finrank (v.adicCompletion F) V) (α : v.adicCompletion F) : ∃ x : V, Q x = α := by
  obtain ⟨e, ho, hne⟩ := exists_orth_basis v Q hQ
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  exact exists_Q_eq_of_family v Q (fun i : Fin 4 => e (Fin.castLE hn i))
    (fun i j hij => ho _ _ (fun h => hij (Fin.castLE_injective hn h))) α
    (PadicClass.represents_of_four_le hK (a := fun i : Fin 4 => Q (e (Fin.castLE hn i)))
      (fun i => hne _) le_rfl α)

/-- **Avoiding four square classes** (O'Meara 1973, proof of 95:1, step 2, p. 281, from 63:9: over a dyadic field
$(\dot F : \dot F^2) \ge 8$): for at most four non-zero $\alpha_i$ there is $\xi \ne 0$ with every $\xi\alpha_i$ a
non-square. -/
theorem exists_not_isSquare_mul (h2 : Valued.v (2 : v.adicCompletion F) < 1) (l : List (v.adicCompletion F))
    (hl0 : ∀ α ∈ l, α ≠ 0) (hlen : l.length ≤ 4) :
    ∃ ξ : v.adicCompletion F, ξ ≠ 0 ∧ ∀ α ∈ l, ¬ IsSquare (ξ * α) := by
  classical
  by_contra hcon
  push Not at hcon
  have hcon' : ∀ ξ : Kv, ξ ≠ 0 → ∃ α ∈ l, IsSquare (ξ * α) := by
    intro ξ hξ
    obtain ⟨α, hα, h⟩ := hcon ξ hξ
    exact ⟨α, hα, h⟩
  set H := (powMonoidHom 2 : Kvˣ →* Kvˣ).range with hH
  have hidx := HN.index_sq_completion v
  have he : 1 ≤ HN.ordTwo v := by
    by_contra h0
    have h0' : HN.ordTwo v = 0 := by omega
    have := HN.valued_two v
    rw [h0'] at this
    simp at this
    rw [this] at h2
    exact lt_irrefl _ h2
  have hN : 2 ≤ Ideal.absNorm v.asIdeal := by
    have h1 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    have h2' : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega
  have h8 : 8 ≤ H.index := by
    rw [hidx]
    calc 8 = 4 * 2 := by norm_num
      _ ≤ 4 * Ideal.absNorm v.asIdeal ^ HN.ordTwo v := by
        gcongr
        calc 2 ≤ Ideal.absNorm v.asIdeal := hN
          _ = Ideal.absNorm v.asIdeal ^ 1 := (pow_one _).symm
          _ ≤ _ := Nat.pow_le_pow_right (by omega) he
  have hsurj : Function.Surjective
      (fun a : l.toFinset => (QuotientGroup.mk (Units.mk0 a.1 (hl0 a.1 (List.mem_toFinset.mp a.2)))⁻¹ :
        Kvˣ ⧸ H)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨α, hα, r, hr⟩ := hcon' g.1 g.ne_zero
      refine ⟨⟨α, List.mem_toFinset.mpr hα⟩, ?_⟩
      show QuotientGroup.mk _ = _
      rw [QuotientGroup.eq]
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hr
        exact mul_ne_zero g.ne_zero (hl0 α hα) hr
      refine ⟨Units.mk0 r hr0, ?_⟩
      ext
      simp [hr, mul_comm, pow_two]
  have hle : Nat.card (Kvˣ ⧸ H) ≤ Nat.card l.toFinset :=
    Nat.card_le_card_of_surjective _ hsurj
  have : Nat.card l.toFinset ≤ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact (List.toFinset_card_le l).trans hlen
  have hidx2 : H.index = Nat.card (Kvˣ ⧸ H) := rfl
  omega

/-- **A ternary subspace representing four values** (O'Meara 1973, proof of 95:1, step 2, p. 281): let $V$ be an
anisotropic quaternary space over a dyadic field and $\alpha_1, \dots, \alpha_r$ ($r \le 4$) non-zero. Then some
regular ternary subspace $U$ of $V$ represents every $\alpha_i$. -/
theorem exists_ternary_rep (h2 : Valued.v (2 : v.adicCompletion F) < 1) (hQ : Q.Anisotropic)
    (hn : finrank (v.adicCompletion F) V = 4) (l : List (v.adicCompletion F)) (hl0 : ∀ α ∈ l, α ≠ 0)
    (hlen : l.length ≤ 4) :
    ∃ U : Submodule (v.adicCompletion F) V, finrank (v.adicCompletion F) U = 3 ∧
      (QuadraticMap.associated (Q.comp U.subtype)).Nondegenerate ∧ ∀ α ∈ l, ∃ u : U, Q (u : V) = α := by
  classical
  obtain ⟨ξ, hξ0, hξ⟩ := exists_not_isSquare_mul v h2 l hl0 hlen
  have hnd := nondeg_of_anisotropic v Q hQ
  obtain ⟨x0, hx0⟩ := exists_Q_eq_of_four_le v Q hnd (by omega) (-ξ)
  have hbx : QuadraticMap.associated Q x0 x0 = -ξ := by rw [← hx0]; exact bil_self Q x0
  set U : Submodule Kv V := LinearMap.ker (QuadraticMap.associated Q x0) with hU
  have hU3 : finrank Kv U = 3 := by
    have hrange : LinearMap.range (QuadraticMap.associated Q x0) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      refine ⟨(c / (-ξ)) • x0, ?_⟩
      rw [map_smul, hbx, smul_eq_mul]
      field_simp
    have := LinearMap.finrank_range_add_finrank_ker (QuadraticMap.associated Q x0)
    rw [hrange, finrank_top, finrank_self, hn, ← hU] at this
    omega
  set Q' := Q.comp U.subtype with hQ'
  have hQ'a : Q'.Anisotropic := fun u hu => Subtype.ext (hQ (u : V) hu)
  have hbil : ∀ a b : U, bil Q' a b = bil Q (a : V) (b : V) := by
    intro a b
    rw [bil_eq_half, bil_eq_half]
    simp [hQ', QuadraticMap.comp_apply]
  obtain ⟨u, hu⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := QuadraticMap.associated Q')
    ⟨fun x y => bil_comm Q' x y⟩
  set c : Fin 3 → Fin (finrank Kv U) := Fin.cast hU3.symm with hc
  have hcinj : ∀ i j, i ≠ j → c i ≠ c j := fun i j hij h => hij (Fin.ext (by simpa [hc] using congrArg Fin.val h))
  set W3 : Fin 3 → V := fun i => (u (c i) : V) with hW3
  have horth3 : ∀ i j, i ≠ j → bil Q (W3 i) (W3 j) = 0 := fun i j hij => by
    rw [← hbil]; exact hu (hcinj i j hij)
  have hne3 : ∀ i, Q (W3 i) ≠ 0 := fun i h0 => by
    have : (u (c i) : V) = 0 := hQ _ h0
    exact u.ne_zero (c i) (Subtype.ext this)
  have hperp : ∀ i, bil Q x0 (W3 i) = 0 := fun i => LinearMap.mem_ker.mp (u (c i)).2
  set W4 : Fin 4 → V := Fin.cons x0 W3 with hW4
  have horth4 : ∀ i j, i ≠ j → bil Q (W4 i) (W4 j) = 0 := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => simpa [hW4] using hperp j
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa [hW4, bil_comm Q _ x0] using hperp i
      | succ j => simpa [hW4] using horth3 i j (fun h => hij (by rw [h]))
  have hne4 : ∀ i, Q (W4 i) ≠ 0 := by
    intro i
    induction i using Fin.cases with
    | zero => simpa [hW4, hx0] using hξ0
    | succ i => simpa [hW4] using hne3 i
  have hsq := isSquare_prod_of_family v Q hQ W4 horth4 hne4
  rw [Fin.prod_univ_succ] at hsq
  simp only [hW4, Fin.cons_zero, Fin.cons_succ, hx0] at hsq
  obtain ⟨s, hs⟩ := hsq
  set P : Kv := ∏ i : Fin 3, Q (W3 i) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne3 i
  refine ⟨U, hU3, nondeg_of_anisotropic v Q' hQ'a, fun α hα => ?_⟩
  have hα0 := hl0 α hα
  have hnsq : ¬ IsSquare (P * (-α)) := by
    rintro ⟨r, hr⟩
    apply hξ α hα
    refine ⟨s * r / P, ?_⟩
    field_simp
    linear_combination (P * (-α)) * hs + (s * s) * hr
  have hb : ∀ i, (![Q (W3 0), Q (W3 1), Q (W3 2), -α] : Fin 4 → Kv) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hne3, hα0]
  have hd : ¬ IsSquare ((![Q (W3 0), Q (W3 1), Q (W3 2), -α] : Fin 4 → Kv) 0 *
      (![Q (W3 0), Q (W3 1), Q (W3 2), -α] : Fin 4 → Kv) 1 *
      (![Q (W3 0), Q (W3 1), Q (W3 2), -α] : Fin 4 → Kv) 2 *
      (![Q (W3 0), Q (W3 1), Q (W3 2), -α] : Fin 4 → Kv) 3) := by
    have : P = Q (W3 0) * Q (W3 1) * Q (W3 2) := by rw [hP, Fin.prod_univ_three]
    simpa [this] using hnsq
  obtain ⟨y, hy0, hy⟩ := LocalRankFive.isotropic_four_of_not_isSquare v _ hb hd
  rw [LocalRankFive.evalIn_diag_four] at hy
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hy
  have hy' : Q (W3 0) * y 0 ^ 2 + Q (W3 1) * y 1 ^ 2 + Q (W3 2) * y 2 ^ 2 = α * y 3 ^ 2 := by
    linear_combination hy
  set cc : Fin 3 → Kv := ![y 0, y 1, y 2] with hcc
  have hQz : ∀ t : Kv, t ≠ 0 → Q (∑ i, (cc i / t) • W3 i) = α * y 3 ^ 2 / t ^ 2 := by
    intro t ht
    rw [Q_comb v Q W3 horth3]
    simp only [hcc, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp
    linear_combination hy'
  by_cases ht : y 3 = 0
  · exfalso
    have hcc0 : cc ≠ 0 := by
      intro h
      apply hy0
      funext i
      fin_cases i
      · simpa [hcc] using congrFun h 0
      · simpa [hcc] using congrFun h 1
      · simpa [hcc] using congrFun h 2
      · simpa using ht
    have hz : Q (∑ i, cc i • W3 i) = 0 := by
      rw [Q_comb v Q W3 horth3]
      simp only [hcc, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [ht] at hy'
      linear_combination hy'
    exact comb_ne_zero v Q W3 horth3 hne3 hcc0 (hQ _ hz)
  · refine ⟨∑ i, (cc i / y 3) • u (c i), ?_⟩
    have : ((∑ i, (cc i / y 3) • u (c i) : U) : V) = ∑ i, (cc i / y 3) • W3 i := by
      simp [hW3]
    rw [this, hQz _ ht]
    field_simp

end S95

end QuadFormsKB.OMeara
