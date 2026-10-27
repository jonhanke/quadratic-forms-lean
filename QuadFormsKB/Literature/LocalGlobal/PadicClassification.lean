/-
# Classification of quadratic forms over $\mathbb{Q}_p$ (Serre IV §2.2–2.3)

**Main results** (all for nondegenerate diagonal forms with coefficients in $\mathbb{Q}^\times$,
over $\mathbb{Q}_p$, every prime $p$ including $2$; indices are 0-based):

* `hasseInvariant_isometric`: the Hasse invariant
  $\varepsilon = \prod_{0 \le i < j < n} (a_i, a_j)_p$ is an isometry invariant (Serre IV §2.1).
* `represents_padic_one_iff`, `represents_padic_two_iff`, `represents_padic_three_iff`,
  `represents_padic_of_four_le`: the representation criterion (Serre IV §2.2, Thm. 6). With
  $d = \prod_i a_i$: rank 1 represents $x$ iff $x \equiv d$; rank 2 iff $(x, -d) = \varepsilon$;
  rank 3 iff $x \not\equiv -d$ or $(-1, -d) = \varepsilon$; rank $\ge 4$ always.
* `isometric_padic_iff_invariants`: the classification (Serre IV §2.3, Thm. 7): same rank,
  same discriminant square class and same Hasse invariant iff isometric. `isometric_padic_iff`
  (`HasseMinkowski.lean`) is this theorem.

**Structure of the proof.** Everything is first proved over an abstract field $K$ of
characteristic $0$ whose Hilbert symbol satisfies three axioms (`PadicClass.LocalHilbertField`):
bimultiplicativity, nondegeneracy ($a$ not a square $\Rightarrow$ $(a, x) = -1$ for some $x$), and
isotropy of every nondegenerate diagonal form of rank $5$. The diagonal coefficients then live in
$K$ (`PadicClass.hasseVec`), so splitting off represented values stays inside the class of diagonal
forms. `PadicClass.localHilbertField_padic` checks the axioms for $\mathbb{Q}_p$: bimultiplicativity
is `HilbertLocal.hilbertSymbol_padic_mul_left`; nondegeneracy comes from the explicit formulas
(`HilbertLocal.hilbertSymbol_odd_formula`, `hilbertSymbol_two_formula`); rank-5 isotropy reduces to
rational coefficients (`Prescribed.exists_rat_sq_class`) and `RankFive`.

* Thm. 6, rank 2: $\langle a_0, a_1 \rangle$ represents $x$ iff $\langle a_0, a_1, -x \rangle$ is
  isotropic iff $(x, -a_0 a_1) = (a_0, a_1)$.
* Rank 3: $\langle a_0, a_1, a_2, -x \rangle$ is isotropic iff $\langle a_0, a_1 \rangle$ and
  $\langle -a_2, x \rangle$ represent a common value, i.e. two Hilbert symbols are prescribed; the
  $\mathbb{F}_2$-linear algebra of `exists_hs_eq_iff` (from nondegeneracy) decides this.
* Invariance of $\varepsilon$: ranks $2, 3$ because the set of represented values is an isometry
  invariant and determines $\varepsilon$; rank $\ge 4$ by induction, splitting off a value $c$
  represented by both $\langle a_1, \dots \rangle$ and $\langle b_1, \dots \rangle$ and cancelling
  $\langle c \rangle$ (Witt). This replaces Serre's appeal to Witt's chain-equivalence theorem
  (IV §1.7, Thm. 4).
* Classification "⇐": induction on $n$, splitting off $a_0$ from both forms (Serre's proof).

Sources: Serre, *A Course in Arithmetic*, Ch. IV §2.1–2.3; Cassels, *Rational Quadratic Forms*,
Ch. 4, Thm. 1.1, p. 55 (classification over $\mathbb{Q}_p$ by $n$, $d$, $c$), Thm. 1.2, p. 56 (over $\mathbb{R}$), Lemma 2.2,
p. 57, and Cor. 1, p. 58 (invariance of $c = \prod_{i<j}(a_i,a_j)$, Serre's $\varepsilon$); Lam, *Introduction to Quadratic Forms
over Fields*, Ch. V §3 (Lam locators [unverified]).
-/
import QuadFormsKB.Witt.Represents

set_option linter.unusedSectionVars false

namespace QuadFormsKB.PadicClass

open QuadForm Matrix

section Hilbert

variable {K : Type*} [Field K] [CharZero K]

/-- **Axioms on the Hilbert symbol of a field $K$** used for the classification (all hold for
$K = \mathbb{Q}_p$, `localHilbertField_padic`):
* `mul_left`: $(a a', b)_K = (a, b)_K (a', b)_K$ for $a, a', b \in K^\times$;
* `exists_neg_one`: if $a \in K^\times$ is not a square, then $(a, x)_K = -1$ for some
  $x \in K^\times$ (nondegeneracy);
* `isotropic_five`: every diagonal form $\langle a_0, \dots, a_4 \rangle$ with all $a_i \ne 0$ is
  isotropic over $K$. -/
structure LocalHilbertField (K : Type*) [Field K] [CharZero K] : Prop where
  mul_left : ∀ a a' b : K, a ≠ 0 → a' ≠ 0 → b ≠ 0 →
    hilbertSymbol K (a * a') b = hilbertSymbol K a b * hilbertSymbol K a' b
  exists_neg_one : ∀ a : K, a ≠ 0 → ¬ IsSquare a → ∃ x : K, x ≠ 0 ∧ hilbertSymbol K a x = -1
  isotropic_five : ∀ a : Fin 5 → K, (∀ i, a i ≠ 0) → (diag a).IsotropicIn K

theorem hs_pm (a b : K) : hilbertSymbol K a b = 1 ∨ hilbertSymbol K a b = -1 := by
  unfold hilbertSymbol; split_ifs <;> simp

theorem hs_sq_left (a b c : K) (hc : c ≠ 0) :
    hilbertSymbol K (c ^ 2 * a) b = hilbertSymbol K a b := by
  rw [mul_comm]; exact HM3.hilbertSymbol_mul_sq_left K a b c hc

theorem hs_sq_right (a b c : K) (hc : c ≠ 0) :
    hilbertSymbol K a (c ^ 2 * b) = hilbertSymbol K a b := by
  rw [hilbertSymbol_comm, hs_sq_left _ _ _ hc, hilbertSymbol_comm]

theorem hs_sq (a c : K) (hc : c ≠ 0) : hilbertSymbol K a (c ^ 2) = 1 := by
  have := hs_sq_right a 1 c hc
  rw [mul_one] at this
  rw [this, hilbertSymbol_one_right]

theorem hs_one_left (a : K) : hilbertSymbol K 1 a = 1 := by
  rw [hilbertSymbol_comm, hilbertSymbol_one_right]

theorem hs_of_isSquare (x A : K) (hA : A ≠ 0) (h : IsSquare A) : hilbertSymbol K x A = 1 := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := by rintro rfl; simp at hA
  rw [← sq]; exact hs_sq x r hr

variable (hK : LocalHilbertField K)
include hK

theorem LocalHilbertField.mul_right {a b b' : K} (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSymbol K a (b * b') = hilbertSymbol K a b * hilbertSymbol K a b' := by
  rw [hilbertSymbol_comm, hK.mul_left _ _ _ hb hb' ha, hilbertSymbol_comm K b,
    hilbertSymbol_comm K b']

theorem LocalHilbertField.self {a : K} (ha : a ≠ 0) :
    hilbertSymbol K a a = hilbertSymbol K a (-1) := by
  have h := hilbertSymbol_self_neg K a
  rw [show -a = -1 * a by ring, hK.mul_right ha (by norm_num) ha] at h
  rcases hs_pm a (-1 : K) with h1 | h1 <;> rw [h1] at h ⊢ <;> linarith

theorem LocalHilbertField.exists_sep {A B : K} (hA : A ≠ 0) (hB : B ≠ 0) (hBs : ¬ IsSquare B)
    (hABs : ¬ IsSquare (A * B)) :
    ∃ v : K, v ≠ 0 ∧ hilbertSymbol K v A = 1 ∧ hilbertSymbol K v B = -1 := by
  obtain ⟨z, hz0, hz⟩ := hK.exists_neg_one B hB hBs
  rw [hilbertSymbol_comm] at hz
  rcases hs_pm z A with h | h
  · exact ⟨z, hz0, h, hz⟩
  obtain ⟨w, hw0, hw⟩ := hK.exists_neg_one (A * B) (mul_ne_zero hA hB) hABs
  rw [hilbertSymbol_comm, hK.mul_right hw0 hA hB] at hw
  rcases hs_pm w A with h' | h'
  · rw [h', one_mul] at hw; exact ⟨w, hw0, h', hw⟩
  · refine ⟨z * w, mul_ne_zero hz0 hw0, ?_, ?_⟩
    · rw [hK.mul_left _ _ _ hz0 hw0 hA, h, h']; norm_num
    · rw [hK.mul_left _ _ _ hz0 hw0 hB, hz]
      rw [h'] at hw
      have : hilbertSymbol K w B = 1 := by linarith
      rw [this]; norm_num

/-- **Prescribing two Hilbert symbols** (Serre III §2.2 / IV §2.2, the counting argument behind
Thm. 6, rank 4). -/
theorem LocalHilbertField.exists_hs_eq_iff {A B : K} (hA : A ≠ 0) (hB : B ≠ 0) {e₁ e₂ : ℤ}
    (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1) :
    (∃ x : K, x ≠ 0 ∧ hilbertSymbol K x A = e₁ ∧ hilbertSymbol K x B = e₂) ↔
      (IsSquare A → e₁ = 1) ∧ (IsSquare B → e₂ = 1) ∧ (IsSquare (A * B) → e₁ = e₂) := by
  constructor
  · rintro ⟨x, hx, h1, h2⟩
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [← h1, hs_of_isSquare x A hA h]
    · rw [← h2, hs_of_isSquare x B hB h]
    · have := hs_of_isSquare x _ (mul_ne_zero hA hB) h
      rw [hK.mul_right hx hA hB, h1, h2] at this
      rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;> first | rfl | norm_num at this
  · rintro ⟨C1, C2, C3⟩
    obtain ⟨u, hu0, hu⟩ : ∃ u : K, u ≠ 0 ∧ hilbertSymbol K u A = e₁ := by
      rcases he₁ with rfl | rfl
      · exact ⟨1, one_ne_zero, hs_one_left A⟩
      · have hAs : ¬ IsSquare A := fun h => by have := C1 h; norm_num at this
        obtain ⟨u, hu0, hu⟩ := hK.exists_neg_one A hA hAs
        exact ⟨u, hu0, by rw [hilbertSymbol_comm]; exact hu⟩
    by_cases hub : hilbertSymbol K u B = e₂
    · exact ⟨u, hu0, hu, hub⟩
    have hub' : hilbertSymbol K u B = -e₂ := by
      rcases hs_pm u B with h | h <;> rcases he₂ with rfl | rfl <;> simp_all
    have hBs : ¬ IsSquare B := fun h => by
      have h1 := hs_of_isSquare u B hB h
      have h2 := C2 h
      rw [h1, h2] at hub; exact hub rfl
    have hABs : ¬ IsSquare (A * B) := fun h => by
      have h1 := hs_of_isSquare u _ (mul_ne_zero hA hB) h
      rw [hK.mul_right hu0 hA hB, hu, hub'] at h1
      have h2 := C3 h
      subst h2
      rcases he₁ with rfl | rfl <;> norm_num at h1
    obtain ⟨v, hv0, hvA, hvB⟩ := hK.exists_sep hA hB hBs hABs
    refine ⟨u * v, mul_ne_zero hu0 hv0, ?_, ?_⟩
    · rw [hK.mul_left _ _ _ hu0 hv0 hA, hu, hvA, mul_one]
    · rw [hK.mul_left _ _ _ hu0 hv0 hB, hub', hvB]; ring

end Hilbert

section Diag

variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}

theorem evalIn_diag_self (a : Fin n → K) (x : Fin n → K) :
    (diag a).evalIn K x = ∑ i, a i * x i ^ 2 := by
  rw [evalIn_diag]; simp

theorem representsIn_diag_iff (a : Fin n → K) (c : K) :
    (diag a).RepresentsIn K c ↔ ∃ y : Fin n → K, ∑ i, a i * y i ^ 2 = c := by
  simp [RepresentsIn, evalIn_diag_self]

theorem isotropicIn_diag_iff (a : Fin n → K) :
    (diag a).IsotropicIn K ↔ ∃ y : Fin n → K, y ≠ 0 ∧ ∑ i, a i * y i ^ 2 = 0 := by
  simp [IsotropicIn, evalIn_diag_self]

theorem isotropicIn_orthSum_diag_iff (a : Fin m → K) (b : Fin n → K) :
    (orthSum (diag a) (diag b)).IsotropicIn K ↔ (diag (Fin.append a b)).IsotropicIn K := by
  have : ∀ x : Fin (m + n) → K,
      (orthSum (diag a) (diag b)).evalIn K x = (diag (Fin.append a b)).evalIn K x := by
    intro x
    rw [evalIn_orthSum, evalIn_diag_self, evalIn_diag_self, evalIn_diag_self, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  simp only [IsotropicIn, this]

/-- A nondegenerate diagonal form represents $c \ne 0$ iff $\langle a \rangle \perp \langle -c \rangle$
is isotropic. -/
theorem representsIn_diag_iff_isotropic {a : Fin n → K} (ha : ∀ i, a i ≠ 0) (c : K) :
    (diag a).RepresentsIn K c ↔ (diag (Fin.append a ![-c])).IsotropicIn K := by
  rw [representsIn_iff_isotropicIn_orthSum K (nondegenerate_diag ha) c,
    isotropicIn_orthSum_diag_iff]

theorem append_two_one (a₀ a₁ c : K) : Fin.append ![a₀, a₁] ![c] = ![a₀, a₁, c] := by
  funext i; fin_cases i <;> rfl

theorem append_three_one (a₀ a₁ a₂ c : K) : Fin.append ![a₀, a₁, a₂] ![c] = ![a₀, a₁, a₂, c] := by
  funext i; fin_cases i <;> rfl

/-- An isotropic nondegenerate diagonal form represents every element. -/
theorem representsIn_of_isotropic {a : Fin n → K} (ha : ∀ i, a i ≠ 0)
    (hiso : (diag a).IsotropicIn K) (c : K) : (diag a).RepresentsIn K c := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, by simp [QuadForm.evalIn]⟩
  rw [representsIn_diag_iff_isotropic ha]
  obtain ⟨y, hy0, hy⟩ := (isotropicIn_diag_iff a).mp hiso
  refine (isotropicIn_diag_iff _).mpr ⟨Fin.append y ![0], fun h => hy0 ?_, ?_⟩
  · funext i
    have := congrFun h (Fin.castAdd 1 i)
    simpa [Fin.append_left] using this
  · rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, hy]

end Diag

section Binary

variable {K : Type*} [Field K] [CharZero K] (hK : LocalHilbertField K)
include hK

/-- **Thm. 6, rank 2** (Serre IV §2.2): for $a_0, a_1, x \in K^\times$,
$\langle a_0, a_1 \rangle$ represents $x$ iff $(x, -a_0 a_1) = (a_0, a_1)$. -/
@[kb "omeara1963" "§63C, 63:21, p. 170 (U a line); §63C, 63:15 (ii), p. 168; cassels1978 Ch. 4, Lemma 2.1 and Cor. 2 to Lemma 2.2, pp. 56–58"]
theorem represents_two_iff {a₀ a₁ : K} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) {x : K} (hx : x ≠ 0) :
    (diag ![a₀, a₁]).RepresentsIn K x ↔
      hilbertSymbol K x (-(a₀ * a₁)) = hilbertSymbol K a₀ a₁ := by
  have ha : ∀ i, (![a₀, a₁] : Fin 2 → K) i ≠ 0 := fun i => by fin_cases i <;> simpa
  rw [representsIn_diag_iff_isotropic ha, append_two_one,
    FieldGen.isotropic_diag_three_iff K a₀ a₁ (-x) h₀ h₁ (neg_ne_zero.mpr hx)]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, neg_neg]
  have hi : a₀⁻¹ ≠ 0 := inv_ne_zero h₀
  have e1 : -a₁ / a₀ = a₀⁻¹ ^ 2 * (-(a₀ * a₁)) := by field_simp
  have e2 : x / a₀ = a₀⁻¹ ^ 2 * (a₀ * x) := by field_simp
  have hd : -(a₀ * a₁) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero h₀ h₁)
  rw [e1, e2, hs_sq_left _ _ _ hi, hs_sq_right _ _ _ hi, hK.mul_right hd h₀ hx,
    hilbertSymbol_comm K _ a₀, show -(a₀ * a₁) = -a₀ * a₁ by ring,
    hK.mul_right h₀ (neg_ne_zero.mpr h₀) h₁, hilbertSymbol_self_neg, one_mul,
    hilbertSymbol_comm K (-a₀ * a₁) x]
  rcases hs_pm a₀ a₁ with h | h <;> rcases hs_pm x (-a₀ * a₁) with h' | h' <;>
    rw [h, h'] <;> norm_num

/-- A binary form $\langle a_0, a_1 \rangle$ with $-a_0 a_1$ a square has $(a_0, a_1) = 1$. -/
theorem hs_eq_one_of_isSquare_neg_mul {a₀ a₁ : K} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0)
    (h : IsSquare (-(a₀ * a₁))) : hilbertSymbol K a₀ a₁ = 1 := by
  obtain ⟨r, hr⟩ := h
  have e : a₁ = (r / a₀) ^ 2 * (-a₀) := by
    rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 h₀)]
    linear_combination (-a₀) * hr
  have hr0 : r / a₀ ≠ 0 := by
    intro h0; rw [h0] at e; simp at e; exact h₁ e
  rw [e, hs_sq_right _ _ _ hr0, hilbertSymbol_self_neg]

/-- An isotropic binary form represents everything. -/
theorem represents_two_of_isSquare {a₀ a₁ : K} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0)
    (h : IsSquare (-(a₀ * a₁))) (x : K) : (diag ![a₀, a₁]).RepresentsIn K x := by
  have ha : ∀ i, (![a₀, a₁] : Fin 2 → K) i ≠ 0 := fun i => by fin_cases i <;> simpa
  refine representsIn_of_isotropic ha ?_ x
  rw [FieldGen.isotropic_diag_two_iff K a₀ a₁ h₀ h₁]
  simpa using h

end Binary

section Rank34

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- A quaternary diagonal form $\langle g_0, g_1, g_2, g_3 \rangle$ is isotropic iff
$\langle g_0, g_1 \rangle$ and $\langle -g_2, -g_3 \rangle$ represent a common $x \ne 0$
(Serre IV §2.2, proof of Thm. 6). -/
@[kb "cassels1978" "Ch. 4, Lemma 2.6, p. 59"]
theorem isotropic_four_iff_common {g₀ g₁ g₂ g₃ : K} (h₀ : g₀ ≠ 0) (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0)
    (h₃ : g₃ ≠ 0) :
    (diag ![g₀, g₁, g₂, g₃]).IsotropicIn K ↔
      ∃ x : K, x ≠ 0 ∧ (diag ![g₀, g₁]).RepresentsIn K x ∧ (diag ![-g₂, -g₃]).RepresentsIn K x := by
  simp only [isotropicIn_diag_iff, representsIn_diag_iff, Fin.sum_univ_four, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  constructor
  · rintro ⟨y, hy0, hy⟩
    by_cases ht : g₀ * y 0 ^ 2 + g₁ * y 1 ^ 2 = 0
    · by_cases h01 : y 0 = 0 ∧ y 1 = 0
      · -- ⟨-g₂, -g₃⟩ is isotropic, so it represents g₀
        have h23 : ¬ (y 2 = 0 ∧ y 3 = 0) := by
          rintro ⟨h2, h3⟩; apply hy0; funext i; fin_cases i <;> simp [h01.1, h01.2, h2, h3]
        have hiso : (diag ![-g₂, -g₃]).IsotropicIn K := by
          rw [isotropicIn_diag_iff]
          refine ⟨![y 2, y 3], fun h => h23 ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩, ?_⟩
          simp [Fin.sum_univ_two]; linear_combination -hy + ht
        have hr := representsIn_of_isotropic (a := ![-g₂, -g₃])
          (fun i => by fin_cases i <;> simpa) hiso g₀
        rw [representsIn_diag_iff] at hr
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hr
        exact ⟨g₀, h₀, ⟨![1, 0], by simp⟩, hr⟩
      · have hiso : (diag ![g₀, g₁]).IsotropicIn K := by
          rw [isotropicIn_diag_iff]
          refine ⟨![y 0, y 1], fun h => h01 ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩, ?_⟩
          simp [Fin.sum_univ_two]; linear_combination ht
        have hr := representsIn_of_isotropic (a := ![g₀, g₁])
          (fun i => by fin_cases i <;> simpa) hiso (-g₂)
        rw [representsIn_diag_iff] at hr
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hr
        exact ⟨-g₂, neg_ne_zero.mpr h₂, hr, ⟨![1, 0], by simp⟩⟩
    · exact ⟨_, ht, ⟨![y 0, y 1], by simp⟩, ⟨![y 2, y 3], by simp; linear_combination -hy⟩⟩
  · rintro ⟨x, hx, ⟨y, hy⟩, ⟨z, hz⟩⟩
    refine ⟨![y 0, y 1, z 0, z 1], fun h => hx ?_, ?_⟩
    · have e0 := congrFun h 0; have e1 := congrFun h 1
      simp at e0 e1
      rw [← hy, e0, e1]; ring
    · simp; linear_combination hy - hz

variable (hK : LocalHilbertField K)
include hK

/-- The Hilbert-symbol identity behind Thm. 6, rank 3:
$(-a_2, -d) = (-1, -d)(a_0, a_2)(a_1, a_2)$ for $d = a_0 a_1 a_2$. -/
theorem hs_neg_a2_neg_d {a₀ a₁ a₂ : K} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) :
    hilbertSymbol K (-a₂) (-(a₀ * a₁ * a₂)) =
      hilbertSymbol K (-1) (-(a₀ * a₁ * a₂)) * hilbertSymbol K a₀ a₂ * hilbertSymbol K a₁ a₂ := by
  have hd : -(a₀ * a₁ * a₂) ≠ 0 := by simp [h₀, h₁, h₂]
  rw [show -a₂ = -1 * a₂ by ring, hK.mul_left _ _ _ (by norm_num) h₂ hd,
    show -(a₀ * a₁ * a₂) = -a₂ * (a₀ * a₁) by ring,
    hK.mul_right h₂ (neg_ne_zero.mpr h₂) (mul_ne_zero h₀ h₁), hilbertSymbol_self_neg, one_mul,
    hK.mul_right h₂ h₀ h₁, hilbertSymbol_comm K a₂ a₀, hilbertSymbol_comm K a₂ a₁]
  ring

/-- **Thm. 6, rank 3** (Serre IV §2.2): for $a_0, a_1, a_2, x \in K^\times$ with $d = a_0 a_1 a_2$ and
$\varepsilon = (a_0,a_1)(a_0,a_2)(a_1,a_2)$, $\langle a_0, a_1, a_2 \rangle$ represents $x$ iff
$x \not\equiv -d$ modulo squares, or $(-1,-d) = \varepsilon$. -/
@[kb "omeara1963" "§63C, 63:21, p. 170 (U a line); cassels1978 Ch. 4, Lemma 2.5, p. 59"]
theorem represents_three_iff {a₀ a₁ a₂ : K} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) {x : K}
    (hx : x ≠ 0) :
    (diag ![a₀, a₁, a₂]).RepresentsIn K x ↔
      ((∃ t : K, t ≠ 0 ∧ x = t ^ 2 * (-(a₀ * a₁ * a₂))) →
        hilbertSymbol K (-1) (-(a₀ * a₁ * a₂)) =
          hilbertSymbol K a₀ a₁ * hilbertSymbol K a₀ a₂ * hilbertSymbol K a₁ a₂) := by
  have ha : ∀ i, (![a₀, a₁, a₂] : Fin 3 → K) i ≠ 0 := fun i => by fin_cases i <;> simpa
  rw [representsIn_diag_iff_isotropic ha, append_three_one,
    isotropic_four_iff_common h₀ h₁ h₂ (neg_ne_zero.mpr hx), neg_neg]
  have step : (∃ y : K, y ≠ 0 ∧ (diag ![a₀, a₁]).RepresentsIn K y ∧
      (diag ![-a₂, x]).RepresentsIn K y) ↔
      ∃ y : K, y ≠ 0 ∧ hilbertSymbol K y (-(a₀ * a₁)) = hilbertSymbol K a₀ a₁ ∧
        hilbertSymbol K y (-(-a₂ * x)) = hilbertSymbol K (-a₂) x := by
    refine exists_congr fun y => ⟨fun ⟨hy, r1, r2⟩ => ⟨hy, ?_, ?_⟩, fun ⟨hy, r1, r2⟩ => ⟨hy, ?_, ?_⟩⟩
    · exact (represents_two_iff hK h₀ h₁ hy).mp r1
    · exact (represents_two_iff hK (neg_ne_zero.mpr h₂) hx hy).mp r2
    · exact (represents_two_iff hK h₀ h₁ hy).mpr r1
    · exact (represents_two_iff hK (neg_ne_zero.mpr h₂) hx hy).mpr r2
  have hA : -(a₀ * a₁) ≠ 0 := by simp [h₀, h₁]
  have hB : -(-a₂ * x) ≠ 0 := by simp [h₂, hx]
  rw [step, hK.exists_hs_eq_iff hA hB (hs_pm _ _) (hs_pm _ _)]
  have C1 : IsSquare (-(a₀ * a₁)) → hilbertSymbol K a₀ a₁ = 1 :=
    hs_eq_one_of_isSquare_neg_mul hK h₀ h₁
  have C2 : IsSquare (-(-a₂ * x)) → hilbertSymbol K (-a₂) x = 1 :=
    hs_eq_one_of_isSquare_neg_mul hK (neg_ne_zero.mpr h₂) hx
  have hd : -(a₀ * a₁ * a₂) ≠ 0 := by simp [h₀, h₁, h₂]
  have key := hs_neg_a2_neg_d hK h₀ h₁ h₂
  have pm : ∀ u v w z : ℤ, (u = 1 ∨ u = -1) → (v = 1 ∨ v = -1) → (w = 1 ∨ w = -1) →
      (z = 1 ∨ z = -1) → (u = v * w * z ↔ v = u * w * z) := by
    intro u v w z hu hv hw hz
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;>
      rcases hz with rfl | rfl <;> decide
  constructor
  · rintro ⟨-, -, C3⟩ ⟨t, ht, rfl⟩
    have hsq : IsSquare (-(a₀ * a₁) * -(-a₂ * (t ^ 2 * -(a₀ * a₁ * a₂)))) :=
      ⟨t * (a₀ * a₁ * a₂), by ring⟩
    have e := C3 hsq
    rw [hs_sq_right _ _ _ ht, key] at e
    exact (pm _ _ _ _ (hs_pm _ _) (hs_pm _ _) (hs_pm _ _) (hs_pm _ _)).mp e
  · intro H
    refine ⟨C1, C2, fun ⟨r, hr⟩ => ?_⟩
    have hr0 : r ≠ 0 := by
      rintro rfl; simp at hr; rcases hr with h | h <;> simp_all
    have hxe : x = (r / (a₀ * a₁ * a₂)) ^ 2 * (-(a₀ * a₁ * a₂)) := by
      have hd' : a₀ * a₁ * a₂ ≠ 0 := by simp [h₀, h₁, h₂]
      rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hd')]
      linear_combination (-(a₀ * a₁ * a₂)) * hr
    have ht : r / (a₀ * a₁ * a₂) ≠ 0 := div_ne_zero hr0 (by simp [h₀, h₁, h₂])
    have e := H ⟨_, ht, hxe⟩
    rw [hxe, hs_sq_right _ _ _ ht, key]
    exact (pm _ _ _ _ (hs_pm _ _) (hs_pm _ _) (hs_pm _ _) (hs_pm _ _)).mpr e

/-- **Thm. 6, rank $\ge 4$**: a nondegenerate diagonal form of rank $\ge 4$ represents every
element. -/
@[kb "omeara1963" "§63C, 63:18, p. 170 (regular quaternary spaces are universal)"]
theorem represents_of_four_le {a : Fin n → K} (ha : ∀ i, a i ≠ 0) (hn : 4 ≤ n) (x : K) :
    (diag a).RepresentsIn K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp [QuadForm.evalIn]⟩
  rw [representsIn_diag_iff_isotropic ha]
  refine FieldGen.isotropicIn_diag_of_prefix K 5 (by omega) _ ?_
  refine hK.isotropic_five _ fun i => ?_
  simp only [Fin.append, Fin.addCases]
  split_ifs with h
  · exact ha _
  · simp [hx]

end Rank34

section Invariants

variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}

/-- The Hasse invariant $\prod_{0 \le i < j < n} (a_i, a_j)_K$ of a diagonal form with
coefficients $a_i \in K$ (`hasseInvariant` is the case $a_i \in \mathbb{Q}$). -/
noncomputable def hasseVec (a : Fin n → K) : ℤ :=
  ∏ i, ∏ j, if i < j then hilbertSymbol K (a i) (a j) else 1

theorem hasseVec_cons_prod (x : K) (v : Fin n → K) :
    hasseVec (Fin.cons x v : Fin (n + 1) → K) = (∏ j, hilbertSymbol K x (v j)) * hasseVec v := by
  unfold hasseVec
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]; simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff, (Fin.succ_pos i).not_gt]

theorem hasseVec_pm (a : Fin n → K) : hasseVec a = 1 ∨ hasseVec a = -1 := by
  unfold hasseVec
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun i _ => ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun j _ => ?_
  · rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  split_ifs
  · exact hs_pm _ _
  · exact Or.inl rfl

theorem hasseVec_two (a₀ a₁ : K) : hasseVec ![a₀, a₁] = hilbertSymbol K a₀ a₁ := by
  simp [hasseVec, Fin.prod_univ_two]

theorem hasseVec_three (a₀ a₁ a₂ : K) :
    hasseVec ![a₀, a₁, a₂] =
      hilbertSymbol K a₀ a₁ * hilbertSymbol K a₀ a₂ * hilbertSymbol K a₁ a₂ := by
  simp [hasseVec, Fin.prod_univ_three]

theorem eq_vec_two (a : Fin 2 → K) : a = ![a 0, a 1] := by
  funext i; fin_cases i <;> rfl

theorem eq_vec_three (a : Fin 3 → K) : a = ![a 0, a 1, a 2] := by
  funext i; fin_cases i <;> rfl

/-- **Isometric forms have Gram matrices related by $P^{\mathsf T} H P = H'$.** -/
theorem transpose_mul_hessian_mul {Q Q' : QuadForm K n} {P : Matrix (Fin n) (Fin n) K}
    (hP : ∀ x, Q.evalIn K (P *ᵥ x) = Q'.evalIn K x) :
    P.transpose * Q.hessian * P = Q'.hessian := by
  have hpol : ∀ x y : Fin n → K,
      (P *ᵥ x) ⬝ᵥ (Q.hessian *ᵥ (P *ᵥ y)) = x ⬝ᵥ (Q'.hessian *ᵥ y) := by
    intro x y
    have h1 := polar_eq_hessian K Q (P *ᵥ x) (P *ᵥ y)
    have h2 := polar_eq_hessian K Q' x y
    rw [← Matrix.mulVec_add, hP, hP, hP] at h1
    have e : ∀ M : Matrix (Fin n) (Fin n) K, M.map (algebraMap K K) = M := fun M => by
      ext; simp
    rw [e] at h1 h2
    rw [← h1, ← h2]
  ext i j
  have := hpol (Pi.single i 1) (Pi.single j 1)
  have e2 : Pi.single i 1 ⬝ᵥ Q'.hessian *ᵥ Pi.single j 1 = Q'.hessian i j := by
    simp
  rw [e2] at this
  rw [← this]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp [Pi.single_apply]; ring

/-- **The discriminant is an isometry invariant:** if $\langle a \rangle \cong \langle b \rangle$ over
$K$ then $\prod_i b_i = t^2 \prod_i a_i$ for some $t \ne 0$. -/
theorem disc_of_isometric {a b : Fin n → K} (h : (diag a).IsometricIn K (diag b)) :
    ∃ t : K, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i := by
  obtain ⟨P, hPu, hP⟩ := h
  have e := congrArg Matrix.det (transpose_mul_hessian_mul hP)
  simp only [Matrix.det_mul, Matrix.det_transpose, hessian, QuadForm.diag,
    Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal] at e
  refine ⟨P.det, hPu.ne_zero, ?_⟩
  have h2 : (∏ i, (b i + b i)) = 2 ^ n * ∏ i, b i := by
    simp [← two_mul, Finset.prod_mul_distrib]
  have h2' : (∏ i, (a i + a i)) = 2 ^ n * ∏ i, a i := by
    simp [← two_mul, Finset.prod_mul_distrib]
  rw [h2, h2'] at e
  have h20 : (2 : K) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h20
  rw [← e]; ring

/-- Permuting the coefficients of a diagonal form gives an isometric form. -/
theorem isometric_diag_comp_perm (a : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    (diag a).IsometricIn K (diag (a ∘ σ)) := by
  refine ⟨Equiv.Perm.permMatrix K σ.symm, ?_, fun x => ?_⟩
  · rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
  · rw [Matrix.permMatrix_mulVec, evalIn_diag_self, evalIn_diag_self]
    rw [← Equiv.sum_comp σ]
    simp

theorem isometric_diag_swap (x y : K) (v : Fin n → K) :
    (diag (Fin.cons x (Fin.cons y v) : Fin (n + 2) → K)).IsometricIn K
      (diag (Fin.cons y (Fin.cons x v) : Fin (n + 2) → K)) := by
  convert isometric_diag_comp_perm (Fin.cons x (Fin.cons y v) : Fin (n + 2) → K)
    (Equiv.swap 0 1) using 2
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
  · simp
  · simp
  · simp only [Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
    simp

variable (hK : LocalHilbertField K)
include hK

theorem hs_prod_right {x : K} (hx : x ≠ 0) {v : Fin n → K} (hv : ∀ i, v i ≠ 0) :
    ∏ j, hilbertSymbol K x (v j) = hilbertSymbol K x (∏ j, v j) := by
  induction n with
  | zero => simp [hilbertSymbol_one_right]
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, ih (fun i => hv i.succ),
      hK.mul_right hx (hv 0) (Finset.prod_ne_zero_iff.mpr fun i _ => hv i.succ)]

@[kb "omeara1963" "§63B, p. 167 (S(U ⊥ W) = S(U) (dU, dW) S(W), U a line); cassels1978 Ch. 4, Lemma 2.3, p. 58 (one summand a line)"]
theorem hasseVec_cons {x : K} (hx : x ≠ 0) {v : Fin n → K} (hv : ∀ i, v i ≠ 0) :
    hasseVec (Fin.cons x v : Fin (n + 1) → K) = hilbertSymbol K x (∏ j, v j) * hasseVec v := by
  rw [hasseVec_cons_prod, hs_prod_right hK hx hv]

theorem hasseVec_swap {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) {v : Fin n → K} (hv : ∀ i, v i ≠ 0) :
    hasseVec (Fin.cons x (Fin.cons y v) : Fin (n + 2) → K) =
      hasseVec (Fin.cons y (Fin.cons x v) : Fin (n + 2) → K) := by
  have hyv : ∀ i, (Fin.cons y v : Fin (n + 1) → K) i ≠ 0 := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [hy, hv]
  have hxv : ∀ i, (Fin.cons x v : Fin (n + 1) → K) i ≠ 0 := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [hx, hv]
  have hpv : ∏ j, v j ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hv i
  rw [hasseVec_cons hK hx hyv, hasseVec_cons hK hy hv, hasseVec_cons hK hy hxv,
    hasseVec_cons hK hx hv, Fin.prod_cons, Fin.prod_cons, hK.mul_right hx hy hpv,
    hK.mul_right hy hx hpv, hilbertSymbol_comm K x y]
  ring

end Invariants

section Classification

variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}

theorem represents_coeff (a : Fin n → K) (i : Fin n) : (diag a).RepresentsIn K (a i) := by
  rw [representsIn_diag_iff]
  refine ⟨Pi.single i 1, ?_⟩
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem cons_ne_zero {x : K} (hx : x ≠ 0) {v : Fin n → K} (hv : ∀ i, v i ≠ 0) :
    ∀ i, (Fin.cons x v : Fin (n + 1) → K) i ≠ 0 := fun i => by
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [hx, hv]

theorem pm_eq_of_iff {c u v : ℤ} (hc : c = 1 ∨ c = -1) (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1)
    (h : c = u ↔ c = v) : u = v := by
  rcases hc with rfl | rfl <;> rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

variable (hK : LocalHilbertField K)
include hK

@[kb "omeara1963" "§63C, 63:19, p. 170"]
theorem isotropic_of_five_le {v : Fin n → K} (hv : ∀ i, v i ≠ 0) (hn : 5 ≤ n) :
    (diag v).IsotropicIn K :=
  FieldGen.isotropicIn_diag_of_prefix K 5 hn v (hK.isotropic_five _ fun _ => hv _)

/-- Two nondegenerate diagonal forms of rank $\ge 3$ represent a common $c \ne 0$ (their orthogonal
difference has rank $\ge 6$, hence is isotropic). -/
@[kb "cassels1978" "Ch. 4, proof of Thm. 1.1, p. 61"]
theorem exists_common_value {a b : Fin n → K} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hn : 3 ≤ n) :
    ∃ c : K, c ≠ 0 ∧ (diag a).RepresentsIn K c ∧ (diag b).RepresentsIn K c := by
  have hab : ∀ i, (Fin.append a (fun j => -b j)) i ≠ 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact ha j
    · rw [Fin.append_right]; exact neg_ne_zero.mpr (hb j)
  obtain ⟨z, hz0, hz⟩ := (isotropicIn_diag_iff _).mp (isotropic_of_five_le hK hab (by omega))
  rw [Fin.sum_univ_add] at hz
  simp only [Fin.append_left, Fin.append_right] at hz
  set x : Fin n → K := fun i => z (Fin.castAdd n i) with hxdef
  set y : Fin n → K := fun j => z (Fin.natAdd n j) with hydef
  have hb' : ∑ j, b j * y j ^ 2 = ∑ i, a i * x i ^ 2 := by
    have e : ∑ j, -b j * y j ^ 2 = -∑ j, b j * y j ^ 2 := by
      rw [← Finset.sum_neg_distrib]; simp
    rw [e] at hz
    linear_combination -hz
  by_cases ht : ∑ i, a i * x i ^ 2 = 0
  · by_cases hx : x = 0
    · have hy : y ≠ 0 := by
        intro hy; apply hz0; funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · exact congrFun hx j
        · exact congrFun hy j
      have hiso : (diag b).IsotropicIn K :=
        (isotropicIn_diag_iff b).mpr ⟨y, hy, by rw [hb', ht]⟩
      exact ⟨a ⟨0, by omega⟩, ha _, represents_coeff a _, representsIn_of_isotropic hb hiso _⟩
    · have hiso : (diag a).IsotropicIn K := (isotropicIn_diag_iff a).mpr ⟨x, hx, ht⟩
      exact ⟨b ⟨0, by omega⟩, hb _, representsIn_of_isotropic ha hiso _, represents_coeff b _⟩
  · exact ⟨_, ht, (representsIn_diag_iff _ _).mpr ⟨x, rfl⟩, (representsIn_diag_iff _ _).mpr ⟨y, hb'⟩⟩

/-- **Invariance of the Hasse invariant** (Serre IV §2.1; Cassels Ch. 4, Lemma 2.2, p. 57, and Cor. 1, p. 58, there over $\mathbb{Q}_p$; Lam V.3 [unverified]):
isometric nondegenerate diagonal forms over $K$ have the same Hasse invariant.

*Proof.* Rank $\le 1$: both are $1$. Rank $2$ and $3$: Thm. 6 expresses the set of represented
values through $(d, \varepsilon)$ and the set is an isometry invariant. Rank $\ge 4$: write
$f = \langle a_0 \rangle \perp f'$, $g = \langle b_0 \rangle \perp g'$, pick $c$ represented by $f'$
and $g'$ (`exists_common_value`), split $f' \cong \langle c \rangle \perp \alpha$,
$g' \cong \langle c \rangle \perp \beta$, and cancel $\langle c \rangle$ in
$\langle c, a_0 \rangle \perp \alpha \cong \langle c, b_0 \rangle \perp \beta$; induct. -/
@[kb "omeara1963" "§63B, p. 167 (independent of the splitting)"]
theorem hasseVec_eq_of_isometric : ∀ (n : ℕ) (a b : Fin n → K), (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) →
    (diag a).IsometricIn K (diag b) → hasseVec a = hasseVec b
  | 0, a, b, _, _, _ => by simp [hasseVec]
  | 1, a, b, _, _, _ => by simp [hasseVec]
  | 2, a, b, ha, hb, h => by
    rw [eq_vec_two a, eq_vec_two b] at h ⊢
    rw [hasseVec_two, hasseVec_two]
    obtain ⟨t, ht, hd⟩ := disc_of_isometric h
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hd
    have r' : (diag ![a 0, a 1]).RepresentsIn K (a 0) := represents_coeff _ 0
    have r := representsIn_of_isometricIn K (isometricIn_symm K h) r'
    rw [represents_two_iff hK (hb 0) (hb 1) (ha 0)] at r
    rw [represents_two_iff hK (ha 0) (ha 1) (ha 0)] at r'
    rw [← r, ← r', hd, show -(t ^ 2 * (a 0 * a 1)) = t ^ 2 * -(a 0 * a 1) by ring,
      hs_sq_right _ _ _ ht]
  | 3, a, b, ha, hb, h => by
    rw [eq_vec_three a, eq_vec_three b] at h ⊢
    rw [hasseVec_three, hasseVec_three]
    obtain ⟨t, ht, hd⟩ := disc_of_isometric h
    replace hd : b 0 * b 1 * b 2 = t ^ 2 * (a 0 * a 1 * a 2) := by
      simpa [Fin.prod_univ_three] using hd
    have hx : -(a 0 * a 1 * a 2) ≠ 0 := by simp [ha 0, ha 1, ha 2]
    have key : (diag ![a 0, a 1, a 2]).RepresentsIn K (-(a 0 * a 1 * a 2)) ↔
        (diag ![b 0, b 1, b 2]).RepresentsIn K (-(a 0 * a 1 * a 2)) :=
      ⟨fun r => representsIn_of_isometricIn K (isometricIn_symm K h) r,
        fun r => representsIn_of_isometricIn K h r⟩
    rw [represents_three_iff hK (ha 0) (ha 1) (ha 2) hx,
      represents_three_iff hK (hb 0) (hb 1) (hb 2) hx] at key
    have c1 : ∃ s : K, s ≠ 0 ∧ -(a 0 * a 1 * a 2) = s ^ 2 * -(a 0 * a 1 * a 2) :=
      ⟨1, one_ne_zero, by ring⟩
    have c2 : ∃ s : K, s ≠ 0 ∧ -(a 0 * a 1 * a 2) = s ^ 2 * -(b 0 * b 1 * b 2) :=
      ⟨t⁻¹, inv_ne_zero ht, by rw [hd]; field_simp⟩
    have e : hilbertSymbol K (-1) (-(b 0 * b 1 * b 2)) =
        hilbertSymbol K (-1) (-(a 0 * a 1 * a 2)) := by
      rw [hd, show -(t ^ 2 * (a 0 * a 1 * a 2)) = t ^ 2 * -(a 0 * a 1 * a 2) by ring,
        hs_sq_right _ _ _ ht]
    rw [e] at key
    refine pm_eq_of_iff (hs_pm _ _) ?_ ?_ ⟨fun h1 => (key.mp fun _ => h1) c2,
      fun h1 => (key.mpr fun _ => h1) c1⟩
    · have := hasseVec_pm ![a 0, a 1, a 2]; rwa [hasseVec_three] at this
    · have := hasseVec_pm ![b 0, b 1, b 2]; rwa [hasseVec_three] at this
  | m + 4, a, b, ha, hb, h => by
    set a' : Fin (m + 3) → K := Fin.tail a with ha'def
    set b' : Fin (m + 3) → K := Fin.tail b with hb'def
    have ha' : ∀ i, a' i ≠ 0 := fun i => ha i.succ
    have hb' : ∀ i, b' i ≠ 0 := fun i => hb i.succ
    have hac : a = Fin.cons (a 0) a' := (Fin.cons_self_tail a).symm
    have hbc : b = Fin.cons (b 0) b' := (Fin.cons_self_tail b).symm
    obtain ⟨c, hc, rca, rcb⟩ := exists_common_value hK ha' hb' (by omega)
    obtain ⟨α, hα, haα⟩ := exists_isometric_diag_cons (nondegenerate_diag ha') hc rca
    obtain ⟨β, hβ, hbβ⟩ := exists_isometric_diag_cons (nondegenerate_diag hb') hc rcb
    have hcα := cons_ne_zero hc hα
    have hcβ := cons_ne_zero hc hβ
    have ha0α := cons_ne_zero (ha 0) hα
    have hb0β := cons_ne_zero (hb 0) hβ
    have IHa := hasseVec_eq_of_isometric (m + 3) a' _ ha' hcα haα
    have IHb := hasseVec_eq_of_isometric (m + 3) b' _ hb' hcβ hbβ
    obtain ⟨s, hs, hds⟩ := disc_of_isometric haα
    obtain ⟨s', hs', hds'⟩ := disc_of_isometric hbβ
    have e1 : (diag (Fin.cons c (Fin.cons (a 0) α) : Fin (m + 4) → K)).IsometricIn K (diag a) := by
      refine isometricIn_trans K (isometric_diag_swap c (a 0) α) ?_
      rw [hac]
      exact isometricIn_diag_cons_of K (a 0) (isometricIn_symm K haα)
    have e2 : (diag b).IsometricIn K (diag (Fin.cons c (Fin.cons (b 0) β) : Fin (m + 4) → K)) := by
      refine isometricIn_trans K ?_ (isometric_diag_swap (b 0) c β)
      rw [hbc]
      exact isometricIn_diag_cons_of K (b 0) hbβ
    have h2 := isometricIn_of_diag_cons K hc ha0α
      (isometricIn_trans K e1 (isometricIn_trans K h e2))
    have IH2 := hasseVec_eq_of_isometric (m + 3) _ _ ha0α hb0β h2
    obtain ⟨u, hu, hdu⟩ := disc_of_isometric h2
    calc hasseVec a = hasseVec (Fin.cons (a 0) a' : Fin (m + 3 + 1) → K) := by rw [← hac]
      _ = hilbertSymbol K (a 0) (∏ i, a' i) * hasseVec a' := hasseVec_cons hK (ha 0) ha'
      _ = hilbertSymbol K (a 0) (∏ i, (Fin.cons c α : Fin (m + 3) → K) i) *
            hasseVec (Fin.cons c α : Fin (m + 3) → K) := by rw [IHa, hds, hs_sq_right _ _ _ hs]
      _ = hasseVec (Fin.cons (a 0) (Fin.cons c α) : Fin (m + 2 + 2) → K) :=
            (hasseVec_cons hK (ha 0) hcα).symm
      _ = hasseVec (Fin.cons c (Fin.cons (a 0) α) : Fin (m + 2 + 2) → K) :=
            hasseVec_swap hK (ha 0) hc hα
      _ = hilbertSymbol K c (∏ i, (Fin.cons (a 0) α : Fin (m + 3) → K) i) *
            hasseVec (Fin.cons (a 0) α : Fin (m + 3) → K) := hasseVec_cons hK hc ha0α
      _ = hilbertSymbol K c (∏ i, (Fin.cons (b 0) β : Fin (m + 3) → K) i) *
            hasseVec (Fin.cons (b 0) β : Fin (m + 3) → K) := by
            rw [IH2, hdu, hs_sq_right _ _ _ hu]
      _ = hasseVec (Fin.cons c (Fin.cons (b 0) β) : Fin (m + 2 + 2) → K) :=
            (hasseVec_cons hK hc hb0β).symm
      _ = hasseVec (Fin.cons (b 0) (Fin.cons c β) : Fin (m + 2 + 2) → K) :=
            hasseVec_swap hK hc (hb 0) hβ
      _ = hilbertSymbol K (b 0) (∏ i, (Fin.cons c β : Fin (m + 3) → K) i) *
            hasseVec (Fin.cons c β : Fin (m + 3) → K) := hasseVec_cons hK (hb 0) hcβ
      _ = hilbertSymbol K (b 0) (∏ i, b' i) * hasseVec b' := by
            rw [IHb, hds', hs_sq_right _ _ _ hs']
      _ = hasseVec b := by rw [hbc]; exact (hasseVec_cons hK (hb 0) hb').symm

/-- **The represented values depend only on $(n, d, \varepsilon)$** (Serre IV §2.2, Thm. 6, for
$n \ge 2$): if two nondegenerate diagonal forms of the same rank $n \ge 2$ have discriminants in the
same square class and equal Hasse invariants, they represent the same nonzero elements. -/
@[kb "omeara1963" "§63C, 63:21, p. 170 (U a line)"]
theorem represents_of_invariants {a b : Fin n → K} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hn : 2 ≤ n) (hd : ∃ t : K, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i)
    (hε : hasseVec a = hasseVec b) {x : K} (hx : x ≠ 0) (hr : (diag a).RepresentsIn K x) :
    (diag b).RepresentsIn K x := by
  obtain ⟨t, ht, hd⟩ := hd
  obtain rfl | rfl | h4 : n = 2 ∨ n = 3 ∨ 4 ≤ n := by omega
  · rw [eq_vec_two a] at hr hε
    rw [eq_vec_two b] at hε ⊢
    rw [hasseVec_two, hasseVec_two] at hε
    replace hd : b 0 * b 1 = t ^ 2 * (a 0 * a 1) := by simpa [Fin.prod_univ_two] using hd
    rw [represents_two_iff hK (ha 0) (ha 1) hx] at hr
    rw [represents_two_iff hK (hb 0) (hb 1) hx, ← hε, ← hr, hd,
      show -(t ^ 2 * (a 0 * a 1)) = t ^ 2 * -(a 0 * a 1) by ring, hs_sq_right _ _ _ ht]
  · rw [eq_vec_three a] at hr hε
    rw [eq_vec_three b] at hε ⊢
    rw [hasseVec_three, hasseVec_three] at hε
    replace hd : b 0 * b 1 * b 2 = t ^ 2 * (a 0 * a 1 * a 2) := by
      simpa [Fin.prod_univ_three] using hd
    rw [represents_three_iff hK (ha 0) (ha 1) (ha 2) hx] at hr
    rw [represents_three_iff hK (hb 0) (hb 1) (hb 2) hx, ← hε, hd,
      show -(t ^ 2 * (a 0 * a 1 * a 2)) = t ^ 2 * -(a 0 * a 1 * a 2) by ring,
      hs_sq_right _ _ _ ht]
    rintro ⟨s, hs, hxs⟩
    exact hr ⟨s * t, mul_ne_zero hs ht, by rw [hxs]; ring⟩
  · exact represents_of_four_le hK hb h4 x

/-- **Classification, the converse direction** (Serre IV §2.3, Thm. 7): nondegenerate diagonal
forms of the same rank with discriminants in the same square class and equal Hasse invariants are
isometric over $K$.

*Proof.* Induction on $n$. For $n \ge 2$, $g$ represents $a_0$ (`represents_of_invariants`), so
$g \cong \langle a_0 \rangle \perp \beta$; the invariants of $\langle a_1, \dots, a_{n-1} \rangle$
and $\beta$ agree (using `hasseVec_eq_of_isometric`), and induction applies. -/
@[kb "omeara1963" "§63C, 63:20, p. 170; cassels1978 Ch. 4, proof of Thm. 1.1, p. 61"]
theorem isometric_of_invariants : ∀ (n : ℕ) (a b : Fin n → K), (∀ i, a i ≠ 0) →
    (∀ i, b i ≠ 0) → (∃ t : K, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i) →
    hasseVec a = hasseVec b → (diag a).IsometricIn K (diag b)
  | 0, a, b, _, _, _, _ => by rw [Subsingleton.elim a b]; exact isometricIn_refl K _
  | 1, a, b, _, _, ⟨t, ht, hd⟩, _ => by
    refine ⟨t • 1, ?_, fun x => ?_⟩
    · simp [ht]
    · rw [Matrix.smul_mulVec, Matrix.one_mulVec, evalIn_smul, evalIn_diag_self, evalIn_diag_self]
      simp only [Fin.prod_univ_one] at hd
      simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, hd]
      ring
  | m + 2, a, b, ha, hb, hd, hε => by
    obtain ⟨t, ht, hdt⟩ := hd
    have rb := represents_of_invariants hK ha hb (by omega) ⟨t, ht, hdt⟩ hε (ha 0)
      (represents_coeff a 0)
    obtain ⟨β, hβ, hbβ⟩ := exists_isometric_diag_cons (nondegenerate_diag hb) (ha 0) rb
    set a' : Fin (m + 1) → K := Fin.tail a with ha'def
    have ha' : ∀ i, a' i ≠ 0 := fun i => ha i.succ
    have hac : a = Fin.cons (a 0) a' := (Fin.cons_self_tail a).symm
    have ha0β := cons_ne_zero (ha 0) hβ
    have hεb := hasseVec_eq_of_isometric hK _ _ _ hb ha0β hbβ
    obtain ⟨s, hs, hds⟩ := disc_of_isometric hbβ
    have hpa : ∏ i, a i = a 0 * ∏ i, a' i := by rw [hac]; exact Fin.prod_cons _ _
    have hprod : ∏ i, β i = (s * t) ^ 2 * ∏ i, a' i := by
      rw [Fin.prod_cons, hdt, hpa] at hds
      apply mul_left_cancel₀ (ha 0)
      rw [hds]; ring
    have hpa0 : ∏ i, a' i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha' i
    have hεa' : hasseVec a' = hasseVec β := by
      have e1 : hasseVec a = hilbertSymbol K (a 0) (∏ i, a' i) * hasseVec a' := by
        rw [show hasseVec a = hasseVec (Fin.cons (a 0) a' : Fin (m + 1 + 1) → K) from
          congrArg hasseVec hac]
        exact hasseVec_cons hK (ha 0) ha'
      have e := hε.trans hεb
      rw [e1, hasseVec_cons hK (ha 0) hβ, hprod,
        hs_sq_right _ _ _ (mul_ne_zero hs ht)] at e
      refine mul_left_cancel₀ ?_ e
      rcases hs_pm (a 0) (∏ i, a' i) with h | h <;> rw [h] <;> norm_num
    have IH := isometric_of_invariants (m + 1) a' β ha' hβ ⟨s * t, mul_ne_zero hs ht, hprod⟩ hεa'
    have e0 : (diag a).IsometricIn K (diag (Fin.cons (a 0) a' : Fin (m + 2) → K)) := by
      rw [← hac]; exact isometricIn_refl K _
    exact isometricIn_trans K e0
      (isometricIn_trans K (isometricIn_diag_cons_of K (a 0) IH) (isometricIn_symm K hbβ))

/-- **Classification of nondegenerate diagonal forms over $K$** (Serre IV §2.3, Thm. 7, over an
abstract field satisfying `LocalHilbertField`). -/
@[kb "omeara1963" "§63C, 63:20, p. 170; cassels1978 Ch. 4, Thm. 1.1, p. 55"]
theorem isometric_iff_invariants {a b : Fin n → K} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (diag a).IsometricIn K (diag b) ↔
      (∃ t : K, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i) ∧ hasseVec a = hasseVec b :=
  ⟨fun h => ⟨disc_of_isometric h, hasseVec_eq_of_isometric hK n a b ha hb h⟩,
    fun ⟨hd, hε⟩ => isometric_of_invariants hK n a b ha hb hd hε⟩

end Classification

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

/-- Every $a \in \mathbb{Q}_p^\times$ is $c^2 p^r u$ with $c \ne 0$, $r \in \{0, 1\}$ and
$u \in \mathbb{Z}_p^\times$. -/
theorem padic_decomp (a : ℚ_[p]) (ha : a ≠ 0) :
    ∃ (c : ℚ_[p]) (r : ℕ) (u : ℤ_[p]ˣ), c ≠ 0 ∧ r < 2 ∧
      a = c ^ 2 * ((p : ℚ_[p]) ^ r * ((u : ℤ_[p]) : ℚ_[p])) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpos : (0 : ℝ) < p := by linarith
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set k := a.valuation
  have hyn : ‖a * (p : ℚ_[p]) ^ (-k)‖ = 1 := by
    rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation ha,
      ← zpow_add₀ hpos.ne']
    simp [k]
  refine ⟨(p : ℚ_[p]) ^ (k / 2), (k % 2).toNat, PadicInt.mkUnits hyn, zpow_ne_zero _ hpne,
    by omega, ?_⟩
  rw [PadicInt.mkUnits_eq]
  have h0 : (0 : ℤ) ≤ k % 2 := Int.emod_nonneg _ (by norm_num)
  have e1 : ((p : ℚ_[p]) ^ (k % 2).toNat) = (p : ℚ_[p]) ^ (k % 2) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg h0]
  rw [e1, ← zpow_natCast, ← _root_.zpow_mul]
  have e2 : (p : ℚ_[p]) ^ (k / 2 * ((2 : ℕ) : ℤ)) * ((p : ℚ_[p]) ^ (k % 2) * (a * (p : ℚ_[p]) ^ (-k)))
      = a * ((p : ℚ_[p]) ^ (k / 2 * ((2 : ℕ) : ℤ)) * (p : ℚ_[p]) ^ (k % 2) * (p : ℚ_[p]) ^ (-k)) := by
    ring
  rw [e2, ← zpow_add₀ hpne, ← zpow_add₀ hpne]
  have e3 : k / 2 * ((2 : ℕ) : ℤ) + k % 2 + -k = 0 := by
    push_cast; omega
  rw [e3, zpow_zero, mul_one]

/-- A $p$-adic unit with nonzero residue: the lift of a nonzero residue class. -/
theorem exists_unit_toZMod (r : ZMod p) (hr : r ≠ 0) :
    ∃ v : ℤ_[p]ˣ, PadicInt.toZMod (v : ℤ_[p]) = r := by
  set w : ℤ_[p] := (r.val : ℤ_[p])
  have hw : PadicInt.toZMod w = r := by simp [w]
  have hu : IsUnit w := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, hw]
    exact hr
  exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hw⟩

/-- **Nondegeneracy of the Hilbert symbol over $\mathbb{Q}_p$** (Serre III §1.2, Thm. 2, from the
explicit formulas): if $a \in \mathbb{Q}_p^\times$ is not a square, then $(a, x)_p = -1$ for some
$x \in \mathbb{Q}_p^\times$. -/
@[kb "omeara1963" "§63B, 63:13, p. 166"]
theorem padic_exists_neg_one (a : ℚ_[p]) (ha : a ≠ 0) (hns : ¬ IsSquare a) :
    ∃ x : ℚ_[p], x ≠ 0 ∧ hilbertSymbol ℚ_[p] a x = -1 := by
  obtain ⟨c, r, u, hc, hr, rfl⟩ := padic_decomp p a ha
  have hns' : ¬ IsSquare ((p : ℚ_[p]) ^ r * ((u : ℤ_[p]) : ℚ_[p])) := by
    rintro ⟨w, hw⟩; exact hns ⟨c * w, by rw [hw]; ring⟩
  have hred : ∀ x, hilbertSymbol ℚ_[p] (c ^ 2 * ((p : ℚ_[p]) ^ r * ((u : ℤ_[p]) : ℚ_[p]))) x =
      hilbertSymbol ℚ_[p] ((p : ℚ_[p]) ^ r * ((u : ℤ_[p]) : ℚ_[p])) x :=
    fun x => hs_sq_left _ _ _ hc
  simp_rw [hred]
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hunit : ∀ v : ℤ_[p]ˣ, ((v : ℤ_[p]) : ℚ_[p]) ≠ 0 := fun v h =>
    v.ne_zero (by simp at h)
  have hzr : ((p : ℚ_[p]) ^ r * ((u : ℤ_[p]) : ℚ_[p])) = (p : ℚ_[p]) ^ (r : ℤ) * ((u : ℤ_[p]) : ℚ_[p]) := by
    rw [zpow_natCast]
  by_cases hp2 : p ≠ 2
  · rw [hzr, HilbertLocal.isSquare_zpow_mul_unit_iff hp2] at hns'
    obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
    · -- `u` has a nonsquare residue; take `x = p`
      have hu : ¬ IsSquare (PadicInt.toZMod (u : ℤ_[p])) := fun h => hns' ⟨by simp, h⟩
      refine ⟨(p : ℚ_[p]) ^ 1 * (((1 : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]), by simp [hpne], ?_⟩
      rw [HilbertLocal.hilbertSymbol_odd_formula hp2 0 1 u 1]
      simp only [HilbertLocal.unitChar]
      rw [quadraticChar_neg_one_iff_not_isSquare.mpr hu]
      simp
    · -- take `x = v`, a unit with nonsquare residue
      have hch : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
      obtain ⟨r0, hr0⟩ := FiniteField.exists_nonsquare hch
      have hr00 : r0 ≠ 0 := by rintro rfl; exact hr0 ⟨0, by simp⟩
      obtain ⟨v, hv⟩ := exists_unit_toZMod p r0 hr00
      refine ⟨(p : ℚ_[p]) ^ 0 * ((v : ℤ_[p]) : ℚ_[p]), by simp [hunit v], ?_⟩
      rw [HilbertLocal.hilbertSymbol_odd_formula hp2 1 0 u v]
      simp only [HilbertLocal.unitChar, hv]
      rw [quadraticChar_neg_one_iff_not_isSquare.mpr hr0]
      simp
  · push Not at hp2
    subst hp2
    have h2 : ((2 : ℕ) : ℚ_[2]) = 2 := by norm_num
    rw [hzr, h2, HilbertLocal.isSquare_two_zpow_mul_unit_iff] at hns'
    simp only [h2]
    have hunit3 : IsUnit ((3 : ℕ) : ℤ_[2]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]; norm_num
    have hunit5 : IsUnit ((5 : ℕ) : ℤ_[2]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]; norm_num
    have h3 : PadicInt.toZModPow 3 ((hunit3.unit : ℤ_[2]ˣ) : ℤ_[2]) = 3 := by
      rw [IsUnit.unit_spec, map_natCast]; rfl
    have h5 : PadicInt.toZModPow 3 ((hunit5.unit : ℤ_[2]ˣ) : ℤ_[2]) = 5 := by
      rw [IsUnit.unit_spec, map_natCast]; rfl
    obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
    · have hu1 : PadicInt.toZModPow 3 (u : ℤ_[2]) ≠ 1 := fun h => hns' ⟨by simp, h⟩
      have hres : ∃ w' : ZMod (2 ^ 3), PadicInt.toZModPow 3 (u : ℤ_[2]) * w' = 1 :=
        ⟨PadicInt.toZModPow 3 ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), by rw [← map_mul, Units.mul_inv, map_one]⟩
      have h4 : ∀ r : ZMod (2 ^ 3), (∃ r', r * r' = 1) → r ≠ 1 → r = 3 ∨ r = 5 ∨ r = 7 := by
        decide
      rcases h4 _ hres hu1 with h | h | h
      · refine ⟨(2 : ℚ_[2]) ^ 1 * (((1 : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]), by simp, ?_⟩
        rw [HilbertLocal.hilbertSymbol_two_formula 0 1 u 1, h]
        simp only [Units.val_one, map_one]
        decide
      · refine ⟨(2 : ℚ_[2]) ^ 1 * (((1 : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]), by simp, ?_⟩
        rw [HilbertLocal.hilbertSymbol_two_formula 0 1 u 1, h]
        simp only [Units.val_one, map_one]
        decide
      · refine ⟨(2 : ℚ_[2]) ^ 0 * (((hunit3.unit : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]),
          by simp, ?_⟩
        rw [HilbertLocal.hilbertSymbol_two_formula 0 0 u hunit3.unit, h, h3]
        decide
    · refine ⟨(2 : ℚ_[2]) ^ 0 * (((hunit5.unit : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]),
        by simp, ?_⟩
      rw [HilbertLocal.hilbertSymbol_two_formula 1 0 u hunit5.unit, h5]
      have hε : HilbertLocal.twoEps 5 = 0 := by decide
      have hω : HilbertLocal.twoOmega 5 = 1 := by decide
      rw [hε, hω]; simp

/-- Every nondegenerate diagonal form of rank $5$ over $\mathbb{Q}_p$ is isotropic (reduced to
rational coefficients by `Prescribed.exists_rat_sq_class`, then `RankFive`). -/
@[kb "omeara1963" "§63C, 63:19, p. 170"]
theorem padic_isotropic_five (a : Fin 5 → ℚ_[p]) (ha : ∀ i, a i ≠ 0) :
    (diag a).IsotropicIn ℚ_[p] := by
  choose q hq0 hsq using fun i => Prescribed.exists_rat_sq_class p (a i) (ha i)
  choose s hs using hsq
  have hrat : (QuadForm.diag q).IsotropicIn ℚ_[p] := by
    by_cases hp2 : p = 2
    · subst hp2; exact RankFive.isotropic_two_adic_diag q hq0 le_rfl
    · exact RankFive.isotropic_padic_diag_odd p hp2 q hq0 le_rfl
  obtain ⟨x, hx0, hx⟩ := hrat
  rw [evalIn_diag] at hx
  have hq0' : ∀ i, (q i : ℚ_[p]) ≠ 0 := fun i => by exact_mod_cast hq0 i
  have hs0 : ∀ i, s i ≠ 0 := fun i h => by
    have := hs i; rw [h, mul_zero, div_eq_zero_iff] at this
    rcases this with h' | h'
    · exact ha i h'
    · exact hq0' i h'
  have has : ∀ i, a i = s i ^ 2 * (q i : ℚ_[p]) := fun i => by
    have := hs i; rw [div_eq_iff (hq0' i)] at this; rw [this]; ring
  refine (isotropicIn_diag_iff a).mpr ⟨fun i => x i / s i, fun h => hx0 ?_, ?_⟩
  · funext i; have := congrFun h i; simpa [hs0 i] using this
  · rw [← hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [has i]; simp only [eq_ratCast]; field_simp [hs0 i]

/-- $\mathbb{Q}_p$ satisfies the axioms `LocalHilbertField`. -/
theorem localHilbertField_padic : LocalHilbertField ℚ_[p] where
  mul_left a a' b ha ha' hb := HilbertLocal.hilbertSymbol_padic_mul_left a a' b ha ha' hb
  exists_neg_one := padic_exists_neg_one p
  isotropic_five := padic_isotropic_five p

end Padic

section Rat

variable (p : ℕ) [Fact p.Prime] {n : ℕ}

theorem isometricIn_rat_iff (a b : Fin n → ℚ) :
    (diag a).IsometricIn ℚ_[p] (diag b) ↔
      (diag fun i => algebraMap ℚ ℚ_[p] (a i)).IsometricIn ℚ_[p]
        (diag fun i => algebraMap ℚ ℚ_[p] (b i)) := by
  simp only [IsometricIn, evalIn_diag, Algebra.algebraMap_self, RingHom.id_apply]

theorem representsIn_rat_iff (a : Fin n → ℚ) (x : ℚ) :
    (diag a).RepresentsIn ℚ_[p] x ↔
      (diag fun i => algebraMap ℚ ℚ_[p] (a i)).RepresentsIn ℚ_[p] (algebraMap ℚ ℚ_[p] x) := by
  simp only [RepresentsIn, evalIn_diag, Algebra.algebraMap_self, RingHom.id_apply]

theorem hasseInvariant_eq_hasseVec (a : Fin n → ℚ) :
    hasseInvariant ℚ_[p] a = hasseVec fun i => algebraMap ℚ ℚ_[p] (a i) := rfl

theorem cast_ne_zero {a : Fin n → ℚ} (ha : ∀ i, a i ≠ 0) :
    ∀ i, (fun i => algebraMap ℚ ℚ_[p] (a i)) i ≠ 0 := fun i => by simpa using ha i

theorem prod_cast (a : Fin n → ℚ) :
    ∏ i, (fun i => algebraMap ℚ ℚ_[p] (a i)) i = algebraMap ℚ ℚ_[p] (∏ i, a i) := by
  simp

end Rat

end QuadFormsKB.PadicClass

namespace QuadFormsKB

open QuadForm PadicClass

variable {n : ℕ}

/-- **Isometry invariance of the Hasse invariant over $\mathbb{Q}_p$** (Serre, *A Course in
Arithmetic*, IV §2.1, "$\varepsilon$ is an invariant of $f$"; Cassels, *Rational Quadratic Forms*,
Ch. 4, Lemma 2.2, p. 57, and Cor. 1, p. 58; Lam V.3 [unverified]): if the nondegenerate diagonal forms
$\langle a_0, \dots, a_{n-1} \rangle$ and $\langle b_0, \dots, b_{n-1} \rangle$ ($a_i, b_i \in
\mathbb{Q}^\times$) are isometric over $\mathbb{Q}_p$, then
$$\prod_{0 \le i < j < n} (a_i, a_j)_p = \prod_{0 \le i < j < n} (b_i, b_j)_p.$$

*Proof* (`PadicClass.hasseVec_eq_of_isometric`, over any field satisfying `LocalHilbertField`).
Ranks $2$ and $3$ from the representation criterion (Thm. 6), whose set of represented values is
an isometry invariant; rank $\ge 4$ by induction, splitting off a value $c$ represented by both
$\langle a_1, \dots \rangle$ and $\langle b_1, \dots \rangle$ and using Witt cancellation. Serre
uses Witt's chain-equivalence theorem instead. -/
@[kb "serre1973" "Ch. IV, §2.1"]
theorem hasseInvariant_isometric (p : ℕ) [Fact p.Prime] (a b : Fin n → ℚ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : (QuadForm.diag a).IsometricIn ℚ_[p] (QuadForm.diag b)) :
    hasseInvariant ℚ_[p] a = hasseInvariant ℚ_[p] b := by
  rw [isometricIn_rat_iff] at h
  exact hasseVec_eq_of_isometric (localHilbertField_padic p) n _ _ (cast_ne_zero p ha)
    (cast_ne_zero p hb) h

/-- **Thm. 6 over $\mathbb{Q}_p$, rank 1** (Serre IV §2.2): for $a_0 \in \mathbb{Q}$ and
$x \in \mathbb{Q}^\times$,
$\langle a_0 \rangle$ represents $x$ over $\mathbb{Q}_p$ iff $x$ and $d = a_0$ lie in the same square
class of $\mathbb{Q}_p^\times$. -/
@[kb "serre1973" "Ch. IV, §2.2, Thm. 6"]
theorem represents_padic_one_iff (p : ℕ) [Fact p.Prime] (a : Fin 1 → ℚ) (x : ℚ) (hx : x ≠ 0) :
    (QuadForm.diag a).RepresentsIn ℚ_[p] x ↔ SameSquareClass ℚ_[p] x (∏ i, a i) := by
  rw [representsIn_rat_iff, representsIn_diag_iff]
  simp only [Fin.sum_univ_one, Fin.prod_univ_one, SameSquareClass]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y 0, fun h0 => ?_, by rw [← hy]; ring⟩
    rw [h0] at hy; simp at hy; exact hx (by exact_mod_cast hy.symm)
  · rintro ⟨t, -, ht⟩
    exact ⟨fun _ => t, by rw [ht]; ring⟩

/-- **Thm. 6 over $\mathbb{Q}_p$, rank 2** (Serre IV §2.2): for $a_0, a_1, x \in \mathbb{Q}^\times$,
with $d = a_0 a_1$ and $\varepsilon = (a_0, a_1)_p$ (`hasseInvariant`), the form
$\langle a_0, a_1 \rangle$ represents $x$ over $\mathbb{Q}_p$ iff $(x, -d)_p = \varepsilon$. -/
@[kb "serre1973" "Ch. IV, §2.2, Thm. 6"]
theorem represents_padic_two_iff (p : ℕ) [Fact p.Prime] (a : Fin 2 → ℚ) (ha : ∀ i, a i ≠ 0)
    (x : ℚ) (hx : x ≠ 0) :
    (QuadForm.diag a).RepresentsIn ℚ_[p] x ↔
      hilbertSymbol ℚ_[p] (algebraMap ℚ ℚ_[p] x) (algebraMap ℚ ℚ_[p] (-∏ i, a i)) =
        hasseInvariant ℚ_[p] a := by
  have ha' := cast_ne_zero p ha
  rw [representsIn_rat_iff, hasseInvariant_eq_hasseVec, eq_vec_two (fun i => algebraMap ℚ ℚ_[p] (a i)),
    represents_two_iff (localHilbertField_padic p) (ha' 0) (ha' 1) (by simpa using hx),
    hasseVec_two]
  simp [Fin.prod_univ_two]

/-- **Thm. 6 over $\mathbb{Q}_p$, rank 3** (Serre IV §2.2): for $a_0, a_1, a_2, x \in \mathbb{Q}^\times$,
with $d = a_0 a_1 a_2$ and $\varepsilon = \prod_{i<j} (a_i, a_j)_p$ (`hasseInvariant`), the form
$\langle a_0, a_1, a_2 \rangle$ represents $x$ over $\mathbb{Q}_p$ iff $x \not\equiv -d$ modulo
squares or $(-1, -d)_p = \varepsilon$. -/
@[kb "serre1973" "Ch. IV, §2.2, Thm. 6"]
theorem represents_padic_three_iff (p : ℕ) [Fact p.Prime] (a : Fin 3 → ℚ) (ha : ∀ i, a i ≠ 0)
    (x : ℚ) (hx : x ≠ 0) :
    (QuadForm.diag a).RepresentsIn ℚ_[p] x ↔
      (SameSquareClass ℚ_[p] x (-∏ i, a i) →
        hilbertSymbol ℚ_[p] (-1) (algebraMap ℚ ℚ_[p] (-∏ i, a i)) = hasseInvariant ℚ_[p] a) := by
  have ha' := cast_ne_zero p ha
  rw [representsIn_rat_iff, hasseInvariant_eq_hasseVec,
    eq_vec_three (fun i => algebraMap ℚ ℚ_[p] (a i)),
    represents_three_iff (localHilbertField_padic p) (ha' 0) (ha' 1) (ha' 2) (by simpa using hx),
    hasseVec_three]
  simp [Fin.prod_univ_three, SameSquareClass]

/-- **Thm. 6 over $\mathbb{Q}_p$, rank $\ge 4$** (Serre IV §2.2): a nondegenerate diagonal form of rank
$n \ge 4$ over $\mathbb{Q}$ represents every element of $\mathbb{Q}$ over $\mathbb{Q}_p$. -/
@[kb "serre1973" "Ch. IV, §2.2, Thm. 6; omeara1963 §63C, 63:18, p. 170 (regular quaternary spaces are universal)"]
theorem represents_padic_of_four_le (p : ℕ) [Fact p.Prime] (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hn : 4 ≤ n) (x : ℚ) : (QuadForm.diag a).RepresentsIn ℚ_[p] x := by
  rw [representsIn_rat_iff]
  exact represents_of_four_le (localHilbertField_padic p) (cast_ne_zero p ha) hn _

/-- **Classification of quadratic forms over $\mathbb{Q}_p$** (Serre IV §2.3, Thm. 7; Cassels Ch. 4,
Thm. 1.1, p. 55; Lam V.3 [unverified]): nondegenerate diagonal forms $\langle a_0, \dots, a_{n-1} \rangle$ and
$\langle b_0, \dots, b_{n-1} \rangle$ of the same rank, $a_i, b_i \in \mathbb{Q}^\times$, are
isometric over $\mathbb{Q}_p$ iff $\prod_i a_i$ and $\prod_i b_i$ lie in the same square class of
$\mathbb{Q}_p^\times$ and their Hasse invariants agree. (The same statement as
`isometric_padic_iff`, proved here.) -/
@[kb "serre1973" "Ch. IV, §2.3, Thm. 7; omeara1963 §63C, 63:20, p. 170; cassels1978 Ch. 4, Thm. 1.1, p. 55"]
theorem isometric_padic_iff_invariants (p : ℕ) [Fact p.Prime] (a b : Fin n → ℚ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (QuadForm.diag a).IsometricIn ℚ_[p] (QuadForm.diag b) ↔
      SameSquareClass ℚ_[p] (∏ i, a i) (∏ i, b i) ∧
        hasseInvariant ℚ_[p] a = hasseInvariant ℚ_[p] b := by
  rw [isometricIn_rat_iff, isometric_iff_invariants (localHilbertField_padic p) (cast_ne_zero p ha)
    (cast_ne_zero p hb), hasseInvariant_eq_hasseVec, hasseInvariant_eq_hasseVec, prod_cast,
    prod_cast]
  refine and_congr ⟨fun ⟨t, ht, h⟩ => ⟨t⁻¹, inv_ne_zero ht, ?_⟩,
    fun ⟨t, ht, h⟩ => ⟨t⁻¹, inv_ne_zero ht, ?_⟩⟩ Iff.rfl
  · rw [h]; field_simp
  · rw [h]; field_simp

end QuadFormsKB
