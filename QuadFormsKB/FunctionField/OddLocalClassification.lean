/-
# Local classification of quadratic forms over an odd local field, and over the completions of $\mathbb{F}_q(t)$

The library's classification of nondegenerate diagonal forms by discriminant and Hasse invariant
(`PadicClass.isometric_iff_invariants`, O'Meara 63:20, Serre Ch. IV §2.3, Thm. 7) is proved over an
abstract field $K$ with $2 \ne 0$ satisfying `PadicClass.LocalHilbertField K`: the Hilbert symbol is
multiplicative, every nonsquare $a$ has some $x$ with $(a, x) = -1$, and every diagonal form of
dimension $5$ is isotropic. This file proves `LocalHilbertField K` from `FF.OddLocalAxioms K`
(`OddLocalAxioms.localHilbertField`), so the classification holds at every place of $\mathbb{F}_q(t)$,
$q$ odd (`isometric_iff_invariants_finite`, `isometric_iff_invariants_infty`).

* *nonsquare $a$:* if $v(a)$ is even, $a$ is a square times a nonsquare unit $u$ and $(u, \pi) = -1$;
  if $v(a)$ is odd, $a$ is a square times a uniformizer $\pi'$ and $(\pi', w) = -1$ for a nonsquare unit $w$.
* *dimension 5* (Serre Ch. IV §2.2 for $\mathbb{Q}_p$; O'Meara 63:19): three of the five entries have
  valuations of the same parity; after scaling by squares and by a common power of $\pi$ they become
  units $w_0, w_1, w_2$, and $w_0 y_0^2 + w_1 y_1^2 + w_2 = 0$ is solvable (`unit_norm`).

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.RatFuncLocal
import QuadFormsKB.Literature.LocalGlobal.PadicClassification

open WithZero QuadFormsKB.QuadForm

namespace QuadFormsKB.FF.OddLocalAxioms

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- Every $b \ne 0$ is $w \pi^{-L(b)}$ with $w$ a unit. -/
lemma unit_decomp {π : K} (hπ : Valued.v π = exp (-1 : ℤ)) {b : K} (hb : b ≠ 0) :
    Valued.v (b * π ^ (L b)) = 1 ∧ b = (b * π ^ (L b)) * π ^ (-(L b)) := by
  have hπ0 : π ≠ 0 := ne_zero_of_v exp_ne_zero hπ
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_zpow₀, hπ, v_eq_exp hb, ← exp_zsmul, ← exp_add]; simp
  · rw [mul_assoc, ← zpow_add₀ hπ0, add_neg_cancel, zpow_zero, mul_one]

/-- **Unit ternary forms are isotropic:** for units $w_0, w_1, w_2$ some $y_0, y_1$ have
$w_0 y_0^2 + w_1 y_1^2 + w_2 = 0$. -/
lemma unit_ternary (h : OddLocalAxioms K) {w₀ w₁ w₂ : K} (h₀ : Valued.v w₀ = 1)
    (h₁ : Valued.v w₁ = 1) (h₂ : Valued.v w₂ = 1) :
    ∃ y₀ y₁ : K, w₀ * y₀ ^ 2 + w₁ * y₁ ^ 2 + w₂ = 0 := by
  have h00 : w₀ ≠ 0 := ne_zero_of_v one_ne_zero h₀
  obtain ⟨x, y, hxy⟩ := h.unit_norm (-(w₁ / w₀)) (-(w₂ / w₀))
    (by rw [Valuation.map_neg, map_div₀, h₀, h₁, div_one])
    (by rw [Valuation.map_neg, map_div₀, h₀, h₂, div_one])
  refine ⟨x, y, ?_⟩
  have : w₀ * (x ^ 2 - -(w₁ / w₀) * y ^ 2) = w₀ * -(w₂ / w₀) := by rw [hxy]
  field_simp at this
  linear_combination this

/-- **Three entries of equal valuation parity give isotropy.** For a diagonal form
$\langle a_0, \dots, a_{n-1} \rangle$ with nonzero entries and distinct indices $i, j, l$ such that
$L(a_i), L(a_j), L(a_l)$ have the same parity, the form is isotropic. -/
lemma isotropic_of_three (h : OddLocalAxioms K) {n : ℕ} (a : Fin n → K) (ha : ∀ m, a m ≠ 0)
    {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hp₁ : Even (L (a j) - L (a i))) (hp₂ : Even (L (a l) - L (a i))) :
    (diag a).IsotropicIn K := by
  classical
  obtain ⟨π, hπ⟩ := h.exists_uniformizer
  have hπ0 : π ≠ 0 := ne_zero_of_v exp_ne_zero hπ
  obtain ⟨hwi, hai⟩ := unit_decomp hπ (ha i)
  obtain ⟨hwj, haj⟩ := unit_decomp hπ (ha j)
  obtain ⟨hwl, hal⟩ := unit_decomp hπ (ha l)
  set wi := a i * π ^ (L (a i))
  set wj := a j * π ^ (L (a j))
  set wl := a l * π ^ (L (a l))
  obtain ⟨y₀, y₁, hy⟩ := h.unit_ternary hwi hwj hwl
  obtain ⟨nj, hnj⟩ := hp₁
  obtain ⟨nl, hnl⟩ := hp₂
  set e := L (a i)
  -- `a m * z m ^ 2 = π^(-e) * w_m * y_m ^ 2`
  set zi := y₀
  set zj := π ^ nj * y₁
  set zl := π ^ nl
  have ki : a i * zi ^ 2 = π ^ (-e) * (wi * y₀ ^ 2) := by
    rw [hai]; ring
  have kj : a j * zj ^ 2 = π ^ (-e) * (wj * y₁ ^ 2) := by
    rw [haj]
    have : -(L (a j)) = -e + (-nj + -nj) := by omega
    rw [this, zpow_add₀ hπ0, zpow_add₀ hπ0]
    have hinv : π ^ (-nj) * π ^ nj = 1 := by rw [← zpow_add₀ hπ0, neg_add_cancel, zpow_zero]
    linear_combination (wj * π ^ (-e) * y₁ ^ 2 * (π ^ (-nj) * π ^ nj + 1)) * hinv
  have kl : a l * zl ^ 2 = π ^ (-e) * wl := by
    rw [hal]
    have : -(L (a l)) = -e + (-nl + -nl) := by omega
    rw [this, zpow_add₀ hπ0, zpow_add₀ hπ0]
    have hinv : π ^ (-nl) * π ^ nl = 1 := by rw [← zpow_add₀ hπ0, neg_add_cancel, zpow_zero]
    linear_combination (wl * π ^ (-e) * (π ^ (-nl) * π ^ nl + 1)) * hinv
  let x : Fin n → K := fun m => if m = i then zi else if m = j then zj else if m = l then zl else 0
  refine ⟨x, ?_, ?_⟩
  · intro h0
    have := congrFun h0 l
    simp only [x, if_neg (Ne.symm hil), if_neg (Ne.symm hjl), if_pos rfl, Pi.zero_apply] at this
    exact zpow_ne_zero nl hπ0 this
  · rw [evalIn_diag]
    have hpt : ∀ m, algebraMap K K (a m) * x m ^ 2 =
        (if m = i then a i * zi ^ 2 else 0) + (if m = j then a j * zj ^ 2 else 0) +
          (if m = l then a l * zl ^ 2 else 0) := by
      intro m
      simp only [Algebra.algebraMap_self, RingHom.id_apply, x]
      by_cases h1 : m = i
      · subst h1; simp [hij, hil]
      by_cases h2 : m = j
      · subst h2; simp [h1, hjl]
      by_cases h3 : m = l
      · subst h3; simp [h1, h2]
      simp [h1, h2, h3]
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ki, kj, kl]
    linear_combination π ^ (-e) * hy

/-- **Five-dimensional forms are isotropic** under `OddLocalAxioms` (O'Meara 63:19, Serre Ch. IV
§2.2, Thm. 6 for $\mathbb{Q}_p$). -/
@[kb "omeara1963" "§63C, 63:19 [unverified]; serre1973 Ch. IV §2.2, Thm. 6 [unverified]"]
theorem isotropic_five (h : OddLocalAxioms K) (a : Fin 5 → K) (ha : ∀ i, a i ≠ 0) :
    (diag a).IsotropicIn K := by
  have par : ∀ i j : Fin 5, (Even (L (a i)) ↔ Even (L (a j))) → Even (L (a j) - L (a i)) := by
    intro i j hij
    rcases Int.even_or_odd (L (a i)) with h1 | h1
    · exact (hij.mp h1).sub h1
    · have h2 : Odd (L (a j)) := by
        rcases Int.even_or_odd (L (a j)) with h2 | h2
        · exact absurd (hij.mpr h2) (Int.not_even_iff_odd.mpr h1)
        · exact h2
      exact h2.sub_odd h1
  have key : ∀ i j l : Fin 5, i ≠ j → i ≠ l → j ≠ l → (Even (L (a i)) ↔ Even (L (a j))) →
      (Even (L (a i)) ↔ Even (L (a l))) → (diag a).IsotropicIn K :=
    fun i j l hij hil hjl h1 h2 =>
      h.isotropic_of_three a ha hij hil hjl (par i j h1) (par i l h2)
  by_cases e0 : Even (L (a 0)) <;> by_cases e1 : Even (L (a 1)) <;>
    by_cases e2 : Even (L (a 2)) <;> by_cases e3 : Even (L (a 3)) <;>
    by_cases e4 : Even (L (a 4)) <;>
    first
    | exact key 0 1 2 (by decide) (by decide) (by decide) (by tauto) (by tauto)
    | exact key 0 1 3 (by decide) (by decide) (by decide) (by tauto) (by tauto)
    | exact key 0 1 4 (by decide) (by decide) (by decide) (by tauto) (by tauto)
    | exact key 0 2 3 (by decide) (by decide) (by decide) (by tauto) (by tauto)
    | exact key 0 2 4 (by decide) (by decide) (by decide) (by tauto) (by tauto)
    | exact key 0 3 4 (by decide) (by decide) (by decide) (by tauto) (by tauto)
    | exact key 1 2 3 (by decide) (by decide) (by decide) (by tauto) (by tauto)
    | exact key 1 2 4 (by decide) (by decide) (by decide) (by tauto) (by tauto)
    | exact key 1 3 4 (by decide) (by decide) (by decide) (by tauto) (by tauto)
    | exact key 2 3 4 (by decide) (by decide) (by decide) (by tauto) (by tauto)

/-- **Every nonsquare has a $-1$ value:** for $a \ne 0$ not a square, some $x \ne 0$ has
$(a, x) = -1$. -/
theorem exists_neg_one (h : OddLocalAxioms K) (a : K) (ha : a ≠ 0) (hsq : ¬ IsSquare a) :
    ∃ x : K, x ≠ 0 ∧ hilbertSymbol K a x = -1 := by
  obtain ⟨π, hπ⟩ := h.exists_uniformizer
  have hπ0 : π ≠ 0 := ne_zero_of_v exp_ne_zero hπ
  have neg : ∀ {b x : K}, hilbertSymbol K b x ≠ 1 → hilbertSymbol K b x = -1 := fun hne =>
    (hs_pm _ _).resolve_left hne
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' (L a)
  · set u := a * π ^ (L a) with hu
    have huv : Valued.v u = 1 := (unit_decomp hπ ha).1
    have hau : a = u * (π ^ (-j)) ^ 2 := by
      rw [hu, ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ hπ0, hj]
      have : 2 * j + -j * ((2 : ℕ) : ℤ) = 0 := by push_cast; ring
      rw [this, zpow_zero, mul_one]
    have hsj : π ^ (-j) ≠ 0 := zpow_ne_zero _ hπ0
    have hns : ¬ IsSquare u := by
      intro hus; apply hsq; rw [hau]; exact hus.mul ⟨π ^ (-j), by ring⟩
    refine ⟨π, hπ0, neg ?_⟩
    rw [hau, hs_mul_sq_left _ _ _ hsj, ne_eq, h.unit_hs_iff hπ huv hns hπ0, L_of_v hπ]
    decide
  · set π' := a * π ^ (2 * j + 2) with hπ'
    have hπ'v : Valued.v π' = exp (-1 : ℤ) := by
      rw [hπ', map_mul, map_zpow₀, hπ, v_eq_exp ha, ← exp_zsmul, ← exp_add, hj]
      congr 1; simp; ring
    have hsj : π ^ (-(j + 1)) ≠ 0 := zpow_ne_zero _ hπ0
    have haπ : a = π' * (π ^ (-(j + 1))) ^ 2 := by
      rw [hπ', ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ hπ0]
      have : 2 * j + 2 + -(j + 1) * ((2 : ℕ) : ℤ) = 0 := by push_cast; ring
      rw [this, zpow_zero, mul_one]
    obtain ⟨w, hw, hwns⟩ := h.exists_nonsquare_unit
    refine ⟨w, ne_zero_of_v one_ne_zero hw, neg ?_⟩
    rw [haπ, hs_mul_sq_left _ _ _ hsj, ne_eq, h.unif_hs_unit_iff hπ'v hw]
    exact hwns

/-- **`OddLocalAxioms` gives the axioms of the abstract local classification** (`LocalHilbertField`). -/
@[kb "omeara1963" "§63B–C, 63:11, 63:19 [unverified]; serre1973 Ch. III–IV [unverified]"]
theorem localHilbertField [NeZero (2 : K)] [Infinite K] (h : OddLocalAxioms K) :
    PadicClass.LocalHilbertField K :=
  ⟨fun a a' b ha ha' hb => h.hilbertSymbol_mul_left a a' b ha ha' hb,
    fun a ha hsq => h.exists_neg_one a ha hsq,
    fun a ha => h.isotropic_five a ha⟩

end QuadFormsKB.FF.OddLocalAxioms

/-! ### At the places of $\mathbb{F}_q(t)$ -/

namespace QuadFormsKB.RatFuncPlace

open IsDedekindDomain Polynomial

open scoped Classical

variable {k : Type} [Field k]

lemma ringChar_ne_two_of_neZero [NeZero (2 : k)] : ringChar k ≠ 2 := by
  intro h
  have h0 : ((2 : ℕ) : k) = 0 := by rw [← h]; exact ringChar.Nat.cast_ringChar
  exact (two_ne_zero : (2 : k) ≠ 0) (by exact_mod_cast h0)

instance infinite_adicCompletion (w : HeightOneSpectrum k[X]) :
    Infinite (w.adicCompletion (RatFunc k)) :=
  Infinite.of_injective (algebraMap (RatFunc k) _) (algebraMap (RatFunc k) _).injective

instance infinite_completionAtInfty : Infinite (RatFunc.CompletionAtInfty k) :=
  Infinite.of_injective (algebraMap (RatFunc k) _) (algebraMap (RatFunc k) _).injective

instance neZero_two_adicCompletion [NeZero (2 : k)] (w : HeightOneSpectrum k[X]) :
    NeZero (2 : w.adicCompletion (RatFunc k)) :=
  ⟨fun h => (two_ne_zero : (2 : k) ≠ 0)
    (((algebraMap (RatFunc k) (w.adicCompletion (RatFunc k))).comp
      (algebraMap k (RatFunc k))).injective (by rw [map_ofNat, h, map_zero]))⟩

instance neZero_two_completionAtInfty [NeZero (2 : k)] :
    NeZero (2 : RatFunc.CompletionAtInfty k) :=
  ⟨fun h => (two_ne_zero : (2 : k) ≠ 0)
    (((algebraMap (RatFunc k) (RatFunc.CompletionAtInfty k)).comp
      (algebraMap k (RatFunc k))).injective (by rw [map_ofNat, h, map_zero]))⟩

/-- **Local classification at a finite place of $\mathbb{F}_q(t)$** ($q$ odd; O'Meara 63:20 for
$F = \mathbb{F}_q(t)$, Serre Ch. IV §2.3, Thm. 7 for $\mathbb{Q}_p$): two nondegenerate diagonal forms
over $k(t)_P$ are isometric iff they have the same discriminant (up to squares) and the same Hasse
invariant. -/
@[kb "omeara1963" "§63C, 63:20, p. 170 (F = F_q(t), finite place)"]
theorem isometric_iff_invariants_finite [Fintype k] [NeZero (2 : k)] (w : HeightOneSpectrum k[X])
    {n : ℕ} {a b : Fin n → w.adicCompletion (RatFunc k)} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (QuadForm.diag a).IsometricIn (w.adicCompletion (RatFunc k)) (QuadForm.diag b) ↔
      (∃ t, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i) ∧
        PadicClass.hasseVec a = PadicClass.hasseVec b :=
  PadicClass.isometric_iff_invariants
    (oddLocalAxioms_finite w ringChar_ne_two_of_neZero).localHilbertField ha hb

/-- **Local classification at the place at infinity of $\mathbb{F}_q(t)$** ($q$ odd; O'Meara 63:20 for
$F = \mathbb{F}_q(t)$): two nondegenerate diagonal forms over $k((t^{-1}))$ are isometric iff they have the
same discriminant (up to squares) and the same Hasse invariant. -/
@[kb "omeara1963" "§63C, 63:20, p. 170 (F = F_q(t), infinite place)"]
theorem isometric_iff_invariants_infty [Fintype k] [NeZero (2 : k)] {n : ℕ}
    {a b : Fin n → RatFunc.CompletionAtInfty k} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (QuadForm.diag a).IsometricIn (RatFunc.CompletionAtInfty k) (QuadForm.diag b) ↔
      (∃ t, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i) ∧
        PadicClass.hasseVec a = PadicClass.hasseVec b :=
  PadicClass.isometric_iff_invariants
    (oddLocalAxioms_infty ringChar_ne_two_of_neZero).localHilbertField ha hb

/-- **Five-dimensional forms are isotropic at every place of $\mathbb{F}_q(t)$** ($q$ odd; O'Meara 63:19
for $F = \mathbb{F}_q(t)$). -/
@[kb "omeara1963" "§63C, 63:19 [unverified] (F = F_q(t))"]
theorem isotropic_five_everywhere [Fintype k] (hk : ringChar k ≠ 2) (v : RatFuncPlace k) :
    v.atPlace fun K _ _ => ∀ a : Fin 5 → K, (∀ i, a i ≠ 0) → (QuadForm.diag a).IsotropicIn K := by
  cases v with
  | finite w => exact fun a ha => (oddLocalAxioms_finite w hk).isotropic_five a ha
  | infinite => exact fun a ha => (oddLocalAxioms_infty hk).isotropic_five a ha

end QuadFormsKB.RatFuncPlace
