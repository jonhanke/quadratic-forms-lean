/-
# Hasse–Minkowski for quaternary forms: the blueprint

Serre, *A Course in Arithmetic*, IV §3.2, case $n = 4$. For
$f = \langle a_1, a_2, -a_3, -a_4 \rangle$ ($a_i \in \mathbb{Q}^\times$):

1. a binary form $\langle a, b \rangle$ represents $x \ne 0$ over a field $K$ iff
   $(x, -ab)_K = (a, b)_K$;
2. if $f$ is isotropic over $\mathbb{Q}_v$, some $x_v \ne 0$ is represented by both $\langle a_1, a_2 \rangle$
   and $\langle a_3, a_4 \rangle$ over $\mathbb{Q}_v$;
3. prescribed local symbols glue the $x_v$ into one rational $x$;
4. by $n = 3$, both binary forms represent $x$ over $\mathbb{Q}$, so $f$ is isotropic over $\mathbb{Q}$.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.LocalGlobal.PrescribedSymbols
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiThree

namespace QuadFormsKB.HM4

open RatPlace HM3

/-- **Binary forms and the Hilbert symbol** (valid over every field): over a field
$K \supseteq \mathbb{Q}$, for nonzero $a, b, x$, the form $a X^2 + b Y^2$ takes the value $x$ for some
$X, Y \in K$ iff $\left(\tfrac{a}{x}, \tfrac{b}{x}\right)_K = 1$ (i.e. $\langle -x, a, b \rangle$ is
isotropic).

*Caution.* The often-quoted form "$(x, -ab)_K = (a, b)_K$" needs bimultiplicativity of the
symbol, which holds over $\mathbb{Q}_p$ and $\mathbb{R}$ but **not** over $\mathbb{Q}$: for $a = b = -1$,
$x = 3$ it gives $-1 = -1$ although $-X^2 - Y^2 = 3$ has no rational solution (counterexample
found by llmprove). -/
@[kb "serre1973" "Ch. IV §2.2, Thm. 6 (n = 2) [unverified]"]
theorem binary_represents_iff (K : Type*) [Field K] [CharZero K] (a b x : K) (ha : a ≠ 0)
    (hb : b ≠ 0) (hx : x ≠ 0) :
    (∃ X Y : K, a * X ^ 2 + b * Y ^ 2 = x) ↔ hilbertSymbol K (a / x) (b / x) = 1 := by
  rw [hilbertSymbol_eq_one_iff_conic K two_ne_zero (div_ne_zero ha hx) (div_ne_zero hb hx)]
  have key : ∀ X Y : K, a / x * X ^ 2 + b / x * Y ^ 2 = (a * X ^ 2 + b * Y ^ 2) / x := by
    intro X Y; ring
  constructor
  · rintro ⟨X, Y, h⟩
    refine ⟨X, Y, ?_⟩
    rw [key, h, div_self hx]
  · rintro ⟨X, Y, h⟩
    refine ⟨X, Y, ?_⟩
    rw [key, div_eq_one_iff_eq hx] at h
    exact h

/-- **A common local value:** over a field $K \supseteq \mathbb{Q}$, if
$\langle a_1, a_2, -a_3, -a_4 \rangle$ (nonzero rationals) is isotropic over $K$, then some $x \ne 0$ in $K$
is represented by both $\langle a_1, a_2 \rangle$ and $\langle a_3, a_4 \rangle$ over $K$, in Hilbert-symbol
form. -/
@[kb "serre1973" "Ch. IV §3.2 (n = 4) [unverified]"]
theorem exists_common_value (K : Type*) [Field K] [CharZero K] (a₁ a₂ a₃ a₄ : ℚ)
    (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0) (h₄ : a₄ ≠ 0)
    (hiso : (QuadForm.diag ![a₁, a₂, -a₃, -a₄]).IsotropicIn K) :
    ∃ x : K, x ≠ 0 ∧
      hilbertSymbol K x (algebraMap ℚ K (-(a₁ * a₂))) = hilbertSymbol K (algebraMap ℚ K a₁) (algebraMap ℚ K a₂) ∧
      hilbertSymbol K x (algebraMap ℚ K (-(a₃ * a₄))) = hilbertSymbol K (algebraMap ℚ K a₃) (algebraMap ℚ K a₄) := by
  have L : ∀ (a b x X Y : K), a ≠ 0 → b ≠ 0 → x ≠ 0 → a*X^2+b*Y^2 = x →
      hilbertSymbol K x (-(a*b)) = hilbertSymbol K a b := by
    intro a b x X Y ha hb hx hX
    unfold hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨s, t, r, hne, hr⟩
      by_cases hs : s = 0
      · subst hs
        have ht : t ≠ 0 := by
          rintro rfl
          apply hne
          have : r = 0 := by simpa using hr
          simp [this]
        refine ⟨r, a*t, 0, ?_, ?_⟩
        · intro h
          simp [Prod.ext_iff] at h
          exact ht (h.2.resolve_left ha)
        · linear_combination (-a) * hr
      · refine ⟨X*r - b*Y*t, Y*r + a*X*t, x*s, ?_, ?_⟩
        · intro h
          simp [Prod.ext_iff] at h
          tauto
        · linear_combination (-x) * hr + (-(r^2 + a*b*t^2)) * hX
    · rintro ⟨u, v, w, hne, hw⟩
      by_cases hw0 : w = 0
      · subst hw0
        have hu : u ≠ 0 := by
          rintro rfl
          apply hne
          have : v = 0 := by simpa [hb] using hw
          simp [this]
        refine ⟨0, u, b*v, ?_, ?_⟩
        · intro h
          simp [Prod.ext_iff] at h
          exact hu h.1
        · linear_combination (-b) * hw
      · refine ⟨w, X*v - Y*u, a*X*u + b*Y*v, ?_, ?_⟩
        · intro h
          simp [Prod.ext_iff] at h
          tauto
        · linear_combination (-(a*X^2+b*Y^2)) * hw + (w^2) * hX
  have L0 : ∀ (a b u w : K), a ≠ 0 → b ≠ 0 → (u ≠ 0 ∨ w ≠ 0) → a*u^2+b*w^2 = 0 →
      (∀ y, hilbertSymbol K y (-(a*b)) = 1) ∧ hilbertSymbol K a b = 1 := by
    intro a b u w ha hb huw h
    have hu : u ≠ 0 := by
      rintro rfl
      have : w = 0 := by simpa [hb] using h
      simp_all
    constructor
    · intro y
      unfold hilbertSymbol
      rw [if_pos]
      refine ⟨0, u, b*w, ?_, ?_⟩
      · intro h'
        simp [Prod.ext_iff] at h'
        exact hu h'.1
      · linear_combination b * h
    · unfold hilbertSymbol
      rw [if_pos]
      refine ⟨u, w, 0, ?_, ?_⟩
      · intro h'
        simp [Prod.ext_iff] at h'
        exact hu h'.1
      · linear_combination (-1:K) * h
  obtain ⟨v, hv0, hv⟩ := hiso
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal] at hv
  simp only [map_neg, map_mul, eq_ratCast]
  have A1 : (a₁ : K) ≠ 0 := by exact_mod_cast h₁
  have A2 : (a₂ : K) ≠ 0 := by exact_mod_cast h₂
  have A3 : (a₃ : K) ≠ 0 := by exact_mod_cast h₃
  have A4 : (a₄ : K) ≠ 0 := by exact_mod_cast h₄
  by_cases hx : (a₁:K) * v 0 ^ 2 + (a₂:K) * v 1 ^ 2 = 0
  · by_cases h01 : v 0 ≠ 0 ∨ v 1 ≠ 0
    · obtain ⟨H1, H2⟩ := L0 _ _ _ _ A1 A2 h01 hx
      refine ⟨(a₃:K), A3, ?_, ?_⟩
      · rw [H1, H2]
      · exact L _ _ _ 1 0 A3 A4 A3 (by ring)
    · have h23 : v 2 ≠ 0 ∨ v 3 ≠ 0 := by
        by_contra hc
        push_neg at hc h01
        apply hv0
        funext i
        fin_cases i <;> simp [*]
      obtain ⟨H1, H2⟩ := L0 _ _ _ _ A3 A4 h23 (by linear_combination (-1:K) * hv + hx)
      refine ⟨(a₁:K), A1, ?_, ?_⟩
      · exact L _ _ _ 1 0 A1 A2 A1 (by ring)
      · rw [H1, H2]
  · refine ⟨_, hx, L _ _ _ _ _ A1 A2 hx rfl, L _ _ _ (v 2) (v 3) A3 A4 hx ?_⟩
    linear_combination (-1:K) * hv

/-- **From local symbols to a global value:** for nonzero rationals $a, b, x$, if
$(x, -ab)_v = (a, b)_v$ at every place $v$, then $a X^2 + b Y^2 = x$ has a rational solution
(by $n = 3$ applied to $\langle a, b, -x \rangle$). -/
@[kb "serre1973" "Ch. IV §3.2 (n = 4) [unverified]"]
theorem binary_represents_rat_of_everywhere (a b x : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0)
    (h : ∀ v : RatPlace, v.hilbert x (-(a * b)) = v.hilbert a b) :
    ∃ X Y : ℚ, a * X ^ 2 + b * Y ^ 2 = x := by
  have hpm : ∀ (v : RatPlace) (u w : ℚ), v.hilbert u w = 1 ∨ v.hilbert u w = -1 := by
    intro v u w
    cases v <;> simp only [RatPlace.hilbert, hilbertSymbol] <;> split_ifs <;> simp
  have hcomm : ∀ (v : RatPlace) (u w : ℚ), v.hilbert u w = v.hilbert w u := by
    intro v u w
    cases v <;> simp only [RatPlace.hilbert] <;> exact hilbertSymbol_comm _ _ _
  have hself : ∀ (v : RatPlace) (u : ℚ), v.hilbert u (-u) = 1 := by
    intro v u
    cases v <;> simp only [RatPlace.hilbert] <;> push_cast <;> exact hilbertSymbol_self_neg _ _
  have hloc : ∀ v : RatPlace, v.hilbert (a * x) (b * x) = 1 := by
    intro v
    have mL := HilbertLocal.RatPlace.hilbert_mul_left v
    have e1 : v.hilbert (a * x) (b * x) = v.hilbert a b * v.hilbert x a * v.hilbert b x * v.hilbert x x := by
      rw [mL _ _ _ ha hx (mul_ne_zero hb hx), hcomm v a, hcomm v x (b*x),
        mL _ _ _ hb hx ha, mL _ _ _ hb hx hx, hcomm v b a]
      ring
    have e2 : v.hilbert x (-(a*b)) = v.hilbert (-1) x * v.hilbert a x * v.hilbert b x := by
      rw [hcomm v x, show -(a*b) = (-1) * (a * b) by ring, mL _ _ _ (by norm_num) (mul_ne_zero ha hb) hx,
        mL _ _ _ ha hb hx]
      ring
    have e3 : v.hilbert (-1) x * v.hilbert x x = 1 := by
      have := hself v x
      rw [hcomm, show -x = (-1) * x by ring, mL _ _ _ (by norm_num) hx hx] at this
      exact this
    have hv := h v
    rw [e1, hcomm v x a]
    rw [e2] at hv
    clear hcomm hself mL h e1 e2
    revert hv e3
    rcases hpm v a b with h1 | h1 <;> rcases hpm v a x with h2 | h2 <;>
      rcases hpm v b x with h3 | h3 <;> rcases hpm v x x with h4 | h4 <;>
      rcases hpm v (-1) x with h5 | h5 <;> simp only [h1, h2, h3, h4, h5] <;> norm_num
  have hq := HM3.hilbert_rat_eq_one_of_everywhere _ _ (mul_ne_zero ha hx) (mul_ne_zero hb hx) hloc
  obtain ⟨u, w, huw⟩ := (hilbertSymbol_eq_one_iff_conic ℚ (by norm_num) (mul_ne_zero ha hx) (mul_ne_zero hb hx)).1 hq
  refine ⟨x * u, x * w, ?_⟩
  linear_combination x * huw

/-- **Hasse–Minkowski for diagonal quaternary forms:** for nonzero rationals,
$\langle a_1, a_2, -a_3, -a_4 \rangle$ is isotropic over $\mathbb{Q}$ iff it is isotropic over every
completion. -/
@[kb "serre1973" "Ch. IV §3.2, Thm. 8 (n = 4) [unverified]; cassels1978 Ch. 6, §5, p. 83"]
theorem hasseMinkowski_diag_four (a₁ a₂ a₃ a₄ : ℚ) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0)
    (h₄ : a₄ ≠ 0) :
    (QuadForm.diag ![a₁, a₂, -a₃, -a₄]).IsotropicIn ℚ ↔
      Everywhere fun K _ _ => (QuadForm.diag ![a₁, a₂, -a₃, -a₄]).IsotropicIn K := by
  constructor
  · rintro ⟨v, hv0, hv⟩ w
    have gen : ∀ (K : Type) [Field K] [CharZero K], QuadForm.IsotropicIn K (QuadForm.diag ![a₁, a₂, -a₃, -a₄]) := by
      intro K _ _
      refine ⟨fun i => (v i : K), ?_, ?_⟩
      · intro h
        apply hv0
        funext i
        have := congrFun h i
        simpa using this
      · simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal] at hv ⊢
        exact_mod_cast hv
    cases w <;> simp only [atPlace] <;> exact gen _
  · intro H
    have hpm : ∀ (v : RatPlace) (u w : ℚ), v.hilbert u w = 1 ∨ v.hilbert u w = -1 := by
      intro v u w
      cases v <;> simp only [RatPlace.hilbert, hilbertSymbol] <;> split_ifs <;> simp
    have hcomm : ∀ (v : RatPlace) (u w : ℚ), v.hilbert u w = v.hilbert w u := by
      intro v u w
      cases v <;> simp only [RatPlace.hilbert] <;> exact hilbertSymbol_comm _ _ _
    have key : ∀ (K : Type) [Field K] [CharZero K], QuadForm.IsotropicIn K (QuadForm.diag ![a₁, a₂, -a₃, -a₄]) → ∃ x : K, x ≠ 0 ∧ hilbertSymbol K (algebraMap ℚ K (-(a₁*a₂))) x = hilbertSymbol K (algebraMap ℚ K a₁) (algebraMap ℚ K a₂) ∧ hilbertSymbol K (algebraMap ℚ K (-(a₃*a₄))) x = hilbertSymbol K (algebraMap ℚ K a₃) (algebraMap ℚ K a₄) := by
      intro K _ _ hK
      obtain ⟨x, hx, e1, e2⟩ := HM4.exists_common_value K a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄ hK
      exact ⟨x, hx, by rw [hilbertSymbol_comm]; exact e1, by rw [hilbertSymbol_comm]; exact e2⟩
    obtain ⟨x, hx0, hx⟩ := Prescribed.exists_rat_prescribed_hilbert (ι := Fin 2) ![-(a₁*a₂), -(a₃*a₄)]
      (by intro i; fin_cases i <;> simp [h₁, h₂, h₃, h₄])
      ![fun v => v.hilbert a₁ a₂, fun v => v.hilbert a₃ a₄]
      (by intro i v; fin_cases i <;> simp [hpm])
      (by
        apply ((HilbertLocal.hilbert_support_finite a₁ a₂ h₁ h₂).union (HilbertLocal.hilbert_support_finite a₃ a₄ h₃ h₄)).subset
        intro v ⟨i, hi⟩
        fin_cases i
        · left; simpa using hi
        · right; simpa using hi)
      (by
        intro i; fin_cases i
        · simpa using (hilbert_product_formula a₁ a₂ h₁ h₂).2
        · simpa using (hilbert_product_formula a₃ a₄ h₃ h₄).2)
      (by
        intro v
        have := H v
        cases v <;> simp only [atPlace] at this ⊢
        · obtain ⟨y, hy, e1, e2⟩ := key ℝ this
          refine ⟨y, hy, ?_⟩
          intro i; fin_cases i
          · simpa [RatPlace.hilbert] using e1
          · simpa [RatPlace.hilbert] using e2
        · obtain ⟨y, hy, e1, e2⟩ := key _ this
          refine ⟨y, hy, ?_⟩
          intro i; fin_cases i
          · simpa [RatPlace.hilbert] using e1
          · simpa [RatPlace.hilbert] using e2)
    obtain ⟨X, Y, hXY⟩ := HM4.binary_represents_rat_of_everywhere a₁ a₂ x h₁ h₂ hx0 (fun v => by
      rw [hcomm]; simpa using hx 0 v)
    obtain ⟨Z, W, hZW⟩ := HM4.binary_represents_rat_of_everywhere a₃ a₄ x h₃ h₄ hx0 (fun v => by
      rw [hcomm]; simpa using hx 1 v)
    refine ⟨![X, Y, Z, W], ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      apply hx0
      rw [← hXY, h0, h1]; ring
    · simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal]
      linear_combination hXY - hZW

end QuadFormsKB.HM4
