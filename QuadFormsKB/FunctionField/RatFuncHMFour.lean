/-
# Hasse–Minkowski over $\mathbb{F}_q(t)$ for quaternary forms

O'Meara proves the case $n = 4$ of 66:1 by passing to the quadratic extension
$E = F(\sqrt{d})$, $d$ the discriminant, and using the ternary case over $E$; for $F = \mathbb{F}_q(t)$
this needs the Hasse norm theorem over the (hyperelliptic) function field $E$, together with the places of
$E$, which the library does not have yet. This file takes Serre's
route instead (Serre, Ch. IV §3.2, $n = 4$; it is `HMNF.hasseMinkowski_diag_four_nf` with `NFPlace`
replaced by `RatFuncPlace`), whose inputs are statements about $k(t)$ itself:

* `HilbertReciprocity k`: $\prod_v (a, b)_v = 1$ over the places of $k(t)$ (the function field case of
  O'Meara 71:18);
* `PrescribedHilbert k`: elements with prescribed local Hilbert symbols (the function field case of
  O'Meara 71:19; over $\mathbb{Q}$ it rests on Dirichlet's theorem, over $\mathbb{F}_q[t]$ on its polynomial
  analogue);
* `LocalHilbertMul k`: the local Hilbert symbol is multiplicative at every place of $k(t)$ (a purely
  local fact: O'Meara 63:11-type, Serre, Ch. III, Thm. 2 for $\mathbb{Q}_p$).

The ternary case over $k(t)$ used in the argument is proved (`hasseMinkowski_three`). The square
discriminant case needs none of the inputs (`hasseMinkowski_diag_four_of_isSquare`).

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.RatFuncHM

open IsDedekindDomain Polynomial

namespace QuadFormsKB.RatFuncPlace

variable (k : Type) [Field k]

/-- **Hilbert reciprocity over $k(t)$ (named input):** for $a, b \in k(t)^\times$, the local Hilbert
symbol $(a, b)_v$ is $-1$ at only finitely many places $v$ of $k(t)$, and at an even number of them,
i.e. $\prod_v (a,b)_v = 1$. This is the function field case of O'Meara 71:18 (stated there for number
fields); for $k(t)$ it is equivalent to quadratic reciprocity in $k[t]$. -/
@[kb "omeara1963" "§71, 71:18, p. 199 (Hilbert Reciprocity Law; function field case) [unverified]"]
structure HilbertReciprocity : Prop where
  reciprocity : ∀ a b : RatFunc k, a ≠ 0 → b ≠ 0 →
    {v : RatFuncPlace k | v.hilbert a b = -1}.Finite ∧
      Even {v : RatFuncPlace k | v.hilbert a b = -1}.ncard

/-- **Elements with prescribed local Hilbert symbols over $k(t)$ (named input):** given
$a_i \in k(t)^\times$ ($i \in \iota$, finite) and signs $\varepsilon_i(v) = \pm 1$ that are $-1$ at only
finitely many places, at an even number of places for each $i$, and locally realizable (at every place
$v$ some $x_v \in k(t)_v^\times$ has $(a_i, x_v)_v = \varepsilon_i(v)$ for all $i$), there is
$x \in k(t)^\times$ with $(a_i, x)_v = \varepsilon_i(v)$ for all $i$ and $v$. The function field case of
O'Meara 71:19 (Serre, Ch. III, Thm. 4 over $\mathbb{Q}$). -/
@[kb "omeara1963" "§71, 71:19, p. 203 (function field case) [unverified]; serre1973 Ch. III §2.2, Thm. 4 [unverified]"]
structure PrescribedHilbert : Prop where
  prescribed : ∀ {ι : Type} [Fintype ι] (a : ι → RatFunc k), (∀ i, a i ≠ 0) →
    ∀ ε : ι → RatFuncPlace k → ℤ, (∀ i v, ε i v = 1 ∨ ε i v = -1) →
    {v : RatFuncPlace k | ∃ i, ε i v = -1}.Finite →
    (∀ i, Even {v : RatFuncPlace k | ε i v = -1}.ncard) →
    (∀ v : RatFuncPlace k, v.atPlace fun K _ _ =>
      ∃ x : K, x ≠ 0 ∧ ∀ i, hilbertSymbol K (algebraMap (RatFunc k) K (a i)) x = ε i v) →
    ∃ x : RatFunc k, x ≠ 0 ∧ ∀ i v, v.hilbert (a i) x = ε i v

/-- **The local Hilbert symbol is multiplicative at every place of $k(t)$ (named input):** for every
place $v$ of $k(t)$ and $a, b, c \in k(t)_v^\times$, $(ab, c)_v = (a, c)_v (b, c)_v$. A local fact
(the completions are Laurent series fields $\kappa((\pi))$ over finite fields of odd characteristic; Serre,
Ch. III, Thm. 2 for $\mathbb{Q}_p$, $p$ odd). -/
@[kb "serre1973" "Ch. III §1.2, Thm. 2 (local fields, odd residue characteristic) [unverified]; omeara1963 §63B, 63:11a [unverified]"]
structure LocalHilbertMul : Prop where
  mul_left : ∀ v : RatFuncPlace k, v.atPlace fun K _ _ => ∀ a b c : K, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    hilbertSymbol K (a * b) c = hilbertSymbol K a c * hilbertSymbol K b c

variable {k}

/-- **$n = 4$, square discriminant** (unconditional; O'Meara 66:1, step 4, first case, for $k(t)$):
for $a_0, \dots, a_3 \in k(t)^\times$ with $a_0 a_1 a_2 a_3$ a square, $\langle a_0, a_1, a_2, a_3 \rangle$ is
isotropic over $k(t)$ iff it is isotropic at every place. *Proof* (as in `Lam.hasseMinkowski_diag_four`):
scaling by $a_0^{-1}$ gives the Pfister form $\langle 1, x, y, xy \rangle$, isotropic iff
$\langle 1, x, y \rangle$ is (`FieldGen.isotropic_pfister_iff`, over $k(t)$ and over each completion);
apply the ternary case `hasseMinkowski_three`. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (case n = 4, d V = 1, F = k(t))"]
theorem hasseMinkowski_diag_four_of_isSquare [Fintype k] (hk : ringChar k ≠ 2) (b : Fin 4 → RatFunc k)
    (hb : ∀ i, b i ≠ 0) (hsq : IsSquare (b 0 * b 1 * b 2 * b 3)) :
    (QuadForm.diag b).IsotropicIn (RatFunc k) ↔
      Everywhere (k := k) fun K _ _ => (QuadForm.diag b).IsotropicIn K := by
  have : NeZero (2 : RatFunc k) := ⟨two_ne_zero_ratFunc hk⟩
  have evalD : ∀ {n : ℕ} (L K : Type) [Field L] [Field K] [Algebra L K] (b : Fin n → L)
      (x : Fin n → K), QuadForm.evalIn K (QuadForm.diag b) x = ∑ i, algebraMap L K (b i) * x i ^ 2 := by
    intro n L K _ _ _ b x
    simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have scale : ∀ {n : ℕ} (L K : Type) [Field L] [Field K] [Algebra L K] (b b' : Fin n → L) (c : L)
      (e : Fin n → L), c ≠ 0 → (∀ i, e i ≠ 0) → (∀ i, b' i = c * b i * e i ^ 2) →
      QuadForm.IsotropicIn K (QuadForm.diag b') → QuadForm.IsotropicIn K (QuadForm.diag b) := by
    intro n L K _ _ _ b b' c e hc he hb ⟨x, hx, h0⟩
    refine ⟨fun i => algebraMap L K (e i) * x i, ?_, ?_⟩
    · intro h; apply hx; funext i
      have := congrFun h i
      simpa [he i] using this
    · rw [evalD] at h0 ⊢
      simp only [hb, map_mul, map_pow] at h0
      have : algebraMap L K c * ∑ i, algebraMap L K (b i) * (algebraMap L K (e i) * x i) ^ 2 = 0 := by
        rw [Finset.mul_sum, ← h0]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      simpa [hc] using this
  have scale' : ∀ {n : ℕ} (L K : Type) [Field L] [Field K] [Algebra L K] (b b' : Fin n → L) (c : L)
      (e : Fin n → L), c ≠ 0 → (∀ i, e i ≠ 0) → (∀ i, b' i = c * b i * e i ^ 2) →
      (QuadForm.IsotropicIn K (QuadForm.diag b) ↔ QuadForm.IsotropicIn K (QuadForm.diag b')) := by
    intro n L K _ _ _ b b' c e hc he hb
    refine ⟨scale L K b' b c⁻¹ (fun i => (e i)⁻¹) (inv_ne_zero hc) (fun i => inv_ne_zero (he i)) ?_,
      scale L K b b' c e hc he hb⟩
    intro i
    rw [hb i]; field_simp [he i]
  obtain ⟨s, hs⟩ := hsq
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3
    rw [hs, mul_zero]
  have hx : b 1 / b 0 ≠ 0 := div_ne_zero h1 h0
  have hy : b 2 / b 0 ≠ 0 := div_ne_zero h2 h0
  have key : ∀ (K : Type) [Field K] [Algebra (RatFunc k) K], QuadForm.IsotropicIn K (QuadForm.diag b) ↔
      QuadForm.IsotropicIn K (QuadForm.diag ![1, b 1 / b 0, b 2 / b 0]) := by
    intro K _ _
    rw [scale' (RatFunc k) K b ![1, b 1 / b 0, b 2 / b 0, b 1 / b 0 * (b 2 / b 0)] (b 0)⁻¹
      ![1, 1, 1, b 1 * b 2 / s] (inv_ne_zero h0) ?_ ?_]
    · exact FieldGen.isotropic_pfister_iff K _ _ hx hy
    · intro i; fin_cases i <;> simp [h1, h2, hs0]
    · intro i; fin_cases i
      · simp [h0]
      · simp; field_simp
      · simp; field_simp
      · simp
        rw [div_pow, sq s, ← hs]
        field_simp
  have nd : (QuadForm.diag ![1, b 1 / b 0, b 2 / b 0]).Nondegenerate := by
    unfold QuadForm.Nondegenerate QuadForm.hessian QuadForm.diag
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    have h2' : (2 : RatFunc k) ≠ 0 := two_ne_zero_ratFunc hk
    fin_cases i <;> simp [← two_mul, h2', hx, hy]
  rw [key (RatFunc k), hasseMinkowski_three hk _ nd]
  constructor
  · intro h v
    have := h v
    cases v with
    | finite w => exact (key _).2 this
    | infinite => exact (key _).2 this
  · intro h v
    have := h v
    cases v with
    | finite w => exact (key _).1 this
    | infinite => exact (key _).1 this

/-- **$n = 4$ over $\mathbb{F}_q(t)$, diagonal form $\langle a_1, a_2, -a_3, -a_4 \rangle$ (conditional on
the named inputs `HilbertReciprocity`, `PrescribedHilbert`, `LocalHilbertMul`).** Serre's argument
(Ch. IV §3.2), as in `HMNF.hasseMinkowski_diag_four_nf`: choose $x \in k(t)^\times$ with
$(x, -a_1 a_2)_v = (a_1, a_2)_v$ and $(x, -a_3 a_4)_v = (a_3, a_4)_v$ at every $v$ (prescribed symbols;
the parity condition is reciprocity, local solvability is `FieldGen.exists_common_value`); then $x$ is
represented by $\langle a_1, a_2 \rangle$ and by $\langle a_3, a_4 \rangle$ over $k(t)$, by the Hasse norm
theorem `hilbert_eq_one_of_everywhere` (proved). -/
@[kb "serre1973" "Ch. IV §3.2 (n = 4) [unverified]; omeara1963 §66, 66:1, p. 187 (case n = 4, F = k(t))"]
theorem hasseMinkowski_diag_four_of_inputs [Fintype k] (hk : ringChar k ≠ 2)
    (hR : HilbertReciprocity k) (hP : PrescribedHilbert k) (hM : LocalHilbertMul k)
    (a₁ a₂ a₃ a₄ : RatFunc k) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0) (h₄ : a₄ ≠ 0) :
    (QuadForm.diag ![a₁, a₂, -a₃, -a₄]).IsotropicIn (RatFunc k) ↔
      Everywhere (k := k) fun K _ _ => (QuadForm.diag ![a₁, a₂, -a₃, -a₄]).IsotropicIn K := by
  classical
  have : NeZero (2 : RatFunc k) := ⟨two_ne_zero_ratFunc hk⟩
  have pm : ∀ (K : Type) [Field K] (a b : K), hilbertSymbol K a b = 1 ∨ hilbertSymbol K a b = -1 := by
    intro K _ a b
    unfold hilbertSymbol
    split_ifs <;> simp
  have key : ∀ (K : Type) [Field K]
      (hm : ∀ a a' b : K, a ≠ 0 → a' ≠ 0 → b ≠ 0 →
        hilbertSymbol K (a * a') b = hilbertSymbol K a b * hilbertSymbol K a' b)
      (a b x : K), a ≠ 0 → b ≠ 0 → x ≠ 0 →
      hilbertSymbol K (a / x) (b / x) = hilbertSymbol K a b * hilbertSymbol K x (-(a * b)) := by
    intro K _ hm a b x ha hb hx
    have hmr : ∀ a b b' : K, a ≠ 0 → b ≠ 0 → b' ≠ 0 →
        hilbertSymbol K a (b * b') = hilbertSymbol K a b * hilbertSymbol K a b' := by
      intro a b b' ha hb hb'
      rw [hilbertSymbol_comm, hm _ _ _ hb hb' ha, hilbertSymbol_comm K b, hilbertSymbol_comm K b']
    have hxi : x⁻¹ ≠ 0 := inv_ne_zero hx
    have e1 : a / x = (a * x) * (x⁻¹) ^ 2 := by field_simp
    have e2 : b / x = (b * x) * (x⁻¹) ^ 2 := by field_simp
    rw [e1, HM3.hilbertSymbol_mul_sq_left _ _ _ _ hxi, hilbertSymbol_comm,
      e2, HM3.hilbertSymbol_mul_sq_left _ _ _ _ hxi, hilbertSymbol_comm]
    have hxx : hilbertSymbol K x x = hilbertSymbol K x (-1) := by
      have h0 := hilbertSymbol_self_neg K x
      have : -x = x * (-1) := by ring
      rw [this, hmr _ _ _ hx hx (by norm_num)] at h0
      rcases pm K x x with h | h <;> rcases pm K x (-1) with h' | h' <;>
        rw [h, h'] at h0 <;> rw [h, h'] <;> norm_num at h0
    have hab : -(a * b) = a * (b * (-1)) := by ring
    rw [hm _ _ _ ha hx (mul_ne_zero hb hx), hmr _ _ _ ha hb hx, hmr _ _ _ hx hb hx, hab,
      hmr _ _ _ hx ha (mul_ne_zero hb (by norm_num)), hmr _ _ _ hx hb (by norm_num), ← hxx,
      hilbertSymbol_comm K a x]
    ring
  have placeKey : ∀ (v : RatFuncPlace k) (a b x : RatFunc k), a ≠ 0 → b ≠ 0 → x ≠ 0 →
      v.hilbert (a / x) (b / x) = v.hilbert a b * v.hilbert x (-(a * b)) := by
    intro v a b x ha hb hx
    have hv := hM.mul_left v
    cases v with
    | finite v =>
      simp only [RatFuncPlace.hilbert, map_div₀, map_mul, map_neg]
      exact key _ hv _ _ _ ((_root_.map_ne_zero _).mpr ha) ((_root_.map_ne_zero _).mpr hb) ((_root_.map_ne_zero _).mpr hx)
    | infinite =>
      simp only [RatFuncPlace.hilbert, map_div₀, map_mul, map_neg]
      exact key _ hv _ _ _ ((_root_.map_ne_zero _).mpr ha) ((_root_.map_ne_zero _).mpr hb) ((_root_.map_ne_zero _).mpr hx)
  have placeComm : ∀ (v : RatFuncPlace k) (a b : RatFunc k), v.hilbert a b = v.hilbert b a := by
    intro v a b
    cases v <;> exact hilbertSymbol_comm _ _ _
  have placePm : ∀ (v : RatFuncPlace k) (a b : RatFunc k), v.hilbert a b = 1 ∨ v.hilbert a b = -1 := by
    intro v a b
    cases v <;> exact pm _ _ _
  have binrep : ∀ a b x : RatFunc k, a ≠ 0 → b ≠ 0 → x ≠ 0 →
      (∀ v : RatFuncPlace k, v.hilbert (-(a * b)) x = v.hilbert a b) →
      ∃ X Y : RatFunc k, a * X ^ 2 + b * Y ^ 2 = x := by
    intro a b x ha hb hx h
    rw [HM4.binary_represents_iff (RatFunc k) a b x ha hb hx]
    apply hilbert_eq_one_of_everywhere hk _ _ (div_ne_zero ha hx) (div_ne_zero hb hx)
    intro v
    rw [placeKey v a b x ha hb hx, placeComm v x, h v]
    rcases placePm v a b with h' | h' <;> rw [h'] <;> norm_num
  constructor
  · intro h v
    cases v <;> exact FieldGen.isotropicIn_of_base _ _ h
  · intro h
    obtain ⟨x, hx, hxv⟩ := hP.prescribed (ι := Fin 2) ![-(a₁ * a₂), -(a₃ * a₄)]
      (by intro i; fin_cases i <;> simp [h₁, h₂, h₃, h₄])
      ![fun v => v.hilbert a₁ a₂, fun v => v.hilbert a₃ a₄]
      (by intro i v; fin_cases i <;> exact placePm _ _ _)
      (((hR.reciprocity a₁ a₂ h₁ h₂).1.union (hR.reciprocity a₃ a₄ h₃ h₄).1).subset (by
        rintro v ⟨i, hi⟩
        fin_cases i
        · left; simpa using hi
        · right; simpa using hi))
      (by
        intro i
        fin_cases i
        · simpa using (hR.reciprocity a₁ a₂ h₁ h₂).2
        · simpa using (hR.reciprocity a₃ a₄ h₃ h₄).2)
      (by
        intro v
        cases v with
        | finite w =>
          obtain ⟨y, hy, e1, e2⟩ := FieldGen.exists_common_value
            (w.adicCompletion (RatFunc k)) a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄ (h (.finite w))
          refine ⟨y, hy, ?_⟩
          intro i
          fin_cases i
          · simp only [RatFuncPlace.hilbert]
            rw [hilbertSymbol_comm]
            simpa using e1
          · simp only [RatFuncPlace.hilbert]
            rw [hilbertSymbol_comm]
            simpa using e2
        | infinite =>
          obtain ⟨y, hy, e1, e2⟩ := FieldGen.exists_common_value
            (RatFunc.CompletionAtInfty k) a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄ (h .infinite)
          refine ⟨y, hy, ?_⟩
          intro i
          fin_cases i
          · simp only [RatFuncPlace.hilbert]
            rw [hilbertSymbol_comm]
            simpa using e1
          · simp only [RatFuncPlace.hilbert]
            rw [hilbertSymbol_comm]
            simpa using e2)
    obtain ⟨X, Y, hXY⟩ := binrep a₁ a₂ x h₁ h₂ hx (fun v => by simpa using hxv 0 v)
    obtain ⟨Z, W, hZW⟩ := binrep a₃ a₄ x h₃ h₄ hx (fun v => by simpa using hxv 1 v)
    refine ⟨![X, Y, Z, W], ?_, ?_⟩
    · intro h0
      have hX : X = 0 := congrFun h0 0
      have hY : Y = 0 := congrFun h0 1
      apply hx
      rw [← hXY, hX, hY]; ring
    · simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four]
      linear_combination hXY - hZW

/-- **Hasse–Minkowski over $\mathbb{F}_q(t)$ for $n = 4$** (O'Meara 66:1, $n = 4$, $F = \mathbb{F}_q(t)$,
$q$ odd; conditional on the named inputs `HilbertReciprocity`, `PrescribedHilbert`, `LocalHilbertMul`):
a nondegenerate quaternary form over $k(t)$ is isotropic iff it is isotropic at every place. By
diagonalization from `hasseMinkowski_diag_four_of_inputs`. -/
@[kb "omeara1963" "§66, 66:1, p. 187 (case n = 4, F = k(t))"]
theorem hasseMinkowski_four_of_inputs [Fintype k] (hk : ringChar k ≠ 2)
    (hR : HilbertReciprocity k) (hP : PrescribedHilbert k) (hM : LocalHilbertMul k)
    (Q : QuadForm (RatFunc k) 4) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn (RatFunc k) ↔ Everywhere (k := k) fun K _ _ => Q.IsotropicIn K := by
  have : NeZero (2 : RatFunc k) := ⟨two_ne_zero_ratFunc hk⟩
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have hd : QuadForm.diag a = QuadForm.diag ![a 0, a 1, -(-a 2), -(-a 3)] := by
    congr 1
    funext i
    fin_cases i <;> simp
  have hT : ∀ (K : Type) [Field K] [Algebra (RatFunc k) K],
      Q.IsotropicIn K ↔ (QuadForm.diag ![a 0, a 1, -(-a 2), -(-a 3)]).IsotropicIn K := by
    intro K _ _
    rw [← hd]
    exact FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso)
  rw [hT (RatFunc k)]
  rw [hasseMinkowski_diag_four_of_inputs hk hR hP hM (a 0) (a 1) (-a 2) (-a 3) (ha 0) (ha 1)
    (neg_ne_zero.mpr (ha 2)) (neg_ne_zero.mpr (ha 3))]
  constructor
  · intro h v
    cases v with
    | finite w => exact (hT _).2 (h (.finite w))
    | infinite => exact (hT _).2 (h .infinite)
  · intro h v
    cases v with
    | finite w => exact (hT _).1 (h (.finite w))
    | infinite => exact (hT _).1 (h .infinite)

end QuadFormsKB.RatFuncPlace
