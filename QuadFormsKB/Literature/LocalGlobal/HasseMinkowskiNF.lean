/-
# Hasse–Minkowski over a number field $F$: the blueprint

Proved **conditionally on the inputs** bundled in `NumberFieldInputs.lean`: Hilbert reciprocity,
squares local–global, prescribed local symbols, the Hasse norm theorem for quadratic extensions,
and multiplicativity of the Hilbert symbol at finite places. Each step takes the inputs as one
explicit hypothesis `I : HMInputs F`, so the reduction is kernel-checked. All the inputs are
now proved (`NumberFieldMain.lean`), and `hasseMinkowski_nf` itself is proved by Lam's route
(`HasseMinkowskiNFMain.lean`).

The structure follows the $\mathbb{Q}$ proof (Serre IV §3), except for $n \ge 5$:
- $n = 2$: $\langle a, b \rangle$ is isotropic iff $-ab$ is a square (squares local–global);
- $n = 3$: the ternary criterion plus the Hasse norm theorem;
- $n = 4$: a common value $x$ of $\langle a_1, a_2 \rangle$ and $\langle a_3, a_4 \rangle$ chosen
  with prescribed local symbols, then the binary case of $n = 3$;
- $n \ge 5$: Lam's induction (VI, Thm. 3.1): split
  $\langle a_0, a_1 \rangle \perp \langle a_2, \dots \rangle$, pick a global value $t$ of
  $\langle a_0, a_1 \rangle$ by weak approximation, and apply the rank $n - 1$ case to
  $\langle t, a_2, \dots \rangle$; away from finitely many places it is isotropic because it
  contains three unit coefficients.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.LocalGlobal.NumberFieldLocal

open NumberField

namespace QuadFormsKB

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

namespace HMNF

/-- **Binary representation, local–global (conditional):** for $a, b, x \in F^\times$, if
$(x, -ab)_v = (a, b)_v$ at every place $v$ of $F$, then $a X^2 + b Y^2 = x$ has a solution
$X, Y \in F$. (From multiplicativity of the local symbols and the Hasse norm theorem; the
$F = \mathbb{Q}$ case is `HM4.binary_represents_rat_of_everywhere`.) -/
@[kb "serre1973" "Ch. IV §3.2 (n = 4) [unverified]"]
theorem binary_represents_nf_of_everywhere (I : NFInputs.HMInputs F) (a b x : F) (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0)
    (h : ∀ v : NFPlace F, v.hilbert x (-(a * b)) = v.hilbert a b) :
    ∃ X Y : F, a * X ^ 2 + b * Y ^ 2 = x := by
  have pm : ∀ (K : Type) [Field K] (a b : K), hilbertSymbol K a b = 1 ∨ hilbertSymbol K a b = -1 := by
    intro K _ a b; unfold hilbertSymbol; split_ifs <;> simp
  have transport : ∀ {K L : Type} [Field K] [Field L] (e : K ≃+* L) (a b : K),
      hilbertSymbol K a b = hilbertSymbol L (e a) (e b) := by
    intro K L _ _ e a b
    have hiff : (∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) ↔
        (∃ x y z : L, (x, y, z) ≠ 0 ∧ z ^ 2 = e a * x ^ 2 + e b * y ^ 2) := by
      constructor
      · rintro ⟨x, y, z, hne, heq⟩
        refine ⟨e x, e y, e z, ?_, ?_⟩
        · intro h0; apply hne; simp [Prod.ext_iff] at h0 ⊢; exact h0
        · rw [← map_pow, heq]; simp
      · rintro ⟨x, y, z, hne, heq⟩
        refine ⟨e.symm x, e.symm y, e.symm z, ?_, ?_⟩
        · intro h0; apply hne; simp [Prod.ext_iff] at h0 ⊢; exact h0
        · apply e.injective; simp [heq]
    unfold hilbertSymbol
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  have key : ∀ (K : Type) [Field K], (∀ a a' b : K, a ≠ 0 → a' ≠ 0 → b ≠ 0 →
      hilbertSymbol K (a * a') b = hilbertSymbol K a b * hilbertSymbol K a' b) →
      ∀ a b x : K, a ≠ 0 → b ≠ 0 → x ≠ 0 → hilbertSymbol K x (-(a * b)) = hilbertSymbol K a b →
      hilbertSymbol K (a / x) (b / x) = 1 := by
    intro K _ hmul a b x ha hb hx hh
    have hc := hilbertSymbol_comm K
    have e1 : hilbertSymbol K (a / x) (b / x) = hilbertSymbol K (a * x) (b * x) := by
      have h1 : a / x = (a * x) * (x⁻¹) ^ 2 := by field_simp
      have h2 : b / x = (b * x) * (x⁻¹) ^ 2 := by field_simp
      rw [h1, h2, HM3.hilbertSymbol_mul_sq_left _ _ _ _ (inv_ne_zero hx), hc,
        HM3.hilbertSymbol_mul_sq_left _ _ _ _ (inv_ne_zero hx), hc]
    have hn1 : (-1 : K) ≠ 0 := by simp
    have e2 : hilbertSymbol K (a * x) (b * x) = hilbertSymbol K b a * hilbertSymbol K x a *
        (hilbertSymbol K b x * hilbertSymbol K x x) := by
      rw [hmul _ _ _ ha hx (mul_ne_zero hb hx), hc a, hc x, hmul _ _ _ hb hx ha,
        hmul _ _ _ hb hx hx]
    have e3 : hilbertSymbol K x x = hilbertSymbol K (-1) x := by
      have := hilbertSymbol_self_neg K x
      rw [hc, show -x = (-1) * x by ring, hmul _ _ _ hn1 hx hx] at this
      rcases pm K (-1) x with h' | h' <;> rcases pm K x x with h'' | h'' <;>
        simp only [h', h''] at this ⊢ <;> norm_num at this
    have e4 : hilbertSymbol K x (-(a * b)) = hilbertSymbol K (-1) x * hilbertSymbol K a x *
        hilbertSymbol K b x := by
      rw [hc, show -(a * b) = (-1) * a * b by ring, hmul _ _ _ (mul_ne_zero hn1 ha) hb hx,
        hmul _ _ _ hn1 ha hx]
    rw [e1, e2, e3, hc b a, hc x a]
    have : hilbertSymbol K a b * hilbertSymbol K a b = 1 := by
      rcases pm K a b with h' | h' <;> rw [h'] <;> norm_num
    calc _ = hilbertSymbol K a b * (hilbertSymbol K (-1) x * hilbertSymbol K a x *
        hilbertSymbol K b x) := by ring
      _ = 1 := by rw [← e4, hh, this]
  have hC : ∀ A B : ℂ, hilbertSymbol ℂ A B = 1 := by
    intro A B
    obtain ⟨z, hz⟩ := IsAlgClosed.isSquare A
    unfold hilbertSymbol
    rw [if_pos]
    exact ⟨1, 0, z, by simp, by rw [hz]; ring⟩
  rw [HM4.binary_represents_iff F a b x ha hb hx]
  apply I.hasse_norm _ _ (div_ne_zero ha hx) (div_ne_zero hb hx)
  intro v
  have hv := h v
  cases v with
  | infinite w =>
    simp only [NFPlace.hilbert, map_div₀, map_neg, map_mul] at hv ⊢
    rcases w.isReal_or_isComplex with hw | hw
    · apply key _ ?_ _ _ _ ((map_ne_zero _).2 ha) ((map_ne_zero _).2 hb) ((map_ne_zero _).2 hx) hv
      intro A A' B hA hA' hB
      rw [transport (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw),
        transport (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) A,
        transport (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) A', map_mul]
      exact HilbertLocal.hilbertSymbol_real_mul_left _ _ _ (by simpa using hA) (by simpa using hA')
        (by simpa using hB)
    · rw [transport (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)]
      exact hC _ _
  | finite w =>
    simp only [NFPlace.hilbert, map_div₀, map_neg, map_mul] at hv ⊢
    exact key _ (I.mul_left_finite w) _ _ _ ((map_ne_zero _).2 ha) ((map_ne_zero _).2 hb)
      ((map_ne_zero _).2 hx) hv

/-- **Hasse–Minkowski over $F$ for $n = 2$** (conditional on squares local–global). -/
@[kb "omeara1963" "§66:1 [unverified]"]
theorem hasseMinkowski_two_nf (I : NFInputs.HMInputs F) (Q : QuadForm F 2) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have ea : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  have key : ∀ (K : Type) [Field K] [Algebra F K],
      Q.IsotropicIn K ↔ IsSquare ((algebraMap F K) (-(a 0 * a 1))) := by
    intro K _ _
    rw [FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso), ea]
    exact FieldGen.isotropic_diag_two_iff K _ _ (ha 0) (ha 1)
  have kF : Q.IsotropicIn F ↔ IsSquare (-(a 0 * a 1)) := by
    rw [key F]; rfl
  rw [kF, I.isSquare_iff_everywhere]
  constructor
  · intro h v
    have := h v
    cases v with
    | infinite w => exact (key _).2 this
    | finite w => exact (key _).2 this
  · intro h v
    have := h v
    cases v with
    | infinite w => exact (key _).1 this
    | finite w => exact (key _).1 this

/-- **Hasse–Minkowski over $F$ for $n = 3$** (conditional on the Hasse norm theorem). -/
@[kb "omeara1963" "§66:1 [unverified]"]
theorem hasseMinkowski_three_nf (I : NFInputs.HMInputs F) (Q : QuadForm F 3) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have ea : a = ![a 0, a 1, a 2] := by ext i; fin_cases i <;> rfl
  constructor
  · intro h v
    cases v <;> exact FieldGen.isotropicIn_of_base _ _ h
  · intro h
    rw [FieldGen.isotropicIn_iff_of_isometricIn F (FieldGen.isometricIn_of_base F hiso), ea,
      FieldGen.isotropic_diag_three_iff F _ _ _ (ha 0) (ha 1) (ha 2)]
    have h1 : -a 1 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.2 (ha 1)) (ha 0)
    have h2 : -a 2 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.2 (ha 2)) (ha 0)
    have := I.hasse_norm _ _ h1 h2 ?_
    · simpa using this
    intro v
    have hv := h v
    cases v with
    | infinite w =>
      simp only [NFPlace.atPlace] at hv
      rw [FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hiso), ea,
        FieldGen.isotropic_diag_three_iff _ _ _ _ (ha 0) (ha 1) (ha 2)] at hv
      exact hv
    | finite w =>
      simp only [NFPlace.atPlace] at hv
      rw [FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hiso), ea,
        FieldGen.isotropic_diag_three_iff _ _ _ _ (ha 0) (ha 1) (ha 2)] at hv
      exact hv

/-- **Hasse–Minkowski over $F$ for diagonal quaternary forms**
$\langle a_1, a_2, -a_3, -a_4 \rangle$, $a_i \in F^\times$ (conditional on reciprocity, prescribed
symbols, the Hasse norm theorem, and local multiplicativity). -/
@[kb "serre1973" "Ch. IV §3.2 (n = 4) [unverified]"]
theorem hasseMinkowski_diag_four_nf (I : NFInputs.HMInputs F) (a₁ a₂ a₃ a₄ : F) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0)
    (h₃ : a₃ ≠ 0) (h₄ : a₄ ≠ 0) :
    (QuadForm.diag ![a₁, a₂, -a₃, -a₄]).IsotropicIn F ↔
      NFPlace.Everywhere (F := F) fun K _ _ => (QuadForm.diag ![a₁, a₂, -a₃, -a₄]).IsotropicIn K := by
  have transfer : ∀ (K L : Type) [Field K] [Field L] (e : K ≃+* L) (a b : K),
      hilbertSymbol K a b = hilbertSymbol L (e a) (e b) := by
    intro K L _ _ e a b
    unfold hilbertSymbol
    have : (∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) ↔
        (∃ x y z : L, (x, y, z) ≠ 0 ∧ z ^ 2 = e a * x ^ 2 + e b * y ^ 2) := by
      constructor
      · rintro ⟨x, y, z, hne, h⟩
        refine ⟨e x, e y, e z, ?_, ?_⟩
        · intro h0
          apply hne
          simp only [Prod.mk_eq_zero, map_eq_zero_iff _ e.injective] at h0 ⊢
          exact h0
        · rw [← map_pow, h]; simp
      · rintro ⟨x, y, z, hne, h⟩
        refine ⟨e.symm x, e.symm y, e.symm z, ?_, ?_⟩
        · intro h0
          apply hne
          simp only [Prod.mk_eq_zero, map_eq_zero_iff _ e.symm.injective] at h0 ⊢
          exact h0
        · apply e.injective
          simp [h]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (this.mp h1) h2
    · exact absurd (this.mpr h2) h1
    · rfl
  have cplx : ∀ a b : ℂ, hilbertSymbol ℂ a b = 1 := by
    intro a b
    unfold hilbertSymbol
    rw [if_pos]
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a (n := 2) (by norm_num)
    exact ⟨1, 0, z, by simp, by simp [hz]⟩
  have pm : ∀ (K : Type) [Field K] (a b : K), hilbertSymbol K a b = 1 ∨ hilbertSymbol K a b = -1 := by
    intro K _ a b
    unfold hilbertSymbol
    split_ifs <;> simp
  have infmul : ∀ (w : InfinitePlace F) (a a' b : w.Completion), a ≠ 0 → a' ≠ 0 → b ≠ 0 →
      hilbertSymbol w.Completion (a * a') b =
        hilbertSymbol w.Completion a b * hilbertSymbol w.Completion a' b := by
    intro w a a' b ha ha' hb
    rcases w.isReal_or_isComplex with hw | hw
    · set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      rw [transfer _ _ e, transfer _ _ e a, transfer _ _ e a', map_mul]
      exact HilbertLocal.hilbertSymbol_real_mul_left _ _ _ (by simpa using ha)
        (by simpa using ha') (by simpa using hb)
    · set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      rw [transfer _ _ e, transfer _ _ e a, transfer _ _ e a', cplx, cplx, cplx]
      norm_num
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
  have placeKey : ∀ (v : NFPlace F) (a b x : F), a ≠ 0 → b ≠ 0 → x ≠ 0 →
      v.hilbert (a / x) (b / x) = v.hilbert a b * v.hilbert x (-(a * b)) := by
    intro v a b x ha hb hx
    cases v with
    | infinite w =>
      simp only [NFPlace.hilbert, map_div₀, map_mul, map_neg]
      exact key _ (infmul w) _ _ _ ((map_ne_zero _).mpr ha) ((map_ne_zero _).mpr hb) ((map_ne_zero _).mpr hx)
    | finite v =>
      simp only [NFPlace.hilbert, map_div₀, map_mul, map_neg]
      exact key _ (I.mul_left_finite v) _ _ _ ((map_ne_zero _).mpr ha) ((map_ne_zero _).mpr hb) ((map_ne_zero _).mpr hx)
  have placeComm : ∀ (v : NFPlace F) (a b : F), v.hilbert a b = v.hilbert b a := by
    intro v a b
    cases v <;> exact hilbertSymbol_comm _ _ _
  have placePm : ∀ (v : NFPlace F) (a b : F), v.hilbert a b = 1 ∨ v.hilbert a b = -1 := by
    intro v a b
    cases v <;> exact pm _ _ _
  have binrep : ∀ a b x : F, a ≠ 0 → b ≠ 0 → x ≠ 0 →
      (∀ v : NFPlace F, v.hilbert (-(a * b)) x = v.hilbert a b) → ∃ X Y : F, a * X ^ 2 + b * Y ^ 2 = x := by
    intro a b x ha hb hx h
    rw [HM4.binary_represents_iff F a b x ha hb hx]
    apply I.hasse_norm _ _ (div_ne_zero ha hx) (div_ne_zero hb hx)
    intro v
    rw [placeKey v a b x ha hb hx, placeComm v x, h v]
    rcases placePm v a b with h' | h' <;> rw [h'] <;> norm_num
  constructor
  · intro h v
    cases v <;> exact FieldGen.isotropicIn_of_base _ _ h
  · intro h
    obtain ⟨x, hx, hxv⟩ := I.prescribed_hilbert (ι := Fin 2) ![-(a₁ * a₂), -(a₃ * a₄)]
      (by intro i; fin_cases i <;> simp [h₁, h₂, h₃, h₄])
      ![fun v => v.hilbert a₁ a₂, fun v => v.hilbert a₃ a₄]
      (by intro i v; fin_cases i <;> exact placePm _ _ _)
      (((I.reciprocity a₁ a₂ h₁ h₂).1.union (I.reciprocity a₃ a₄ h₃ h₄).1).subset (by
        rintro v ⟨i, hi⟩
        fin_cases i
        · left; simpa using hi
        · right; simpa using hi))
      (by
        intro i
        fin_cases i
        · simpa using (I.reciprocity a₁ a₂ h₁ h₂).2
        · simpa using (I.reciprocity a₃ a₄ h₃ h₄).2)
      (by
        intro v
        cases v with
        | infinite w =>
          obtain ⟨y, hy, e1, e2⟩ := FieldGen.exists_common_value w.Completion a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄
            (h (.infinite w))
          refine ⟨y, hy, ?_⟩
          intro i
          fin_cases i
          · simp only [NFPlace.hilbert]
            rw [hilbertSymbol_comm]
            simpa using e1
          · simp only [NFPlace.hilbert]
            rw [hilbertSymbol_comm]
            simpa using e2
        | finite w =>
          obtain ⟨y, hy, e1, e2⟩ := FieldGen.exists_common_value
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w) a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄
            (h (.finite w))
          refine ⟨y, hy, ?_⟩
          intro i
          fin_cases i
          · simp only [NFPlace.hilbert]
            rw [hilbertSymbol_comm]
            simpa using e1
          · simp only [NFPlace.hilbert]
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

/-- **Hasse–Minkowski over $F$ for $n = 4$** (conditional, as for the diagonal case). -/
@[kb "omeara1963" "§66:1 [unverified]"]
theorem hasseMinkowski_four_nf (I : NFInputs.HMInputs F) (Q : QuadForm F 4) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have hd : QuadForm.diag a = QuadForm.diag ![a 0, a 1, -(-a 2), -(-a 3)] := by
    congr 1
    funext i
    fin_cases i <;> simp
  have hT : ∀ (K : Type) [Field K] [Algebra F K],
      Q.IsotropicIn K ↔ (QuadForm.diag ![a 0, a 1, -(-a 2), -(-a 3)]).IsotropicIn K := by
    intro K _ _
    rw [← hd]
    exact FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso)
  rw [hT F]
  rw [hasseMinkowski_diag_four_nf I (a 0) (a 1) (-a 2) (-a 3) (ha 0) (ha 1) (neg_ne_zero.mpr (ha 2))
    (neg_ne_zero.mpr (ha 3))]
  constructor
  · intro h v
    cases v with
    | infinite w => exact (hT _).2 (h (.infinite w))
    | finite w => exact (hT _).2 (h (.finite w))
  · intro h v
    cases v with
    | infinite w => exact (hT _).1 (h (.infinite w))
    | finite w => exact (hT _).1 (h (.finite w))

/-- **Hasse–Minkowski over $F$ for $n \ge 5$**, by induction on $n$ from $n = 4$ (Lam VI,
Thm. 3.1). -/
@[kb "lam2005" "Ch. VI, Thm. 3.1 [unverified]"]
theorem hasseMinkowski_five_le_nf (I : NFInputs.HMInputs F) (Q : QuadForm F n) (hn : 5 ≤ n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  have nd : ∀ k (a : Fin k → F), (∀ i, a i ≠ 0) → (QuadForm.diag a).Nondegenerate := by
    intro k a ha
    unfold QuadForm.Nondegenerate QuadForm.hessian QuadForm.diag
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    have := ha i
    simp only [ne_eq, add_self_eq_zero]
    exact this
  have main : ∀ k, 4 ≤ k → ∀ a : Fin k → F, (∀ i, a i ≠ 0) →
      NFPlace.Everywhere (F := F) (fun K _ _ => (QuadForm.diag a).IsotropicIn K) →
      (QuadForm.diag a).IsotropicIn F := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro a ha h; exact (hasseMinkowski_four_nf I _ (nd 4 a ha)).2 h
    | succ k hk ih =>
      intro a ha h
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k-1, by omega⟩
      classical
      let S : Finset (NFPlace F) := (Finset.univ.image NFPlace.infinite) ∪
        (NFLocal.finite_bad_places_nf (m+2) a ha).toFinset.image NFPlace.finite
      obtain ⟨t, ht, hrep, hS⟩ := NFLocal.exists_global_split_nf S m (by omega) a ha (fun v _ => h v)
      apply FieldGen.isotropic_of_split m a t ht hrep
      apply ih (Fin.cons t fun i => a (i.addNat 2))
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa using ht
        · intro j; simpa using ha _
      · intro v
        by_cases hv : v ∈ S
        · exact hS v hv
        · cases v with
          | infinite w =>
            exfalso; apply hv
            simp [S]
          | finite w =>
            have hw : ¬ (2 ∈ w.asIdeal ∨ ∃ i, (IsDedekindDomain.HeightOneSpectrum.valuation F w) (a i) ≠ 1) := by
              intro hc; apply hv
              simp only [S, Finset.mem_union, Finset.mem_image]
              right
              exact ⟨w, by simpa using hc, rfl⟩
            push_neg at hw
            simp only [NFPlace.atPlace]
            apply FieldGen.isotropicIn_diag_cons_of
            apply NFLocal.isotropic_diag_units_nf w hw.1 m (by omega)
            intro i
            exact hw.2 _
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have hT : ∀ (K : Type) [Field K] [Algebra F K],
      Q.IsotropicIn K ↔ (QuadForm.diag a).IsotropicIn K := by
    intro K _ _
    exact FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso)
  constructor
  · intro h v
    cases v <;> exact FieldGen.isotropicIn_of_base _ _ h
  · intro h
    rw [hT F]
    apply main n (by omega) a ha
    intro v
    cases v with
    | infinite w => exact (hT _).1 (h (.infinite w))
    | finite w => exact (hT _).1 (h (.finite w))

end HMNF

/-- **Hasse–Minkowski over $F$, from the inputs:** given `I : HMInputs F` (the five input theorems as
one hypothesis), a nondegenerate quadratic form over $F$ is isotropic over $F$ iff it is isotropic
over every completion $F_v$. Assembled from `HMNF.hasseMinkowski_two_nf`, `…_three_nf`,
`…_four_nf` and `…_five_le_nf` ($n \le 1$ is direct). -/
@[kb "omeara1963" "§66:1 [unverified]"]
theorem hasseMinkowski_nf_of_inputs (I : NFInputs.HMInputs F) (Q : QuadForm F n)
    (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  match n, Q, hQ with
  | 2, Q, hQ => exact HMNF.hasseMinkowski_two_nf I Q hQ
  | 3, Q, hQ => exact HMNF.hasseMinkowski_three_nf I Q hQ
  | 4, Q, hQ => exact HMNF.hasseMinkowski_four_nf I Q hQ
  | k+5, Q, hQ => exact HMNF.hasseMinkowski_five_le_nf I Q (by omega) hQ
  | 0, Q, hQ =>
    have hno : ∀ (K : Type) [Field K] [Algebra F K], ¬ Q.IsotropicIn K := by
      intro K _ _ h
      obtain ⟨x, hx, _⟩ := h
      exact hx (Subsingleton.elim _ _)
    constructor
    · intro h; exact absurd h (hno F)
    · intro h
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
      exact absurd (h (.infinite w)) (hno _)
  | 1, Q, hQ =>
    obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
    have hno : ∀ (K : Type) [Field K] [Algebra F K], ¬ Q.IsotropicIn K := by
      intro K _ _ h
      rw [FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso)] at h
      obtain ⟨x, hx, hx0⟩ := h
      apply hx
      funext i
      fin_cases i
      have := ha 0
      simp [QuadForm.evalIn, QuadForm.diag] at hx0
      simpa [this] using hx0
    constructor
    · intro h; exact absurd h (hno F)
    · intro h
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
      exact absurd (h (.infinite w)) (hno _)

/-! ### Lam's route: everything from the cases $n = 2, 3$

Lam, Ch. VI, Thm. 3.1. The only inputs are `NFInputs.LamInputs`: squares local–global and the Hasse
norm theorem, for every number field. For $n = 4$ with non-square discriminant $d$, pass to
$L = F(\sqrt d)$, where the discriminant becomes a square, and come back down with
`FieldGen.isotropic_four_of_quadExt`. -/

namespace Lam

/-- **$n = 2$ from squares local–global** (the proof of `HMNF.hasseMinkowski_two_nf` uses only the
field `isSquare_iff_everywhere` of the inputs). -/
@[kb "lam2005" "Ch. VI, Thm. 3.1 [unverified]"]
theorem hasseMinkowski_two
    (hsq : ∀ a : F, IsSquare a ↔ NFPlace.Everywhere (F := F) fun K _ _ => IsSquare (algebraMap F K a))
    (Q : QuadForm F 2) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have ea : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  have key : ∀ (K : Type) [Field K] [Algebra F K],
      Q.IsotropicIn K ↔ IsSquare ((algebraMap F K) (-(a 0 * a 1))) := by
    intro K _ _
    rw [FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso), ea]
    exact FieldGen.isotropic_diag_two_iff K _ _ (ha 0) (ha 1)
  have kF : Q.IsotropicIn F ↔ IsSquare (-(a 0 * a 1)) := by
    rw [key F]; rfl
  rw [kF, hsq]
  constructor
  · intro h v
    have := h v
    cases v with
    | infinite w => exact (key _).2 this
    | finite w => exact (key _).2 this
  · intro h v
    have := h v
    cases v with
    | infinite w => exact (key _).1 this
    | finite w => exact (key _).1 this

/-- **$n = 3$ from the Hasse norm theorem** (the proof of `HMNF.hasseMinkowski_three_nf` uses only
the field `hasse_norm` of the inputs). -/
@[kb "lam2005" "Ch. VI, Thm. 3.1 [unverified]"]
theorem hasseMinkowski_three
    (hnorm : ∀ a b : F, a ≠ 0 → b ≠ 0 → (∀ v : NFPlace F, v.hilbert a b = 1) →
      hilbertSymbol F a b = 1)
    (Q : QuadForm F 3) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have ea : a = ![a 0, a 1, a 2] := by ext i; fin_cases i <;> rfl
  constructor
  · intro h v
    cases v <;> exact FieldGen.isotropicIn_of_base _ _ h
  · intro h
    rw [FieldGen.isotropicIn_iff_of_isometricIn F (FieldGen.isometricIn_of_base F hiso), ea,
      FieldGen.isotropic_diag_three_iff F _ _ _ (ha 0) (ha 1) (ha 2)]
    have h1 : -a 1 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.2 (ha 1)) (ha 0)
    have h2 : -a 2 / a 0 ≠ 0 := div_ne_zero (neg_ne_zero.2 (ha 2)) (ha 0)
    have := hnorm _ _ h1 h2 ?_
    · simpa using this
    intro v
    have hv := h v
    cases v with
    | infinite w =>
      simp only [NFPlace.atPlace] at hv
      rw [FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hiso), ea,
        FieldGen.isotropic_diag_three_iff _ _ _ _ (ha 0) (ha 1) (ha 2)] at hv
      exact hv
    | finite w =>
      simp only [NFPlace.atPlace] at hv
      rw [FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hiso), ea,
        FieldGen.isotropic_diag_three_iff _ _ _ _ (ha 0) (ha 1) (ha 2)] at hv
      exact hv

/-- **The quadratic extension $F(\sqrt d)$ is a number field:** for $d \in F$ not a square there is a
number field $L \supseteq F$ with an element $s$, $s^2 = d$, such that every element of $L$ is
$b_0 + b_1 s$ with $b_0, b_1 \in F$. *Proof:* $L$ = `AdjoinRoot (X ^ 2 - C d)`, a field because
$X^2 - d$ is irreducible (degree 2, no root), finite over $F$ hence over $\mathbb{Q}$, of characteristic
$0$; $s$ = `AdjoinRoot.root`; spanning from the power basis (`AdjoinRoot.powerBasis'`). -/
@[kb "lam2005" "Ch. VI §3 [unverified]"]
theorem exists_quadExt (d : F) (hd : ¬ IsSquare d) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L) (s : L),
      s ^ 2 = algebraMap F L d ∧ ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s := by
  classical
  have hmon : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F).Monic := by
    apply Polynomial.monic_X_pow_sub_C; norm_num
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F).natDegree = 2 := by
    rw [Polynomial.natDegree_X_pow_sub_C]
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; norm_num
    · intro x hx
      apply hd
      simp [Polynomial.IsRoot, sub_eq_zero] at hx
      exact ⟨x, by rw [← hx]; ring⟩
  haveI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F)) := ⟨hirr⟩
  let L := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F)
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  let pb := AdjoinRoot.powerBasis' hmon
  haveI : FiniteDimensional F L := pb.finite
  haveI : FiniteDimensional ℚ L := Module.Finite.trans F L
  refine ⟨L, inferInstance, ⟨⟩, inferInstance, AdjoinRoot.root _, ?_, ?_⟩
  · have := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F)
    simp at this
    rw [sub_eq_zero] at this
    exact this
  · intro y
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    have h1 : AdjoinRoot.mk (Polynomial.X ^ 2 - Polynomial.C d) p
        = AdjoinRoot.mk (Polynomial.X ^ 2 - Polynomial.C d) (p %ₘ (Polynomial.X ^ 2 - Polynomial.C d)) := by
      rw [AdjoinRoot.mk_eq_mk]
      exact ⟨p /ₘ (Polynomial.X ^ 2 - Polynomial.C d), by
        linear_combination (-1 : Polynomial F) *
          Polynomial.modByMonic_add_div p (Polynomial.X ^ 2 - Polynomial.C d)⟩
    have hlt : (p %ₘ (Polynomial.X ^ 2 - Polynomial.C d)).degree ≤ 1 := by
      have := Polynomial.degree_modByMonic_lt p hmon
      rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg] at this
      exact Order.le_of_lt_succ this
    rw [h1, Polynomial.eq_X_add_C_of_degree_le_one hlt]
    refine ⟨(p %ₘ (Polynomial.X ^ 2 - Polynomial.C d)).coeff 0,
      (p %ₘ (Polynomial.X ^ 2 - Polynomial.C d)).coeff 1, ?_⟩
    simp [AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    simp only [L, AdjoinRoot.algebraMap_eq]
    ring

/-- **Local isotropy goes up a finite extension:** let $L \supseteq F$ be number fields. If $Q$ is
isotropic over every completion $F_v$, then $Q$ (viewed over $L$) is isotropic over every
completion $L_w$.

*Proof.* Each place $w$ of $L$ lies over a place $v$ of $F$, and the inclusion $F \to L$ extends to a
ring map $F_v \to L_w$ compatible with $F \to L$: for infinite places, `InfinitePlace.comap` and
`NumberField.LiesOver.completionMap` (scoped instances in
`Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances`); for finite places, the prime
$\mathfrak{P}$ of $\mathcal{O}_L$ lies over $\mathfrak{p} = \mathfrak{P} \cap \mathcal{O}_F$ and the completions
are related as in the `LiesOver` section of `Mathlib.NumberTheory.NumberField.Completion.FinitePlace`
(alternatively: $F \to L \to L_{\mathfrak{P}}$ is uniformly continuous for the $\mathfrak{p}$-adic uniformity,
`valuation_liesOver`, so it extends to $F_{\mathfrak{p}}$). Push an isotropic vector along that map. -/
@[kb "lam2005" "Ch. VI §3 [unverified]"]
theorem isotropic_everywhere_map {L : Type} [Field L] [NumberField L] [Algebra F L]
    (Q : QuadForm F n) (h : NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K) :
    NFPlace.Everywhere (F := L) fun K _ _ => (Q.map (algebraMap F L)).IsotropicIn K := by
  have transfer : ∀ (K K' : Type) [Field K] [Field K'] [Algebra F K] [Algebra L K'] (φ : K →+* K'),
        (∀ c : F, φ (algebraMap F K c) = algebraMap L K' (algebraMap F L c)) →
        Q.IsotropicIn K → (Q.map (algebraMap F L)).IsotropicIn K' := by
    intro K K' _ _ _ _ φ hφ ⟨x, hx, h0⟩
    refine ⟨fun i => φ (x i), ?_, ?_⟩
    · intro h; apply hx; funext i
      have := congrFun h i
      simpa using this
    · have := congrArg φ h0
      simp only [QuadForm.evalIn, map_sum, map_zero] at this
      simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply]
      refine Eq.trans ?_ this
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp [hφ]
  intro u
  cases u with
  | infinite w =>
    let v : InfinitePlace F := w.comap (algebraMap F L)
    have hlo : w.LiesOver v := by
      constructor
      ext x
      simp [AbsoluteValue.under]
      rfl
    have hv := h (.infinite v)
    simp only [NFPlace.atPlace] at hv ⊢
    refine transfer _ _ (@NumberField.LiesOver.completionMap F L _ _ _ v w hlo) ?_ hv
    intro c
    letI := @NumberField.LiesOver.instAlgebraCompletion F L _ _ _ v w hlo
    haveI := @NumberField.LiesOver.instIsScalarTowerCompletion F L _ _ _ v w hlo
    change algebraMap v.Completion w.Completion (algebraMap F v.Completion c) = _
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  | finite w =>
    let v := IsDedekindDomain.HeightOneSpectrum.under (𝓞 F) w
    have : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]⟩
    have hu := IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F L v w
    let g : WithVal (IsDedekindDomain.HeightOneSpectrum.valuation F v) →+*
        (IsDedekindDomain.HeightOneSpectrum.valuation L w).Completion :=
      (UniformSpace.Completion.coeRingHom).comp (algebraMap _ _)
    have hc : Continuous g := ((UniformSpace.Completion.uniformContinuous_coe _).comp hu).continuous
    have hv := h (.finite v)
    simp only [NFPlace.atPlace] at hv ⊢
    refine transfer _ _ ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
      ((UniformSpace.Completion.extensionHom g hc).comp
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv F v).toRingHom)) ?_ hv
    intro c
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
      IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, RingHom.comp_apply]
    apply (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).injective
    simp
    rw [UniformSpace.Completion.extensionHom_coe]
    rfl

/-- **$n = 4$, diagonal** (Lam VI, Thm. 3.1). Let $a_0, \dots, a_3 \in F^\times$ and
$d = a_0 a_1 a_2 a_3$.

*Proof.* If $d$ is a square, scale by $a_0$: the form is similar to $\langle 1, x, y, xy \rangle$ with
$x = a_1/a_0$, $y = a_2/a_0$ (since $a_3/a_0 \equiv xy$ modulo squares), which is isotropic iff
$\langle 1, x, y \rangle$ is (`FieldGen.isotropic_pfister_iff`, over $F$ and over each $F_v$); apply
$n = 3$. If $d$ is not a square, let $L = F(\sqrt d)$ (`exists_quadExt`). The form is isotropic at every
place of $L$ (`isotropic_everywhere_map`) and has square discriminant over $L$, so by the first case
over $L$ (with `I` for $L$) it is isotropic over $L$; then it is isotropic over $F$ by
`FieldGen.isotropic_four_of_quadExt`. -/
@[kb "lam2005" "Ch. VI, Thm. 3.1 [unverified]"]
theorem hasseMinkowski_diag_four (I : NFInputs.LamInputs) (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0) :
    (QuadForm.diag a).IsotropicIn F ↔
      NFPlace.Everywhere (F := F) fun K _ _ => (QuadForm.diag a).IsotropicIn K := by
  have evalD : ∀ {n : ℕ} (L K : Type) [Field L] [Field K] [Algebra L K] (b : Fin n → L) (x : Fin n → K), QuadForm.evalIn K (QuadForm.diag b) x = ∑ i, algebraMap L K (b i) * x i ^ 2 := by
    intro n L K _ _ _ b x
    simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have scale : ∀ {n : ℕ} (L K : Type) [Field L] [Field K] [Algebra L K] (b b' : Fin n → L) (c : L) (e : Fin n → L), c ≠ 0 → (∀ i, e i ≠ 0) → (∀ i, b' i = c * b i * e i ^ 2) → QuadForm.IsotropicIn K (QuadForm.diag b') → QuadForm.IsotropicIn K (QuadForm.diag b) := by
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
  have scale' : ∀ {n : ℕ} (L K : Type) [Field L] [Field K] [Algebra L K] (b b' : Fin n → L) (c : L) (e : Fin n → L), c ≠ 0 → (∀ i, e i ≠ 0) → (∀ i, b' i = c * b i * e i ^ 2) → (QuadForm.IsotropicIn K (QuadForm.diag b) ↔ QuadForm.IsotropicIn K (QuadForm.diag b')) := by
    intro n L K _ _ _ b b' c e hc he hb
    refine ⟨scale L K b' b c⁻¹ (fun i => (e i)⁻¹) (inv_ne_zero hc) (fun i => inv_ne_zero (he i)) ?_, scale L K b b' c e hc he hb⟩
    intro i
    rw [hb i]; field_simp [he i]
  have nd : ∀ (L : Type) [Field L] [CharZero L] k (a : Fin k → L), (∀ i, a i ≠ 0) → (QuadForm.diag a).Nondegenerate := by
    intro L _ _ k a ha
    unfold QuadForm.Nondegenerate QuadForm.hessian QuadForm.diag
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    have := ha i
    simp only [ne_eq, add_self_eq_zero]
    exact this
  have sqcase : ∀ (L : Type) [Field L] [NumberField L] (b : Fin 4 → L), (∀ i, b i ≠ 0) →
      IsSquare (b 0 * b 1 * b 2 * b 3) →
      NFPlace.Everywhere (F := L) (fun K _ _ => QuadForm.IsotropicIn K (QuadForm.diag b)) →
      QuadForm.IsotropicIn L (QuadForm.diag b) := by
    intro L _ _ b hb hsq h
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
    have key : ∀ (K : Type) [Field K] [Algebra L K], QuadForm.IsotropicIn K (QuadForm.diag b) ↔
        QuadForm.IsotropicIn K (QuadForm.diag ![1, b 1 / b 0, b 2 / b 0]) := by
      intro K _ _
      rw [scale' L K b ![1, b 1 / b 0, b 2 / b 0, b 1 / b 0 * (b 2 / b 0)] (b 0)⁻¹ ![1, 1, 1, b 1 * b 2 / s]
        (inv_ne_zero h0) ?_ ?_]
      · exact FieldGen.isotropic_pfister_iff K _ _ hx hy
      · intro i; fin_cases i <;> simp [h1, h2, hs0]
      · intro i; fin_cases i
        · simp [h0]
        · simp; field_simp
        · simp; field_simp
        · simp
          rw [div_pow, sq s, ← hs]
          field_simp
    rw [key L]
    rw [Lam.hasseMinkowski_three (I.hasse_norm L) _ (nd L 3 _ (by intro i; fin_cases i <;> simp [hx, hy]))]
    intro v
    have := h v
    cases v with
    | infinite w => exact (key _).1 this
    | finite w => exact (key _).1 this
  constructor
  · intro h v
    cases v <;> exact FieldGen.isotropicIn_of_base _ _ h
  intro h
  by_cases hd : IsSquare (a 0 * a 1 * a 2 * a 3)
  · exact sqcase F a ha hd h
  obtain ⟨L, _, _, _, s, hs, hspan⟩ := Lam.exists_quadExt _ hd
  have hL := Lam.isotropic_everywhere_map (L := L) (QuadForm.diag a) h
  have hmap : (QuadForm.diag a).map (algebraMap F L) = QuadForm.diag (fun i => algebraMap F L (a i)) := by
    unfold QuadForm.map QuadForm.diag
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [hmap] at hL
  have hiso := sqcase L _ (fun i => by simpa using ha i)
    ⟨s, by simp only [← map_mul]; rw [← hs, sq]⟩ hL
  apply FieldGen.isotropic_four_of_quadExt L a ha hd s hs hspan
  obtain ⟨x, hx, h0⟩ := hiso
  exact ⟨x, hx, by rw [evalD] at h0 ⊢; simpa using h0⟩

/-- **$n = 4$** for an arbitrary nondegenerate form, by diagonalisation (as in
`HMNF.hasseMinkowski_four_nf`). -/
@[kb "lam2005" "Ch. VI, Thm. 3.1 [unverified]"]
theorem hasseMinkowski_four (I : NFInputs.LamInputs) (Q : QuadForm F 4) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have hT : ∀ (K : Type) [Field K] [Algebra F K],
      Q.IsotropicIn K ↔ (QuadForm.diag a).IsotropicIn K := by
    intro K _ _
    exact FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso)
  rw [hT F, Lam.hasseMinkowski_diag_four I a ha]
  constructor
  · intro h v
    cases v with
    | infinite w => exact (hT _).2 (h (.infinite w))
    | finite w => exact (hT _).2 (h (.finite w))
  · intro h v
    cases v with
    | infinite w => exact (hT _).1 (h (.infinite w))
    | finite w => exact (hT _).1 (h (.finite w))

/-- **$n \ge 5$**, by induction from $n = 4$ exactly as in `HMNF.hasseMinkowski_five_le_nf`
(splitting and weak approximation), with `Lam.hasseMinkowski_four` as the base case. -/
@[kb "lam2005" "Ch. VI, Thm. 3.1 [unverified]"]
theorem hasseMinkowski_five_le (I : NFInputs.LamInputs) (Q : QuadForm F n) (hn : 5 ≤ n)
    (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  have nd : ∀ k (a : Fin k → F), (∀ i, a i ≠ 0) → (QuadForm.diag a).Nondegenerate := by
    intro k a ha
    unfold QuadForm.Nondegenerate QuadForm.hessian QuadForm.diag
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    have := ha i
    simp only [ne_eq, add_self_eq_zero]
    exact this
  have main : ∀ k, 4 ≤ k → ∀ a : Fin k → F, (∀ i, a i ≠ 0) →
      NFPlace.Everywhere (F := F) (fun K _ _ => (QuadForm.diag a).IsotropicIn K) →
      (QuadForm.diag a).IsotropicIn F := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro a ha h; exact (Lam.hasseMinkowski_four I _ (nd 4 a ha)).2 h
    | succ k hk ih =>
      intro a ha h
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k-1, by omega⟩
      classical
      let S : Finset (NFPlace F) := (Finset.univ.image NFPlace.infinite) ∪
        (NFLocal.finite_bad_places_nf (m+2) a ha).toFinset.image NFPlace.finite
      obtain ⟨t, ht, hrep, hS⟩ := NFLocal.exists_global_split_nf S m (by omega) a ha (fun v _ => h v)
      apply FieldGen.isotropic_of_split m a t ht hrep
      apply ih (Fin.cons t fun i => a (i.addNat 2))
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa using ht
        · intro j; simpa using ha _
      · intro v
        by_cases hv : v ∈ S
        · exact hS v hv
        · cases v with
          | infinite w =>
            exfalso; apply hv
            simp [S]
          | finite w =>
            have hw : ¬ (2 ∈ w.asIdeal ∨ ∃ i, (IsDedekindDomain.HeightOneSpectrum.valuation F w) (a i) ≠ 1) := by
              intro hc; apply hv
              simp only [S, Finset.mem_union, Finset.mem_image]
              right
              exact ⟨w, by simpa using hc, rfl⟩
            push_neg at hw
            simp only [NFPlace.atPlace]
            apply FieldGen.isotropicIn_diag_cons_of
            apply NFLocal.isotropic_diag_units_nf w hw.1 m (by omega)
            intro i
            exact hw.2 _
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  have hT : ∀ (K : Type) [Field K] [Algebra F K],
      Q.IsotropicIn K ↔ (QuadForm.diag a).IsotropicIn K := by
    intro K _ _
    exact FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso)
  constructor
  · intro h v
    cases v <;> exact FieldGen.isotropicIn_of_base _ _ h
  · intro h
    rw [hT F]
    apply main n (by omega) a ha
    intro v
    cases v with
    | infinite w => exact (hT _).1 (h (.infinite w))
    | finite w => exact (hT _).1 (h (.finite w))

end Lam

/-- **Hasse–Minkowski over $F$ from Lam's two inputs:** given `I : LamInputs` (squares local–global
and the Hasse norm theorem, for all number fields), a nondegenerate quadratic form over $F$ is
isotropic over $F$ iff it is isotropic over every completion $F_v$. Assembled from `Lam.hasseMinkowski_two`,
`…_three`, `…_four`, `…_five_le` ($n \le 1$ is direct, as in `hasseMinkowski_nf_of_inputs`). -/
@[kb "lam2005" "Ch. VI, Thm. 3.1 [unverified]"]
theorem hasseMinkowski_nf_of_lamInputs (I : NFInputs.LamInputs) (Q : QuadForm F n)
    (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  match n, Q, hQ with
  | 2, Q, hQ => exact Lam.hasseMinkowski_two (I.isSquare_iff_everywhere F) Q hQ
  | 3, Q, hQ => exact Lam.hasseMinkowski_three (I.hasse_norm F) Q hQ
  | 4, Q, hQ => exact Lam.hasseMinkowski_four I Q hQ
  | k+5, Q, hQ => exact Lam.hasseMinkowski_five_le I Q (by omega) hQ
  | 0, Q, hQ =>
    have hno : ∀ (K : Type) [Field K] [Algebra F K], ¬ Q.IsotropicIn K := by
      intro K _ _ h
      obtain ⟨x, hx, _⟩ := h
      exact hx (Subsingleton.elim _ _)
    constructor
    · intro h; exact absurd h (hno F)
    · intro h
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
      exact absurd (h (.infinite w)) (hno _)
  | 1, Q, hQ =>
    obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
    have hno : ∀ (K : Type) [Field K] [Algebra F K], ¬ Q.IsotropicIn K := by
      intro K _ _ h
      rw [FieldGen.isotropicIn_iff_of_isometricIn K (FieldGen.isometricIn_of_base K hiso)] at h
      obtain ⟨x, hx, hx0⟩ := h
      apply hx
      funext i
      fin_cases i
      have := ha 0
      simp [QuadForm.evalIn, QuadForm.diag] at hx0
      simpa [this] using hx0
    constructor
    · intro h; exact absurd h (hno F)
    · intro h
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
      exact absurd (h (.infinite w)) (hno _)

end QuadFormsKB
