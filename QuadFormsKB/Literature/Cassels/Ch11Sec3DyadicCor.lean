/-
# Cassels, Chapter 11, §3: Lemma 3.8, Corollary (the $2$-adic determinant bound)

**Layer:** as in `Ch11Sec3Dyadic.lean`: $\Lambda_2 = L_v$ at the prime $v \mid 2$ of $\mathcal O_{\mathbb Q}$, bases
$\gamma$ with `loc v L.1 = locAct v γ (std v)`, Gram matrices `locGram Q v γ` of $B = 2\phi$.

**Proves** Cassels' Lemma 3.8, Corollary (pp. 214–215): if $\phi$ takes $2$-adic integral values on $\Lambda_2$ and
$U_2 \not\subseteq \theta(\Lambda_2)$, then the form induced on $\Lambda_2$ is classically integral
($\phi(x, y) = \tfrac12B(x,y) \in \mathbb Z_2$ for $x, y \in \Lambda_2$, `classicallyIntegral_of_not_units_mem_two`)
and its determinant $d = \det(\phi(b_k, b_l)) = 2^{-n}\det G$ is divisible by $2^T$ with
$T = \tfrac12n(n-3) + [\tfrac12(n+1)]$ (`valued_det_le_of_not_units_mem_two`, stated for $\det G = 2^nd$).
*Proof* (Cassels): by the $2$-adic Jordan decomposition (Ch. 8, Lemma 4.1) $\Lambda_2$ is an orthogonal sum of
$1$-dimensional lattices and binary lattices of type (i) of Lemma 3.8; the latter cannot occur, so the basis can be
taken orthogonal; the valuations $m_k = v_2(\phi(b_k))$, sorted, satisfy $m_{k+2} \ge m_k + 2$ by Lemma 3.8 (ii), so
$\sum_k m_k \ge 0 + 0 + 2 + 2 + 4 + \cdots = T$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3Dyadic

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- **Cassels' exponent** $T(n) = \tfrac12n(n-3) + [\tfrac12(n+1)]$ of Theorem 1.3 (ii) and Lemma 3.8, Corollary
(Ch. 11, pp. 202, 214); $T = 0, 0, 2, 4, 8, 12, 18, \dots$ for $n = 1, 2, 3, \dots$ (and $T(0) = 0$). -/
def casselsExpTwo (n : ℕ) : ℤ := (n * ((n : ℤ) - 3)) / 2 + ((n : ℤ) + 1) / 2

variable {n : ℕ} (Q : QuadForm ℚ n) {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ


local notation "𝔬" => v.adicCompletionIntegers ℚ

/-! ### Combinatorics of the valuations -/

section Comb

/-- $\sum_{k<c}2\lfloor k/2\rfloor$, the integer value of `casselsExpTwo`. -/
def casselsSum (c : ℕ) : ℕ := ∑ k ∈ Finset.range c, 2 * (k / 2)

theorem casselsSum_succ (c : ℕ) : casselsSum (c + 1) = casselsSum c + 2 * (c / 2) :=
  Finset.sum_range_succ _ _

theorem casselsSum_closed (q : ℕ) :
    (casselsSum (2 * q) : ℤ) = 2 * q * (q - 1) ∧ (casselsSum (2 * q + 1) : ℤ) = 2 * q ^ 2 := by
  induction q with
  | zero => simp [casselsSum]
  | succ q ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : casselsSum (2 * (q + 1)) = casselsSum (2 * q + 1) + 2 * q := by
      rw [show 2 * (q + 1) = (2 * q + 1) + 1 by ring, casselsSum_succ]
      congr 2
      omega
    have e2 : casselsSum (2 * (q + 1) + 1) = casselsSum (2 * (q + 1)) + 2 * (q + 1) := by
      rw [casselsSum_succ]
      congr 2
      omega
    have h3 : (casselsSum (2 * (q + 1)) : ℤ) = 2 * ((q + 1 : ℕ) : ℤ) * (((q + 1 : ℕ) : ℤ) - 1) := by
      rw [e1]; push_cast; rw [h2]; ring
    refine ⟨h3, ?_⟩
    rw [e2]; push_cast at h3 ⊢; rw [h3]; ring

theorem casselsExpTwo_eq (n : ℕ) : casselsExpTwo n = (casselsSum n : ℤ) := by
  obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [(casselsSum_closed q).1]
    unfold casselsExpTwo
    push_cast
    have e1 : (2 * (q : ℤ)) * (2 * q - 3) = 2 * (q * (2 * q - 3)) := by ring
    rw [e1, Int.mul_ediv_cancel_left _ (by norm_num), show (2 * (q : ℤ) + 1) / 2 = q by omega]
    ring
  · rw [(casselsSum_closed q).2]
    unfold casselsExpTwo
    push_cast
    have e1 : (2 * (q : ℤ) + 1) * (2 * q + 1 - 3) = 2 * ((2 * q + 1) * (q - 1)) := by ring
    rw [e1, Int.mul_ediv_cancel_left _ (by norm_num), show (2 * (q : ℤ) + 1 + 1) / 2 = q + 1 by omega]
    ring

variable {m : ℕ}

theorem window_card_le (f : Fin m → ℕ)
    (hf : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → f i = f j → f k ≠ f i ∧ f k ≠ f i + 1 ∧ f i ≠ f k + 1)
    (s : Finset (Fin m)) (a : ℕ) : (s.filter (fun k => f k = a ∨ f k = a + 1)).card ≤ 2 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp h
  simp only [Finset.mem_filter] at hi hj hk
  have h1 := hf i j k hij hik hjk
  have h2 := hf i k j hik hij hjk.symm
  have h3 := hf j k i hjk hij.symm hik.symm
  omega

theorem count_lt_le (f : Fin m → ℕ)
    (hf : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → f i = f j → f k ≠ f i ∧ f k ≠ f i + 1 ∧ f i ≠ f k + 1)
    (s : Finset (Fin m)) (q : ℕ) : (s.filter (fun k => f k < 2 * q)).card ≤ 2 * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsub : s.filter (fun k => f k < 2 * (q + 1)) ⊆
        s.filter (fun k => f k < 2 * q) ∪ s.filter (fun k => f k = 2 * q ∨ f k = 2 * q + 1) := by
      intro k hk
      simp only [Finset.mem_union, Finset.mem_filter] at hk ⊢
      obtain ⟨hks, hk⟩ := hk
      by_cases h : f k < 2 * q
      · exact Or.inl ⟨hks, h⟩
      · exact Or.inr ⟨hks, by omega⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 2 * q + 2 := add_le_add ih (window_card_le f hf s _)
      _ = _ := by ring

theorem sum_ge_casselsSum (f : Fin m → ℕ)
    (hf : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → f i = f j → f k ≠ f i ∧ f k ≠ f i + 1 ∧ f i ≠ f k + 1) :
    ∀ (c : ℕ) (s : Finset (Fin m)), s.card = c → casselsSum c ≤ ∑ k ∈ s, f k := by
  intro c
  induction c with
  | zero => intro s hs; simp [casselsSum]
  | succ c ih =>
    intro s hs
    have hne : s.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image s f hne
    have hcard : (s.erase k0).card = c := by rw [Finset.card_erase_of_mem hk0]; omega
    have h1 := ih (s.erase k0) hcard
    rw [← Finset.add_sum_erase s f hk0, casselsSum_succ]
    have h2 := count_lt_le f hf s (f k0 / 2 + 1)
    rw [Finset.filter_true_of_mem (fun k hk => by have := hmax k hk; omega)] at h2
    omega

end Comb

section Dyadic

variable (v)

/-- At the prime above $2$ of $\mathbb Q$: $\lvert 2\rvert = \lvert\varpi\rvert = e^{-1}$. -/
theorem valued_two_dyadic (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : Valued.v (2 : Fv) = exp (-1 : ℤ) := by
  have hπ := LocalDensity.NF.irreducible_π v
  have h1 : LocalDensity.NF.π v ∣ 2 := by
    have := (LocalDensity.NF.π_pow_dvd_two_iff v 1).mpr (by simpa using h2)
    simpa using this
  have h2' : ¬ LocalDensity.NF.π v ^ 2 ∣ 2 := fun h =>
    Tamagawa.Indefinite.two_not_mem_sq h2 ((LocalDensity.NF.π_pow_dvd_two_iff v 2).mp h)
  obtain ⟨t, ht⟩ := h1
  have htu : IsUnit t := LocalDensity.DVR.dvr_isUnit_of_not_dvd hπ
    (fun ⟨s, hs⟩ => h2' ⟨s, by rw [ht, hs]; ring⟩)
  have ht1 := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp htu
  have h := congrArg (fun z : 𝔬 => (z : Fv)) ht
  have h' : (2 : Fv) = ((LocalDensity.NF.π v : 𝔬) : Fv) * (t : Fv) := h
  rw [h', map_mul, LocalDensity.NF.valued_π, ht1, mul_one]

theorem valued_alg_pi_mul (ν : ℕ) (b : 𝔬) :
    Valued.v (algebraMap 𝔬 Fv (LocalDensity.NF.π v ^ ν * b)) = exp (-(ν : ℤ)) * Valued.v (b : Fv) := by
  have : algebraMap 𝔬 Fv (LocalDensity.NF.π v ^ ν * b) = ((LocalDensity.NF.π v : 𝔬) : Fv) ^ ν * (b : Fv) := by
    rw [map_mul, map_pow]; rfl
  rw [this, map_mul, map_pow, LocalDensity.NF.valued_π, ← WithZero.exp_nsmul,
    show ν • (-1 : ℤ) = -(ν : ℤ) by simp]

theorem valued_alg_two_pi_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (ν : ℕ) (b : 𝔬) :
    Valued.v (algebraMap 𝔬 Fv (2 * LocalDensity.NF.π v ^ ν * b)) =
      exp (-1) * exp (-(ν : ℤ)) * Valued.v (b : Fv) := by
  have : algebraMap 𝔬 Fv (2 * LocalDensity.NF.π v ^ ν * b) =
      2 * algebraMap 𝔬 Fv (LocalDensity.NF.π v ^ ν * b) := by
    rw [mul_assoc, map_mul]; rfl
  rw [this, map_mul, valued_two_dyadic v h2, valued_alg_pi_mul, mul_assoc]

end Dyadic

/-- A symmetric matrix with even diagonal is $c + c^t$ (take $c$ upper triangular). -/
theorem exists_add_transpose_eq {R : Type*} [CommRing R] {m : ℕ} (G : Matrix (Fin m) (Fin m) R)
    (hs : Gᵀ = G) (q : Fin m → R) (hd : ∀ k, G k k = 2 * q k) : ∃ c : Matrix (Fin m) (Fin m) R, c + cᵀ = G := by
  refine ⟨Matrix.of fun k l => if k < l then G k l else if k = l then q k else 0, ?_⟩
  ext k l
  rcases lt_trichotomy k l with h | rfl | h
  · simp [h, not_lt.mpr h.le, h.ne']
  · simp [hd]; ring
  · have := congrFun (congrFun hs k) l
    simp only [Matrix.transpose_apply] at this
    simp [h, not_lt.mpr h.le, h.ne', this]

section Basis

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {Q : QuadForm F n} {v : HeightOneSpectrum (𝓞 F)}

local notation "Fw" => v.adicCompletion F
local notation "𝔬w" => v.adicCompletionIntegers F

variable (v) in
theorem valued_alg_pi_mul' (ν : ℕ) (b : 𝔬w) :
    Valued.v (algebraMap 𝔬w Fw (LocalDensity.NF.π v ^ ν * b)) = exp (-(ν : ℤ)) * Valued.v (b : Fw) := by
  have : algebraMap 𝔬w Fw (LocalDensity.NF.π v ^ ν * b) = ((LocalDensity.NF.π v : 𝔬w) : Fw) ^ ν * (b : Fw) := by
    rw [map_mul, map_pow]; rfl
  rw [this, map_mul, map_pow, LocalDensity.NF.valued_π, ← WithZero.exp_nsmul,
    show ν • (-1 : ℤ) = -(ν : ℤ) by simp]

variable (v) in
theorem valued_alg_two_pi_mul' (h2v : Valued.v (2 : Fw) = exp (-1 : ℤ)) (ν : ℕ) (b : 𝔬w) :
    Valued.v (algebraMap 𝔬w Fw (2 * LocalDensity.NF.π v ^ ν * b)) =
      exp (-1) * exp (-(ν : ℤ)) * Valued.v (b : Fw) := by
  have : algebraMap 𝔬w Fw (2 * LocalDensity.NF.π v ^ ν * b) =
      2 * algebraMap 𝔬w Fw (LocalDensity.NF.π v ^ ν * b) := by
    rw [mul_assoc, map_mul]; rfl
  rw [this, map_mul, h2v, valued_alg_pi_mul', mul_assoc]

set_option maxHeartbeats 1600000 in
/-- **A $2$-adic Jordan basis of an integral local lattice** ($v \mid 2$ over $\mathbb Q$): there is a basis $\gamma'$
of $L_v$ with the same $\lvert\det\rvert$ whose Gram matrix is block diagonal, with $2 \times 2$ blocks on the pairs
`e ∈ P` (disjoint; $G_{e_1e_2} \ne 0$, $\lvert G_{e_1e_1}\rvert, \lvert G_{e_2e_2}\rvert \le \lvert 2G_{e_1e_2}\rvert$)
and $1 \times 1$ blocks elsewhere ($\lvert G_{kk}\rvert = e^{-1-\nu_k}$). (`dvr_jinv_complete_aux`.) -/
theorem exists_dyadic_basis (hQ : Q.Nondegenerate) (h2v : Valued.v (2 : Fw) = exp (-1 : ℤ))
    (h2' : ¬ LocalDensity.NF.π v ^ 2 ∣ 2) (L : Lat F n)
    (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v))
    (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fw x) ≤ 1) :
    ∃ (γ' : GL (Fin n) Fw) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      loc v L.1 = locAct v γ' (std v) ∧
      Valued.v (locGram Q v γ').det = Valued.v (locGram Q v γ).det ∧
      (∀ k l, k ≠ l → (k, l) ∉ P → (l, k) ∉ P → locGram Q v γ' k l = 0) ∧
      (∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
      (∀ e ∈ P, e.1 ≠ e.2 ∧ locGram Q v γ' e.1 e.2 ≠ 0 ∧
        Valued.v (locGram Q v γ' e.1 e.1) ≤ Valued.v (2 * locGram Q v γ' e.1 e.2) ∧
        Valued.v (locGram Q v γ' e.2 e.2) ≤ Valued.v (2 * locGram Q v γ' e.1 e.2)) ∧
      (∀ k, ¬ LocalDensity.IsPaired P k → Valued.v (locGram Q v γ' k k) = exp (-1 - (ν k : ℤ))) := by
  have hmemb : ∀ k : Fin n, γ.val *ᵥ (Pi.single k 1 : Fin n → Fw) ∈ loc v L.1 := fun k => by
    rw [hγ, mem_locAct]; exact ⟨_, single_mem_std k (by simp), rfl⟩
  have hle : ∀ k l, Valued.v (locGram Q v γ k l) ≤ 1 := fun k l => by
    have h1 : ∀ z ∈ loc v L.1, Valued.v (Q.evalIn Fw z) ≤ 1 := hint
    have := qbil_le_one_of_int (Q := Q) (v := v) (M := loc v L.1) h1 (hmemb k) (hmemb l)
    rwa [locGram_apply_eq] at this
  have hQle : ∀ k, Valued.v (Q.evalIn Fw (γ.val *ᵥ (Pi.single k 1 : Fin n → Fw))) ≤ 1 :=
    fun k => hint _ (hmemb k)
  let G₀ : Matrix (Fin n) (Fin n) 𝔬w := Matrix.of fun k l => toO v _ (hle k l)
  have hG₀ : G₀.map (algebraMap 𝔬w Fw) = locGram Q v γ := by ext k l; rfl
  have hinj : Function.Injective (algebraMap 𝔬w Fw) := fun a b h => Subtype.ext h
  have hsymm : G₀ᵀ = G₀ := by
    refine Matrix.map_injective hinj ?_
    show G₀ᵀ.map (algebraMap 𝔬w Fw) = G₀.map (algebraMap 𝔬w Fw)
    rw [Matrix.transpose_map, hG₀, locGram_transpose]
  have hdiag : ∀ k, G₀ k k = 2 * toO v _ (hQle k) := fun k => by
    apply hinj
    show locGram Q v γ k k = 2 * Q.evalIn Fw (γ.val *ᵥ (Pi.single k 1 : Fin n → Fw))
    rw [two_mul_evalIn_eq, locGram_apply_eq]
  obtain ⟨c, hcc⟩ := exists_add_transpose_eq G₀ hsymm _ hdiag
  have hdet0 : (c + cᵀ).det ≠ 0 := by
    rw [hcc]
    intro h
    apply locGram_det_ne_zero hQ γ
    rw [← hG₀, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  have hπ := LocalDensity.NF.irreducible_π v
  have hJ0 : LocalDensity.DVR.DvrJInv (LocalDensity.NF.π v) (c + cᵀ) ∅ ∅ (fun _ => 0) := by
    refine ⟨by simp, by simp, by simp, ?_, by simp, by simp⟩
    intro i j _ h
    simp at h
  obtain ⟨V, P', ν', hV, hJ⟩ := LocalDensity.DVR.dvr_jinv_complete_aux hπ h2' _ c ∅ ∅ (fun _ => 0) rfl hdet0 hJ0
  rw [hcc] at hJ
  let Pg : GL (Fin n) 𝔬w := Matrix.nonsingInvUnit V hV
  let P : GL (Fin n) Fw := GeneralLinearGroup.map (algebraMap 𝔬w Fw) Pg
  have hPval : P.val = V.map (algebraMap 𝔬w Fw) := rfl
  have H1 : locGram Q v (γ * P) = (Vᵀ * G₀ * V).map (algebraMap 𝔬w Fw) := by
    rw [locGram_mul, hPval, ← hG₀]
    simp [Matrix.map_mul, Matrix.transpose_map]
  refine ⟨γ * P, P', ν', ?_, ?_, ?_, hJ.2.2.1, ?_, ?_⟩
  · rw [locAct_mul, locAct_map_std v Pg, ← hγ]
  · rw [locGram_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_mul, map_mul]
    have : Valued.v (P.val.det) = 1 := by
      rw [hPval, show (V.map (algebraMap 𝔬w Fw)).det = algebraMap 𝔬w Fw V.det from
        (RingHom.map_det (algebraMap 𝔬w Fw) V).symm]
      exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hV
    rw [this]
    simp
  · intro k l hkl hkP hlP
    rw [H1, Matrix.map_apply]
    have := hJ.2.2.2.1 k l hkl (Or.inl (Finset.mem_univ _)) hkP hlP
    rw [this, map_zero]
  · intro e he
    obtain ⟨hlt, -⟩ := hJ.2.1 e he
    obtain ⟨hν, ⟨b, hb, hbu⟩, ⟨a1, ha1⟩, ⟨a2, ha2⟩⟩ := hJ.2.2.2.2.1 e he
    have hb1 := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hbu
    have ha1le : Valued.v (a1 : Fw) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp a1.2
    have ha2le : Valued.v (a2 : Fw) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp a2.2
    have g12 : locGram Q v (γ * P) e.1 e.2 = algebraMap 𝔬w Fw (LocalDensity.NF.π v ^ ν' e.1 * b) := by
      rw [H1, Matrix.map_apply, hb]
    have g11 : locGram Q v (γ * P) e.1 e.1 = algebraMap 𝔬w Fw (2 * LocalDensity.NF.π v ^ ν' e.1 * a1) := by
      rw [H1, Matrix.map_apply, ha1]
    have g22 : locGram Q v (γ * P) e.2 e.2 = algebraMap 𝔬w Fw (2 * LocalDensity.NF.π v ^ ν' e.1 * a2) := by
      rw [H1, Matrix.map_apply, ha2]
    have v12 : Valued.v (2 * locGram Q v (γ * P) e.1 e.2) = exp (-1) * exp (-(ν' e.1 : ℤ)) := by
      rw [g12, map_mul, h2v, valued_alg_pi_mul', hb1, mul_one]
    refine ⟨hlt.ne, ?_, ?_, ?_⟩
    · intro h0
      have : Valued.v (2 * locGram Q v (γ * P) e.1 e.2) = 0 := by rw [h0, mul_zero, map_zero]
      rw [v12] at this
      exact absurd this (by simp)
    · rw [v12, g11, valued_alg_two_pi_mul' v h2v]
      calc _ ≤ exp (-1) * exp (-(ν' e.1 : ℤ)) * 1 := mul_le_mul' le_rfl ha1le
        _ = _ := mul_one _
    · rw [v12, g22, valued_alg_two_pi_mul' v h2v]
      calc _ ≤ exp (-1) * exp (-(ν' e.1 : ℤ)) * 1 := mul_le_mul' le_rfl ha2le
        _ = _ := mul_one _
  · intro k hk
    obtain ⟨u, hu, hunit⟩ := hJ.2.2.2.2.2 k (Finset.mem_univ _) hk
    have hu1 := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hunit
    rw [H1, Matrix.map_apply, hu, valued_alg_two_pi_mul' v h2v, hu1, mul_one, ← exp_add]
    congr 1

/-- On an orthogonal basis of $L_v$ with $\lvert G_{kk}\rvert \le r$: $\lvert B(x, y)\rvert \le r$ on $L_v$. -/
theorem qbil_le_of_diag (L : Lat F n) (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v))
    (horth : ∀ k l, k ≠ l → locGram Q v γ k l = 0) {r : WithZero (Multiplicative ℤ)}
    (hr : ∀ k, Valued.v (locGram Q v γ k k) ≤ r) :
    ∀ x ∈ loc v L.1, ∀ y ∈ loc v L.1, Valued.v (qbil Q Fw x y) ≤ r := by
  intro x hx y hy
  rw [hγ, mem_locAct] at hx hy
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨d, hd, rfl⟩ := hy
  rw [mem_std_iff] at hc hd
  rw [qbil_mulVec_locGram, dotProduct]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [locGram_mulVec_diag horth, map_mul, map_mul]
  calc Valued.v (c k) * (Valued.v (locGram Q v γ k k) * Valued.v (d k)) ≤ 1 * (r * 1) :=
        mul_le_mul' (hc k) (mul_le_mul' (hr k) (hd k))
    _ = r := by rw [one_mul, mul_one]

end Basis

/-- Every lattice over $\mathbb Q$ has a basis, so $L_v = \gamma\mathfrak o_v^n$ for some $\gamma$. -/
theorem exists_loc_basis_rat (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) := by
  obtain ⟨γ, hγ⟩ := HilbertModular.exists_latOf_of_isPrincipalIdealRing L
  exact ⟨_, by rw [hγ, latOf, loc_glImage, loc_intVec]⟩

/-- **The $2$-adic Jordan basis is orthogonal** under the hypotheses of Lemma 3.8, Corollary: a binary block would
give $U_2 \subseteq \theta(\Lambda_2)$ by Lemma 3.8 (i). The diagonal entries are $\lvert G_{kk}\rvert = e^{-1-\nu_k}$. -/
theorem exists_diag_basis_two (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (L : Lat ℚ n) (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (hnot : ¬ ∀ u : Fvˣ, Valued.v (u : Fv) = 1 → u ∈ localSpinorNormGroup Q hQ v L)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) :
    ∃ (γ' : GL (Fin n) Fv) (ν : Fin n → ℕ), loc v L.1 = locAct v γ' (std v) ∧
      Valued.v (locGram Q v γ').det = Valued.v (locGram Q v γ).det ∧
      (∀ k l, k ≠ l → locGram Q v γ' k l = 0) ∧
      (∀ k, Valued.v (locGram Q v γ' k k) = exp (-1 - (ν k : ℤ))) := by
  have h2' : ¬ LocalDensity.NF.π v ^ 2 ∣ 2 := fun h =>
    Tamagawa.Indefinite.two_not_mem_sq h2 ((LocalDensity.NF.π_pow_dvd_two_iff v 2).mp h)
  obtain ⟨γ', P, ν, hγ', hdet, hzero, hdisj, hpair, hsing⟩ :=
    exists_dyadic_basis hQ (valued_two_dyadic v h2) h2' L γ hγ (by convert hint; exact Subsingleton.elim _ _)
  have hP : P = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨e, he⟩
    obtain ⟨hne, h0, hi, hj⟩ := hpair e he
    have key : ∀ m, m ≠ e.1 → m ≠ e.2 → ∀ l, (l = e.1 ∨ l = e.2) → (m, l) ∉ P ∧ (l, m) ∉ P := by
      intro m hm1 hm2 l hl
      constructor
      · intro hm
        by_cases hee : (m, l) = e
        · exact hm1 (Prod.ext_iff.mp hee).1
        · obtain ⟨-, -, h3, h4⟩ := hdisj _ hm e he hee
          rcases hl with hl | hl
          · exact h3 hl
          · exact h4 hl
      · intro hm
        by_cases hee : (l, m) = e
        · exact hm2 (Prod.ext_iff.mp hee).2
        · obtain ⟨h1, h2, -, -⟩ := hdisj _ hm e he hee
          rcases hl with hl | hl
          · exact h1 hl
          · exact h2 hl
    apply hnot
    intro u hu
    refine units_mem_localSpinorNormGroup_two_binary Q hQ h2 L γ' hγ' hne (fun m hm1 hm2 => ?_) h0 hi hj u hu
    obtain ⟨k1, k2⟩ := key m hm1 hm2 e.1 (Or.inl rfl)
    obtain ⟨k3, k4⟩ := key m hm1 hm2 e.2 (Or.inr rfl)
    exact ⟨hzero m e.1 hm1 k1 k2, hzero m e.2 hm2 k3 k4⟩
  subst hP
  exact ⟨γ', ν, hγ', hdet, fun k l hkl => hzero k l hkl (by simp) (by simp),
    fun k => hsing k (by simp [LocalDensity.IsPaired])⟩

/-- **Cassels, Lemma 3.8, Corollary** (Ch. 11, p. 214), first assertion: *suppose that $\phi$ takes $2$-adic
integral values on $\Lambda_2$ and that $U_2 \not\subseteq \theta(\Lambda_2)$. Then the quadratic form induced on
$\Lambda_2$ is $2$-adically integral in the classical sense*: $\lvert B(x, y)\rvert \le \lvert 2\rvert$ for all
$x, y \in \Lambda_2$. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.8, Cor., pp. 214–215 (classically integral)"]
theorem classicallyIntegral_of_not_units_mem_two (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (L : Lat ℚ n) (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (hnot : ¬ ∀ u : Fvˣ, Valued.v (u : Fv) = 1 → u ∈ localSpinorNormGroup Q hQ v L) :
    ∀ x ∈ loc v L.1, ∀ y ∈ loc v L.1, Valued.v (qbil Q Fv x y) ≤ Valued.v (2 : Fv) := by
  obtain ⟨γ, hγ⟩ := exists_loc_basis_rat L v
  obtain ⟨γ', ν, hγ', -, horth, hval⟩ := exists_diag_basis_two Q hQ h2 L hint hnot γ hγ
  have key := qbil_le_of_diag L γ' hγ' horth (r := Valued.v (2 : Fv)) fun k => by
    rw [hval, valued_two_dyadic v h2, exp_le_exp]; omega
  intro x hx y hy
  convert key x hx y hy using 3
  exact Subsingleton.elim _ _

/-- **Cassels, Lemma 3.8, Corollary** (Ch. 11, pp. 214–215), second assertion: *under the same hypotheses the
determinant of the form induced on $\Lambda_2$ is divisible by $2^T$, $T = \tfrac12n(n-3) + [\tfrac12(n+1)]$.* Here for
every basis $\gamma$ of $\Lambda_2$: $\lvert\det G\rvert \le 2^{-(T+n)}$, since $\det G = 2^nd$. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.8, Cor., pp. 214–215 (2^T divides the determinant)"]
theorem valued_det_le_of_not_units_mem_two (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (L : Lat ℚ n) (hint : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn Fv x) ≤ 1)
    (hnot : ¬ ∀ u : Fvˣ, Valued.v (u : Fv) = 1 → u ∈ localSpinorNormGroup Q hQ v L)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) :
    Valued.v (locGram Q v γ).det ≤ exp (-(casselsExpTwo n + n)) := by
  obtain ⟨γ', ν, hγ', hdet, horth, hval⟩ := exists_diag_basis_two Q hQ h2 L hint hnot γ hγ
  rw [← hdet]
  have hf : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ν i = ν j →
      ν k ≠ ν i ∧ ν k ≠ ν i + 1 ∧ ν i ≠ ν k + 1 := by
    intro i j k hij hik hjk hji
    have horth' : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ' l m = 0 :=
      fun l m hlm _ => horth l m hlm
    have h2v := valued_two_dyadic v h2
    by_contra hcon
    apply hnot
    intro u hu
    refine units_mem_localSpinorNormGroup_two_ternary Q hQ h2 L γ' hγ' hij hik hjk horth'
      (by rw [hval, hval, hji]) ?_ u hu
    rw [map_mul, map_mul, h2v, hval, hval, ← exp_add, ← exp_add]
    by_cases h1 : ν k = ν i
    · exact Or.inl (by rw [h1])
    by_cases h3 : ν k = ν i + 1
    · exact Or.inr (Or.inl (by rw [h3]; congr 1; push_cast; ring))
    have h4 : ν i = ν k + 1 := by tauto
    exact Or.inr (Or.inr (by rw [h4]; congr 1; push_cast; ring))
  have hG : locGram Q v γ' = Matrix.diagonal (fun k => locGram Q v γ' k k) := by
    ext k l
    by_cases h : k = l
    · subst h; simp
    · rw [horth k l h, Matrix.diagonal_apply_ne _ h]
  rw [hG, Matrix.det_diagonal, map_prod]
  simp only [hval]
  rw [prod_exp, exp_le_exp]
  have h1 := sum_ge_casselsSum ν hf n Finset.univ (by simp)
  rw [casselsExpTwo_eq]
  have h3 : (∑ k, (-1 - (ν k : ℤ))) = -(n : ℤ) - ((∑ k, ν k : ℕ) : ℤ) := by
    simp [Finset.sum_sub_distrib]
  rw [h3]
  have : (casselsSum n : ℤ) ≤ ((∑ k, ν k : ℕ) : ℤ) := by exact_mod_cast h1
  omega

end QuadFormsKB.Lattices
