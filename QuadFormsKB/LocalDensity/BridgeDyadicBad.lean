/-
# Checks of the dyadic $\mathfrak p \mid N$ formulas: $\mathbb{Z}_2$ ($e = f = 1$) and a ramified prime ($e = 2$)

**Layer:** bridge between the ℚ layer at $p = 2$ and the dyadic results of `DyadicClosed.lean` and `DyadicBad.lean`,
at $R = \mathbb{Z}_2$; plus an abstract ramified check ($e = 2$, $f = 1$, e.g. $\mathbb{Z}_2[\sqrt 2]$). Every count is
evaluated by kernel `decide` on $(\mathbb{Z}/2^K)^n$ (no `native_decide`).

* **$n = 1$, $\mathbb{Z}_2$** (`localDensity_sq_two`): $\beta_2(x^2; m) = 4, 0, 0, 8$ for $m = 1, 2, 3, 4$ — the closed form
  $2q^{e + a/2}$ of `DVR.localDensity_unary` ($m = 1, 2, 4$) and an enumeration mod $8$ ($m = 3$), which also confirms
  $r_8(1) = 4 = 2q^e$.
* **$n = 3$, $\mathbb{Z}_2$** (`localDensity_sumThreeSq_two`): $\beta_2(x^2 + y^2 + z^2; m) = 3/2, 3/2, 1, 3/2, 0$ for
  $m = 1, 2, 3, 5, 7$, by `DVR.localDensity_unit_diag` (level $2e + 1 = 3$) and, for $m = 2$, `DVR.localDensity_eq_level_J`
  (level $a + 2e + 1 = 4$).
* **$n = 4$, $\mathbb{Z}_2$: `Siegel.localDensity_Q4_two_nat` recovered** (`localDensity_Q4_two_nat_dyadic`): for
  $I_4 = x_0^2 + \dots + x_3^2$, $\beta_2(m) = 1$ for $m$ odd and $3/2^\nu$ otherwise, from the recursion
  $\beta_2(m) = \beta^*_8(m) + \tfrac14\beta_2(m/4)$ (`DVR.localDensity_eq_prim_add_zero_J`, level $K = 3$) and the primitive
  counts mod $8$ ($512, 768, 256, 0$). Same statement as the Siegel-layer theorem, proved independently of it.
* **Ramified, $e = 2$, $f = 1$** (`localDensity_sq_ramified`): for any DVR with $q = 2$ and $\mathrm{ord}_\pi 2 = 2$,
  $\beta_\pi(x^2; 1) = 8$, $\beta_\pi(x^2; \pi^2) = 16$, $\beta_\pi(x^2; 1 + \pi) = 0$. Over $\mathbb{Z}_2$ ($e = 1$) the first
  value is $4$: the dyadic densities depend on $e$, not only on $q$, and on unit classes mod $\pi^{2e+1}$, not mod $\pi$.

**Depends on** `BridgeDyadic.lean`, `BridgeExplicit.lean`, `DyadicBad.lean`.
-/
import QuadFormsKB.LocalDensity.BridgeDyadic
import QuadFormsKB.LocalDensity.BridgeExplicit
import QuadFormsKB.LocalDensity.DyadicBad
import QuadFormsKB.Literature.AWS.FourSquares

namespace QuadFormsKB.LocalDensity

open QuadForm

/-! ### $\mathbb{Z}_2$ basics -/

/-- $\mathrm{ord}_2 2 = 1$ in $\mathbb{Z}_2$. -/
theorem padic_two_ord : (2 : ℤ_[2]) ^ 1 ∣ 2 ∧ ¬ (2 : ℤ_[2]) ^ (1 + 1) ∣ 2 :=
  ⟨by simp, by exact_mod_cast padicInt_not_sq_dvd_two 2⟩

/-- Base change of an integral diagonal form to $\mathbb{Z}_p$. -/
theorem diag_map_padic {n : ℕ} (p : ℕ) [Fact p.Prime] (a : Fin n → ℤ) :
    (QuadForm.diag a).map (Int.castRingHom ℤ_[p]) = QuadForm.diag fun i => (a i : ℤ_[p]) := by
  ext i j
  simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem padic_two_not_dvd_one : ¬ (2 : ℤ_[2]) ∣ 1 := not_two_dvd_one_padic

/-- An odd integer is a unit of $\mathbb{Z}_2$. -/
theorem padic_two_not_dvd_odd {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) : ¬ (2 : ℤ_[2]) ∣ (m : ℤ_[2]) := by
  have := padic_pow_dvd_int_iff 2 1 m
  simp only [pow_one, Nat.cast_ofNat] at this
  rwa [this]

/-! ### $n = 1$ over $\mathbb{Z}_2$ -/

/-- $r_8(x^2; c)$ for $c = 1, 3$: the squares mod $8$ are $0, 1, 4$, and $1$ has the $4$ roots $\pm1, \pm3$. -/
theorem repCount_sq_eight : repCount (QuadForm.diag ![(1 : ℤ)]) 2 3 1 = 4 ∧
    repCount (QuadForm.diag ![(1 : ℤ)]) 2 3 3 = 0 := by
  have h : ∀ c : ℤ, ∀ x : Fin 1 → ZMod (2 ^ 3), (QuadForm.diag ![(1 : ℤ)]).evalIn (ZMod (2 ^ 3)) x =
      (c : ZMod (2 ^ 3)) ↔ x 0 ^ 2 = (c : ZMod 8) := by
    intro c x
    simp [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
    ring_nf
  unfold repCount
  constructor
  · rw [Nat.card_congr (Equiv.subtypeEquivRight (h 1)), Nat.card_eq_fintype_card]; decide
  · rw [Nat.card_congr (Equiv.subtypeEquivRight (h 3)), Nat.card_eq_fintype_card]; decide

/-- **$\beta_2(x^2;\, m)$ for $m = 1, 2, 3, 4$** ($e = f = 1$): $4, 0, 0, 8$. The values $4 = 2q^e$ (an enumeration mod $8$
gives the same $r_8(1) = 4$), $0$ ($\mathrm{ord}_2 m$ odd) and $8 = 2q^{e+1}$ are the closed form `DVR.localDensity_unary`;
$\beta_2(3) = r_8(3) = 0$ by enumeration ($3$ is not a square mod $8$). -/
@[kb "hanke2004" "p. 362 (dyadic case-by-case; p = 2 check, n = 1)"]
theorem localDensity_sq_two :
    localDensity (QuadForm.diag ![(1 : ℤ)]) 2 1 = 4 ∧ localDensity (QuadForm.diag ![(1 : ℤ)]) 2 2 = 0 ∧
      localDensity (QuadForm.diag ![(1 : ℤ)]) 2 3 = 0 ∧ localDensity (QuadForm.diag ![(1 : ℤ)]) 2 4 = 8 := by
  have hd : (QuadForm.diag ![(1 : ℤ)]).map (Int.castRingHom ℤ_[2]) = QuadForm.diag ![(1 : ℤ_[2])] := by
    rw [diag_map_padic]; congr 1; funext i; fin_cases i; simp
  have hπ := padic_two_irreducible
  have hu : ¬ (2 : ℤ_[2]) ∣ 1 := padic_two_not_dvd_one
  have hcl := fun (a : ℕ) (m : ℤ_[2]) (hda : (2 : ℤ_[2]) ^ a ∣ m) (ha : ¬ (2 : ℤ_[2]) ^ (a + 1) ∣ m) =>
    DVR.localDensity_unary (2 : ℤ_[2]) hπ 1 padic_two_ord hu hda ha
  simp only [localDensity_eq_padic, hd, Nat.cast_ofNat]
  have h1 := DVR.dvr_not_pow_succ_dvd hπ isUnit_one (π := (2 : ℤ_[2]))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ((1 : ℤ) : ℤ_[2]) = 2 ^ 0 * 1 by simp, hcl 0 _ (by simp) (h1 0),
      DVR.divPow_pow_mul hπ.ne_zero le_rfl, q_padicInt]
    split_ifs with h
    · norm_num
    · exact absurd ⟨⟨0, rfl⟩, 1, by simp⟩ h
  · rw [show ((2 : ℤ) : ℤ_[2]) = 2 ^ 1 * 1 by simp, hcl 1 _ (by simp) (h1 1)]
    split_ifs with h
    · exact absurd h.1 (by decide)
    · rfl
  · have h := DVR.localDensity_unit_diag ![(1 : ℤ_[2])] 2 hπ (fun i => by fin_cases i; exact hu) 1
      padic_two_ord (m := ((3 : ℤ) : ℤ_[2])) (padic_two_not_dvd_odd (by decide))
    have hr := (repCount_eq_padic (QuadForm.diag ![(1 : ℤ)]) 2 ∅ 3 3).1
    rw [hd] at hr
    simp only [Nat.cast_ofNat] at hr
    rw [h, show 2 * 1 + 1 = 3 by rfl, ← hr, repCount_sq_eight.2]
    simp
  · rw [show ((4 : ℤ) : ℤ_[2]) = 2 ^ 2 * 1 by norm_num, hcl 2 _ (by simp) (h1 2),
      DVR.divPow_pow_mul hπ.ne_zero le_rfl, q_padicInt]
    split_ifs with h
    · norm_num
    · exact absurd ⟨⟨1, rfl⟩, 1, by simp⟩ h

/-! ### $n = 3$ over $\mathbb{Z}_2$: $x^2 + y^2 + z^2$ -/

/-- Coordinates of $\mathbb{Z}/2^k$-vectors of length $3$ as triples (for kernel enumeration). -/
def fin3EquivD (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun x := (x 0, x 1, x 2)
  invFun y := ![y.1, y.2.1, y.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv y := rfl

/-- The number of triples in $(\mathbb{Z}/2^k)^3$ with $y_0^2 + y_1^2 + y_2^2 = c$ (decidable). -/
def card3 (k : ℕ) (c : ℤ) : ℕ :=
  Fintype.card {y : ZMod (2 ^ k) × ZMod (2 ^ k) × ZMod (2 ^ k) //
    y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = (c : ZMod (2 ^ k))}

/-- $r_{2^k}(x^2 + y^2 + z^2;\, c)$ as a count of triples in $\mathbb{Z}/2^k$. -/
theorem repCount_sumThreeSq_eq_card (k : ℕ) (c : ℤ) :
    repCount (QuadForm.diag fun _ : Fin 3 => (1 : ℤ)) 2 k c = card3 k c := by
  unfold repCount card3
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr ((fin3EquivD _).subtypeEquiv fun x => ?_)
  show _ ↔ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = _
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three]
  ring_nf

set_option maxRecDepth 100000 in
/-- Enumerations of $(\mathbb{Z}/8)^3$ and $(\mathbb{Z}/16)^3$: $r_8(c) = 96, 64, 96, 0$ for $c = 1, 3, 5, 7$, and
$r_{16}(2) = 384$, for $x^2 + y^2 + z^2$. -/
theorem card3_values : card3 3 1 = 96 ∧ card3 3 3 = 64 ∧ card3 3 5 = 96 ∧ card3 3 7 = 0 ∧ card3 4 2 = 384 := by
  unfold card3
  decide +kernel

/-- **$\beta_2(x^2 + y^2 + z^2;\, m)$ for $m = 1, 2, 3, 5, 7$** ($e = f = 1$): $3/2, 3/2, 1, 3/2, 0$. Units at level
$2e + 1 = 3$ (`DVR.localDensity_unit_diag`: $r_8(m)/8^2$); $m = 2$ at level $\mathrm{ord}_2 m + 2e + 1 = 4$
(`DVR.localDensity_eq_level_J`: $r_{16}(2)/16^2$). Kernel enumeration. -/
@[kb "hanke2004" "p. 362 (dyadic case-by-case; p = 2 check, n = 3)"]
theorem localDensity_sumThreeSq_two :
    localDensity (QuadForm.diag fun _ : Fin 3 => (1 : ℤ)) 2 1 = 3 / 2 ∧
    localDensity (QuadForm.diag fun _ : Fin 3 => (1 : ℤ)) 2 2 = 3 / 2 ∧
    localDensity (QuadForm.diag fun _ : Fin 3 => (1 : ℤ)) 2 3 = 1 ∧
    localDensity (QuadForm.diag fun _ : Fin 3 => (1 : ℤ)) 2 5 = 3 / 2 ∧
    localDensity (QuadForm.diag fun _ : Fin 3 => (1 : ℤ)) 2 7 = 0 := by
  have hπ := padic_two_irreducible
  set Q := QuadForm.diag fun _ : Fin 3 => (1 : ℤ)
  have hd : Q.map (Int.castRingHom ℤ_[2]) = QuadForm.diag fun _ : Fin 3 => (1 : ℤ_[2]) := by
    rw [diag_map_padic]; simp
  have hu : ∀ i : Fin 3, ¬ (2 : ℤ_[2]) ∣ (fun _ => (1 : ℤ_[2])) i := fun _ => padic_two_not_dvd_one
  have hr : ∀ k (c : ℤ), DVR.repCount (QuadForm.diag fun _ : Fin 3 => (1 : ℤ_[2])) 2 k (c : ℤ_[2]) =
      card3 k c := by
    intro k c
    have := (repCount_eq_padic Q 2 ∅ k c).1
    rw [hd] at this
    simp only [Nat.cast_ofNat] at this
    rw [← this]; exact repCount_sumThreeSq_eq_card k c
  have hunit : ∀ c : ℤ, ¬ (2 : ℤ) ∣ c → localDensity Q 2 c = (card3 3 c : ℝ) / 8 ^ 2 := by
    intro c hc
    rw [localDensity_eq_padic, hd, Nat.cast_ofNat,
      DVR.localDensity_unit_diag _ 2 hπ hu 1 padic_two_ord (padic_two_not_dvd_odd hc), hr, q_padicInt]
    norm_num
  obtain ⟨c1, c3, c5, c7, c2⟩ := card3_values
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := hunit 1 (by decide)
    rw [this, c1]; norm_num
  · have h2 : ¬ (2 : ℤ_[2]) ^ (1 + 1) ∣ ((2 : ℤ) : ℤ_[2]) := by
      simpa using DVR.dvr_not_pow_succ_dvd hπ isUnit_one 1 (π := (2 : ℤ_[2]))
    have h := DVR.localDensity_eq_level_J _ 2 hπ ∅ 0 (DVR.isJordanFormW_diag_unit _ hπ hu) 1 padic_two_ord 0
      (fun _ => le_rfl) h2 4 (by norm_num)
    have e2 : localDensity Q 2 2 = localDensity Q 2 ((2 : ℤ) : ℤ) := rfl
    rw [e2, localDensity_eq_padic, hd, Nat.cast_ofNat, h, hr, q_padicInt, c2]
    norm_num
  · have := hunit 3 (by decide)
    rw [this, c3]; norm_num
  · have := hunit 5 (by decide)
    rw [this, c5]; norm_num
  · have := hunit 7 (by decide)
    rw [this, c7]; norm_num

/-! ### $n = 4$ over $\mathbb{Z}_2$: $\beta_2$ of $x_0^2 + \dots + x_3^2$ recovered from the dyadic recursion -/

/-- Coordinates of vectors of length $4$ as quadruples (for kernel enumeration). -/
def fin4EquivD (α : Type*) : (Fin 4 → α) ≃ α × α × α × α where
  toFun x := (x 0, x 1, x 2, x 3)
  invFun y := ![y.1, y.2.1, y.2.2.1, y.2.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv y := rfl

set_option maxRecDepth 100000 in
/-- Enumeration of $(\mathbb{Z}/8)^4$: the primitive solutions of $x_0^2 + \dots + x_3^2 = c$ number $512$ ($c$ odd),
$768$ ($c \equiv 2 \bmod 4$), $256$ ($c = 4$), $0$ ($c = 0$). -/
theorem card_sumFourSq_prim_zmod8 : ∀ c : ZMod 8,
    (Finset.univ.filter (fun x : ZMod 8 × ZMod 8 × ZMod 8 × ZMod 8 =>
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2.1 ^ 2 + x.2.2.2 ^ 2 = c ∧
        ¬ (x.1.val % 2 = 0 ∧ x.2.1.val % 2 = 0 ∧ x.2.2.1.val % 2 = 0 ∧ x.2.2.2.val % 2 = 0))).card =
      if c.val % 2 = 1 then 512 else if c.val % 4 = 2 then 768 else if c.val = 4 then 256 else 0 := by
  decide +kernel

theorem zmod8_two_dvd_iff' (y : ZMod (2 ^ 3)) : ((2 : ℕ) : ZMod (2 ^ 3)) ∣ y ↔ y.val % 2 = 0 := by
  have h : ∀ y : ZMod 8, (∃ c : ZMod 8, y = 2 * c) ↔ y.val % 2 = 0 := by decide
  exact h y

/-- **Primitive counts of $I_4$ mod $8$**: $r^{*}_8(m) = 512, 768, 256, 0$ for $m$ odd, $\equiv 2 \bmod 4$, $\equiv 4 \bmod 8$,
$\equiv 0 \bmod 8$. -/
theorem repCountOf_nonZero_Q4_eight_dyadic (m : ℤ) :
    repCountOf AWS.Q4 2 3 m (fun x => ¬ IsZeroType 2 3 x) =
      if m % 2 = 1 then 512 else if m % 4 = 2 then 768 else if m % 8 = 4 then 256 else 0 := by
  classical
  unfold repCountOf
  have : ∀ x : Fin 4 → ZMod (2 ^ 3),
      (AWS.Q4.evalIn (ZMod (2 ^ 3)) x = ((m : ℤ) : ZMod (2 ^ 3)) ∧ ¬ IsZeroType 2 3 x) ↔
      ((fin4EquivD _ x).1 ^ 2 + (fin4EquivD _ x).2.1 ^ 2 + (fin4EquivD _ x).2.2.1 ^ 2 +
          (fin4EquivD _ x).2.2.2 ^ 2 = ((m : ℤ) : ZMod (2 ^ 3)) ∧
        ¬ ((fin4EquivD _ x).1.val % 2 = 0 ∧ (fin4EquivD _ x).2.1.val % 2 = 0 ∧
          (fin4EquivD _ x).2.2.1.val % 2 = 0 ∧ (fin4EquivD _ x).2.2.2.val % 2 = 0)) := by
    intro x
    refine and_congr ?_ (not_congr ?_)
    · simp [AWS.Q4, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, sq, fin4EquivD]
    · simp only [IsZeroType, fin4EquivD, ← zmod8_two_dvd_iff']
      constructor
      · intro h; exact ⟨h 0, h 1, h 2, h 3⟩
      · rintro ⟨h0, h1, h2, h3⟩ i; fin_cases i <;> assumption
  rw [Nat.card_congr ((Equiv.subtypeEquivRight this).trans ((fin4EquivD _).subtypeEquiv
      (q := fun y : ZMod (2 ^ 3) × ZMod (2 ^ 3) × ZMod (2 ^ 3) × ZMod (2 ^ 3) =>
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2.1 ^ 2 + y.2.2.2 ^ 2 = ((m : ℤ) : ZMod (2 ^ 3)) ∧
          ¬ (y.1.val % 2 = 0 ∧ y.2.1.val % 2 = 0 ∧ y.2.2.1.val % 2 = 0 ∧ y.2.2.2.val % 2 = 0))
      (fun _ => Iff.rfl))),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine (card_sumFourSq_prim_zmod8 ((m : ℤ) : ZMod 8)).trans ?_
  have h8 : ((((m : ℤ) : ZMod 8)).val : ℤ) = m % 8 := ZMod.val_intCast m
  generalize (((m : ℤ) : ZMod 8)).val = v at h8 ⊢
  split_ifs <;> omega

/-- $I_4$ over $\mathbb{Z}_2$ is $\langle 1, 1, 1, 1\rangle$. -/
theorem Q4_map_two : AWS.Q4.map (Int.castRingHom ℤ_[2]) = QuadForm.diag fun _ : Fin 4 => (1 : ℤ_[2]) := by
  rw [show AWS.Q4 = QuadForm.diag fun _ : Fin 4 => (1 : ℤ) from rfl, diag_map_padic]; simp

/-- **The dyadic recursion for $I_4$ over $\mathbb{Z}_2$** (`DVR.localDensity_eq_prim_add_zero_J`, $L = 0$, $e = 1$,
$K = 3$, $c_4 = 2^4/2^6 = 1/4$): $\beta_2(c) = r^{*}_8(c)/2^9 + [4 \mid c]\,\beta_2(c/4)/4$ for $c \ne 0$. -/
theorem localDensity_Q4_two_step (c : ℤ) (hc : c ≠ 0) :
    localDensity AWS.Q4 2 c = (repCountOf AWS.Q4 2 3 c (fun x => ¬ IsZeroType 2 3 x) : ℝ) / 2 ^ 9 +
      if (4 : ℤ) ∣ c then localDensity AWS.Q4 2 (c / 4) / 4 else 0 := by
  have hπ := padic_two_irreducible
  have hu : ∀ i : Fin 4, ¬ (2 : ℤ_[2]) ∣ (fun _ => (1 : ℤ_[2])) i := fun _ => padic_two_not_dvd_one
  have hJ := DVR.isJordanFormW_diag_unit _ hπ hu
  have hc' : (c : ℤ_[2]) ≠ 0 := by exact_mod_cast hc
  simp only [localDensity_eq_padic, Q4_map_two, Nat.cast_ofNat]
  rw [DVR.localDensity_eq_prim_add_zero_J _ 2 hπ ∅ 0 hJ 1 padic_two_ord 0 (fun _ => le_rfl) hc' 3 le_rfl]
  congr 1
  · unfold DVR.primDensityAt
    rw [repCountOf_nonZero_eq_padic, Q4_map_two, q_padicInt]
    simp only [Nat.cast_ofNat]
  · have hd : (2 : ℤ_[2]) ^ 2 ∣ (c : ℤ_[2]) ↔ (4 : ℤ) ∣ c := by
      have := padic_pow_dvd_int_iff 2 2 c
      simp only [Nat.cast_ofNat] at this
      rw [this]; norm_num
    by_cases h4 : (4 : ℤ) ∣ c
    · rw [if_pos (hd.2 h4), if_pos h4]
      have hdiv : DVR.divPow (2 : ℤ_[2]) 2 (c : ℤ_[2]) = ((c / 4 : ℤ) : ℤ_[2]) := by
        refine DVR.divPow_eq_of_eq_mul hπ.ne_zero ?_
        have : c = 4 * (c / 4) := (Int.mul_ediv_cancel' h4).symm
        conv_lhs => rw [this]
        push_cast; ring
      rw [hdiv, DVR.zeroFactor, q_padicInt]
      norm_num
      ring
    · rw [if_neg (fun h => h4 (hd.1 h)), if_neg h4]

/-- **$\beta_2$ of $I_4$ on $2^a u$, $u$ odd, from the dyadic recursion:** $1$ if $a = 0$, $3/2^a$ if $a \ge 1$. Same values
as `Siegel.localDensity_Q4_two_pow_mul`, proved here only from `DVR.localDensity_eq_prim_add_zero_J` and an
enumeration of the primitive solutions mod $8$. -/
theorem localDensity_Q4_two_pow_mul_dyadic (a : ℕ) (u : ℤ) (hu : Odd u) :
    localDensity AWS.Q4 2 (2 ^ a * u) = if a = 0 then 1 else 3 / 2 ^ a := by
  obtain ⟨w, rfl⟩ := hu
  have hne : ∀ b : ℕ, (2 : ℤ) ^ b * (2 * w + 1) ≠ 0 := fun b =>
    mul_ne_zero (pow_ne_zero _ two_ne_zero) (by omega)
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rw [localDensity_Q4_two_step _ (hne a), repCountOf_nonZero_Q4_eight_dyadic]
    match a with
    | 0 =>
      have h4 : ¬ (4 : ℤ) ∣ 2 ^ 0 * (2 * w + 1) := by omega
      rw [if_neg h4]; norm_num
    | 1 =>
      have h4 : ¬ (4 : ℤ) ∣ 2 ^ 1 * (2 * w + 1) := by omega
      rw [if_neg h4]; norm_num
      split_ifs <;> first | omega | norm_num
    | 2 =>
      have h4 : (4 : ℤ) ∣ 2 ^ 2 * (2 * w + 1) := ⟨2 * w + 1, by ring⟩
      rw [if_pos h4, show (2 : ℤ) ^ 2 * (2 * w + 1) / 4 = 2 ^ 0 * (2 * w + 1) by norm_num, ih 0 (by omega)]
      norm_num
      split_ifs <;> first | omega | norm_num
    | a + 3 =>
      have h4 : (4 : ℤ) ∣ 2 ^ (a + 3) * (2 * w + 1) := ⟨2 ^ (a + 1) * (2 * w + 1), by ring⟩
      rw [if_pos h4, show (2 : ℤ) ^ (a + 3) * (2 * w + 1) / 4 = 2 ^ (a + 1) * (2 * w + 1) by
        rw [show (2 : ℤ) ^ (a + 3) * (2 * w + 1) = 4 * (2 ^ (a + 1) * (2 * w + 1)) by ring]; simp,
        ih (a + 1) (by omega)]
      have h8 : (2 : ℤ) ^ (a + 3) * (2 * w + 1) = 8 * (2 ^ a * (2 * w + 1)) := by ring
      rw [h8]
      generalize (2 : ℤ) ^ a * (2 * w + 1) = c
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [Nat.cast_zero, zero_div, zero_add, Nat.add_eq_zero_iff, and_false,
        OfNat.ofNat_ne_zero, ↓reduceIte]
      rw [pow_succ, pow_succ 2 (a + 2), pow_succ 2 (a + 1)]
      ring

/-- **`Siegel.localDensity_Q4_two_nat` recovered from the dyadic formula**: for $m \ge 1$ with
$\nu = \mathrm{ord}_2 m$, $\beta_2(x_0^2 + \dots + x_3^2;\, m) = 1$ if $\nu = 0$ and $3/2^\nu$ otherwise. The statement is
the Siegel-layer theorem's, proved independently of it (no import of `Siegel/`). -/
@[kb "hanke2011aws" "§2.7.5, Lemma 2.7.6, p. 39 (via the dyadic recursion, Hanke 2004 §3)"]
theorem localDensity_Q4_two_nat_dyadic (m : ℕ) (hm : m ≠ 0) :
    localDensity AWS.Q4 2 m =
      if m.factorization 2 = 0 then 1 else 3 / 2 ^ m.factorization 2 := by
  have hodd : Odd (m / 2 ^ m.factorization 2) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hm))
  have e : (m : ℤ) = 2 ^ m.factorization 2 * ((m / 2 ^ m.factorization 2 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self m 2).symm
  rw [e, localDensity_Q4_two_pow_mul_dyadic _ _ (by exact_mod_cast hodd)]

/-! ### A ramified dyadic prime: $e = 2$, $f = 1$ (e.g. $\mathbb{Z}_2[\sqrt 2]$, $\pi = \sqrt 2$) -/

section Ramified

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (IsLocalRing.ResidueField R)]

/-- If the residue field has $2$ elements, every unit is $\equiv 1 \pmod \pi$. -/
theorem DVR.dvd_sub_one_of_q_eq_two (hq : DVR.q R = 2) {π : R} (hπ : Irreducible π) {y : R} (hy : ¬ π ∣ y) :
    π ∣ y - 1 := by
  classical
  have := Fintype.ofFinite (IsLocalRing.ResidueField R)
  have hc : Fintype.card (IsLocalRing.ResidueField R) = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hq
  set r := IsLocalRing.residue R y
  have hr0 : r ≠ 0 := fun h => hy ((DVR.residue_eq_zero_iff_dvd hπ y).1 h)
  have hr2 : r ^ 2 = r := by rw [← hc]; exact FiniteField.pow_card r
  have hr1 : r = 1 := by
    have : r * (r - 1) = 0 := by linear_combination hr2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hr0)
  rw [← DVR.residue_eq_zero_iff_dvd hπ, map_sub, map_one]
  exact sub_eq_zero.2 hr1

/-- **$\beta_\pi(x^2;\, m)$ at a ramified dyadic prime** ($q = 2$, $\mathrm{ord}_\pi 2 = 2$; e.g. $\mathbb{Z}_2[\sqrt 2]$): from the
closed form `DVR.localDensity_unary`,
$$\beta_\pi(1) = 2q^e = 8, \qquad \beta_\pi(\pi^2) = 2q^{e+1} = 16, \qquad \beta_\pi(1 + \pi) = 0.$$
Compare $\beta_2(x^2;\, 1) = 4$ over $\mathbb{Z}_2$ (`localDensity_sq_two`): same $q$, different $e$. And $1 + \pi$ is a unit
with residue $1$ that is not a square (squares of units are $\equiv 1 \bmod \pi^2$), so $\beta_\pi$ on units is not a function
of the residue class: Table 1-style counts mod $\pi$ cannot give it. -/
@[kb "hanke2004" "p. 362 (dyadic case-by-case; ramified check, e = 2)"]
theorem localDensity_sq_ramified (hq : DVR.q R = 2) {π : R} (hπ : Irreducible π)
    (he : π ^ 2 ∣ 2 ∧ ¬ π ^ (2 + 1) ∣ 2) :
    DVR.localDensity (QuadForm.diag ![(1 : R)]) π 1 = 8 ∧
      DVR.localDensity (QuadForm.diag ![(1 : R)]) π (π ^ 2) = 16 ∧
      DVR.localDensity (QuadForm.diag ![(1 : R)]) π (1 + π) = 0 := by
  have hu : ¬ π ∣ (1 : R) := fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
  have hπ2 : π ∣ 2 := (dvd_pow_self π (by norm_num)).trans he.1
  refine ⟨?_, ?_, ?_⟩
  · rw [DVR.localDensity_unary π hπ 2 he hu (a := 0) (by simp) (by simpa using hu), DVR.divPow_zero, hq]
    split_ifs with h
    · norm_num
    · exact absurd ⟨⟨0, rfl⟩, 1, by simp⟩ h
  · have hd : DVR.divPow π 2 (π ^ 2) = 1 := DVR.divPow_eq_of_eq_mul hπ.ne_zero (by ring)
    rw [DVR.localDensity_unary π hπ 2 he hu (a := 2) dvd_rfl
      (by simpa using DVR.dvr_not_pow_succ_dvd hπ isUnit_one 2), hd, hq]
    split_ifs with h
    · norm_num
    · exact absurd ⟨even_two, 1, by simp⟩ h
  · have hm : ¬ π ∣ 1 + π := fun h => hu (by simpa using dvd_sub h (dvd_refl π))
    rw [DVR.localDensity_unary_unit π hπ 2 he hu hm]
    split_ifs with h
    · exfalso
      obtain ⟨y, hy⟩ := h
      have hy2 : π ^ 2 ∣ y ^ 2 - (1 + π) :=
        (pow_dvd_pow π (by norm_num : 2 ≤ 2 * 2 + 1)).trans (by simpa using hy)
      by_cases hpy : π ∣ y
      · apply hm
        have h1 : π ∣ y ^ 2 - (1 + π) := (dvd_pow_self π (by norm_num)).trans hy2
        have := dvd_sub (dvd_pow hpy (by norm_num : (2 : ℕ) ≠ 0)) h1
        rwa [sub_sub_cancel] at this
      · obtain ⟨t, ht⟩ := DVR.dvd_sub_one_of_q_eq_two hq hπ hpy
        obtain ⟨s, hs⟩ := hπ2
        have hfac : y ^ 2 - (1 + π) = π * (π * (s * t + t ^ 2) - 1) := by
          have : y = 1 + π * t := by linear_combination ht
          rw [this]; linear_combination (π * t) * hs
        have hunit : IsUnit (π * (s * t + t ^ 2) - 1) := by
          refine DVR.dvr_isUnit_of_not_dvd hπ fun hd => hu ?_
          have := dvd_sub (dvd_mul_right π (s * t + t ^ 2)) hd
          rwa [sub_sub_cancel] at this
        rw [hfac] at hy2
        exact DVR.dvr_not_pow_succ_dvd hπ hunit 1 (by simpa using hy2)
    · rfl

end Ramified

end QuadFormsKB.LocalDensity
