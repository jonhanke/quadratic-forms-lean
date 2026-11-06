/-
# Conway–Sloane, LDL IV, §11, Lemma 2 at $p = 2$: sums over discriminant groups are invariants

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §11, Lemma 2, p. 280.

Let $\Delta = \operatorname{diag}(2^{e_i})$ on an index type $\iota$. The finite group $\mathbb Z_2^\iota/\Delta\mathbb Z_2^\iota$
has the representatives $r \in \prod_i \{0, \dots, 2^{e_i} - 1\}$. Given integral $\Psi$, $\Psi'$ which are mutually inverse
modulo $\Delta$, $\Delta'$ (`DeltaData`), $r \mapsto (\Psi r \bmod \Delta')$ is a bijection of representatives
(`repEquiv`); hence sums of $\Delta$-periodic functions $f$, $f'$ with $f'(\Psi v) = f(v)$ agree (`sum_reps_eq`).

Two instances are used for Lemma 2:
* Gauss sums $\sum_r \mathrm{ch}(c\, r^{\mathsf T}F^{-1}r)$ for $F\mathbb Z_2^\iota = \Delta\mathbb Z_2^\iota$ (`Shape`) and
  admissible data (`gauss_eq_of_admissible`);
* the numbers of $2^k$-torsion elements, $\prod_i 2^{\min(k, e_i)}$ (`torsion_eq_of_admissible`).

Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2GaussBase

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Cassels Finset

namespace QuadFormsKB.ConwaySloane.Mass.Gauss2

/-! ### Integrality -/

theorem norm_natCast_le (a : ℕ) : ‖(((a : ℚ) : ℚ_[2]))‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := 2) (a : ℤ)
  rw [Rat.cast_natCast]; exact_mod_cast this

theorem norm_two_le : ‖(2 : ℚ_[2])‖ ≤ 1 := by
  rw [show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ by simpa using Padic.norm_p (p := 2)]; norm_num

theorem norm_two_pow_le (k : ℕ) : ‖(2 : ℚ_[2]) ^ k‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) norm_two_le

theorem isIntV_natVec {ι : Type*} {N : ι → ℕ} (f : (i : ι) → Fin (N i)) : IsIntV (natVec f) :=
  fun i => norm_natCast_le _

theorem norm_sum_le_one {κ : Type*} (s : Finset κ) (g : κ → ℚ_[2]) (h : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∑ i ∈ s, g i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi)))

theorem norm_mul_le_one' {x y : ℚ_[2]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

variable {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

theorem IsIntV.add {v w : ι → ℚ_[2]} (hv : IsIntV v) (hw : IsIntV w) : IsIntV (v + w) := fun i =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv i) (hw i))

theorem IsIntV.sub {v w : ι → ℚ_[2]} (hv : IsIntV v) (hw : IsIntV w) : IsIntV (v - w) := fun i => by
  rw [Pi.sub_apply, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv i) (by rw [norm_neg]; exact hw i))

theorem IsIntV.smul_two_pow {v : ι → ℚ_[2]} (hv : IsIntV v) (k : ℕ) : IsIntV (((2 : ℚ_[2]) ^ k) • v) := fun i => by
  rw [Pi.smul_apply, smul_eq_mul]; exact norm_mul_le_one' (norm_two_pow_le k) (hv i)

theorem IsIntM.mulVec {M : Matrix κ ι ℚ_[2]} (hM : IsIntM M) {v : ι → ℚ_[2]} (hv : IsIntV v) :
    IsIntV (M *ᵥ v) := fun i =>
  norm_sum_le_one _ _ fun j _ => norm_mul_le_one' (hM i j) (hv j)

theorem IsIntV.dot {v w : ι → ℚ_[2]} (hv : IsIntV v) (hw : IsIntV w) : ‖v ⬝ᵥ w‖ ≤ 1 :=
  norm_sum_le_one _ _ fun j _ => norm_mul_le_one' (hv j) (hw j)

theorem IsIntM.mul {M : Matrix κ ι ℚ_[2]} {N : Matrix ι ι' ℚ_[2]} (hM : IsIntM M) (hN : IsIntM N) :
    IsIntM (M * N) := fun i j =>
  norm_sum_le_one _ _ fun l _ => norm_mul_le_one' (hM i l) (hN l j)

theorem IsIntM.sub {M N : Matrix κ ι ℚ_[2]} (hM : IsIntM M) (hN : IsIntM N) : IsIntM (M - N) := fun i j => by
  rw [Matrix.sub_apply, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hM i j) (by rw [norm_neg]; exact hN i j))

theorem IsIntM.add {M N : Matrix κ ι ℚ_[2]} (hM : IsIntM M) (hN : IsIntM N) : IsIntM (M + N) := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hM i j) (hN i j))

/-! ### Representatives modulo $2^k$ -/

/-- The truncation $\mathbb Q_2 \to \mathbb Z_2$ (zero off $\mathbb Z_2$). -/
noncomputable def toZ2 (x : ℚ_[2]) : ℤ_[2] := if h : ‖x‖ ≤ 1 then ⟨x, h⟩ else 0

theorem coe_toZ2 {x : ℚ_[2]} (h : ‖x‖ ≤ 1) : ((toZ2 x : ℤ_[2]) : ℚ_[2]) = x := by
  simp [toZ2, h]

/-- The representative in $\{0, \dots, 2^k - 1\}$ of $x \in \mathbb Z_2$ modulo $2^k$. -/
noncomputable def redC (k : ℕ) (x : ℚ_[2]) : Fin (2 ^ k) :=
  ⟨(PadicInt.toZModPow k (toZ2 x)).val, ZMod.val_lt _⟩

theorem redC_spec (k : ℕ) {x : ℚ_[2]} (hx : ‖x‖ ≤ 1) :
    ∃ z : ℚ_[2], ‖z‖ ≤ 1 ∧ x = (((redC k x : ℕ) : ℚ) : ℚ_[2]) + 2 ^ k * z := by
  have hker : toZ2 x - ((PadicInt.toZModPow k (toZ2 x)).val : ℤ_[2]) ∈
      RingHom.ker (PadicInt.toZModPow (p := 2) k) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨w, hw⟩ := hker
  refine ⟨(w : ℚ_[2]), w.2, ?_⟩
  have hw' : toZ2 x = ((PadicInt.toZModPow k (toZ2 x)).val : ℤ_[2]) + 2 ^ k * w := by
    have h2 : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
    rw [h2] at hw; rw [← hw]; ring
  have e := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hw'
  simp only [PadicInt.coe_add, PadicInt.coe_natCast, PadicInt.coe_mul, PadicInt.coe_pow, coe_toZ2 hx] at e
  simp only [redC]
  rw [Rat.cast_natCast]
  conv_lhs => rw [e]
  norm_num
  left; norm_cast

theorem redC_unique (k : ℕ) {a : ℕ} (ha : a < 2 ^ k) {z : ℚ_[2]} (hz : ‖z‖ ≤ 1) :
    redC k ((((a : ℕ) : ℚ) : ℚ_[2]) + 2 ^ k * z) = ⟨a, ha⟩ := by
  have hx : ‖(((a : ℕ) : ℚ) : ℚ_[2]) + 2 ^ k * z‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (norm_natCast_le a) (norm_mul_le_one' (norm_two_pow_le k) hz))
  have e : toZ2 ((((a : ℕ) : ℚ) : ℚ_[2]) + 2 ^ k * z) = (a : ℤ_[2]) + 2 ^ k * toZ2 z := by
    apply Subtype.ext
    rw [coe_toZ2 hx, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
      Rat.cast_natCast, coe_toZ2 hz]
    norm_num
    left; norm_cast
  have h2 : (PadicInt.toZModPow (p := 2) k) (2 ^ k) = 0 := by
    have : ((2 : ℤ_[2]) ^ k) = ((2 ^ k : ℕ) : ℤ_[2]) := by push_cast; rfl
    rw [this, map_natCast, ZMod.natCast_self]
  apply Fin.ext
  simp only [redC]
  rw [e, map_add, map_natCast, map_mul, h2, zero_mul, add_zero, ZMod.val_natCast_of_lt ha]

/-! ### The bijection of representatives -/

/-- $\operatorname{diag}(2^{e_i})$. -/
noncomputable def dlt (e : ι → ℕ) : Matrix ι ι ℚ_[2] := diagonal fun i => (2 : ℚ_[2]) ^ e i

theorem dlt_mulVec (e : ι → ℕ) (z : ι → ℚ_[2]) (i : ι) : (dlt e *ᵥ z) i = (2 : ℚ_[2]) ^ e i * z i := by
  simp [dlt, mulVec_diagonal]

/-- **Mutually inverse maps modulo $\Delta$, $\Delta'$**: integral $\Psi$, $\Psi'$ with $\Psi\Delta = \Delta'P$,
$\Psi'\Delta' = \Delta P'$, $\Psi'\Psi = 1 + \Delta N$, $\Psi\Psi' = 1 + \Delta'N'$ ($P$, $P'$, $N$, $N'$ integral). -/
structure DeltaData (e : ι → ℕ) (e' : ι' → ℕ) (Ψ : Matrix ι' ι ℚ_[2]) (Ψ' : Matrix ι ι' ℚ_[2]) : Prop where
  intΨ : IsIntM Ψ
  intΨ' : IsIntM Ψ'
  r1 : ∃ P : Matrix ι' ι ℚ_[2], IsIntM P ∧ Ψ * dlt e = dlt e' * P
  r2 : ∃ P : Matrix ι ι' ℚ_[2], IsIntM P ∧ Ψ' * dlt e' = dlt e * P
  r3 : ∃ N : Matrix ι ι ℚ_[2], IsIntM N ∧ Ψ' * Ψ = 1 + dlt e * N
  r4 : ∃ N : Matrix ι' ι' ℚ_[2], IsIntM N ∧ Ψ * Ψ' = 1 + dlt e' * N

theorem DeltaData.symm {e : ι → ℕ} {e' : ι' → ℕ} {Ψ : Matrix ι' ι ℚ_[2]} {Ψ' : Matrix ι ι' ℚ_[2]}
    (h : DeltaData e e' Ψ Ψ') : DeltaData e' e Ψ' Ψ := ⟨h.intΨ', h.intΨ, h.r2, h.r1, h.r4, h.r3⟩

/-- The map of representatives $r \mapsto \Psi r \bmod \Delta'$. -/
noncomputable def repMap (e' : ι' → ℕ) {e : ι → ℕ} (Ψ : Matrix ι' ι ℚ_[2]) (r : (i : ι) → Fin (2 ^ e i)) :
    (i : ι') → Fin (2 ^ e' i) := fun i => redC (e' i) ((Ψ *ᵥ natVec r) i)

theorem repMap_spec {e : ι → ℕ} {e' : ι' → ℕ} {Ψ : Matrix ι' ι ℚ_[2]} (hΨ : IsIntM Ψ)
    (r : (i : ι) → Fin (2 ^ e i)) :
    ∃ z : ι' → ℚ_[2], IsIntV z ∧ Ψ *ᵥ natVec r = natVec (repMap e' Ψ r) + dlt e' *ᵥ z := by
  have hv := hΨ.mulVec (isIntV_natVec r)
  choose z hz hzx using fun i => redC_spec (e' i) (hv i)
  refine ⟨z, hz, funext fun i => ?_⟩
  rw [Pi.add_apply, dlt_mulVec]
  exact hzx i

theorem repMap_left_inv {e : ι → ℕ} {e' : ι' → ℕ} {Ψ : Matrix ι' ι ℚ_[2]} {Ψ' : Matrix ι ι' ℚ_[2]}
    (h : DeltaData e e' Ψ Ψ') (r : (i : ι) → Fin (2 ^ e i)) : repMap e Ψ' (repMap e' Ψ r) = r := by
  obtain ⟨z, hz, hzr⟩ := repMap_spec (e' := e') h.intΨ r
  obtain ⟨P, hP, hP'⟩ := h.r2
  obtain ⟨N, hN, hN'⟩ := h.r3
  -- Ψ' (repMap r) = Ψ'Ψ r - Ψ'Δ'z = r + Δ (N r - P z)
  have key : Ψ' *ᵥ natVec (repMap e' Ψ r) = natVec r + dlt e *ᵥ (N *ᵥ natVec r - P *ᵥ z) := by
    have e1 : natVec (repMap e' Ψ r) = Ψ *ᵥ natVec r - dlt e' *ᵥ z := by rw [hzr]; abel
    rw [e1, mulVec_sub, mulVec_mulVec, mulVec_mulVec, hN', hP', add_mulVec, one_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec, mulVec_sub]
    abel
  have hint : IsIntV (N *ᵥ natVec r - P *ᵥ z) := (hN.mulVec (isIntV_natVec r)).sub (hP.mulVec hz)
  funext i
  simp only [repMap]
  rw [key, Pi.add_apply, dlt_mulVec]
  exact redC_unique (e i) (r i).2 (hint i)

/-- **The bijection of representatives** induced by $\Psi$. -/
noncomputable def repEquiv {e : ι → ℕ} {e' : ι' → ℕ} {Ψ : Matrix ι' ι ℚ_[2]} {Ψ' : Matrix ι ι' ℚ_[2]}
    (h : DeltaData e e' Ψ Ψ') : ((i : ι) → Fin (2 ^ e i)) ≃ ((i : ι') → Fin (2 ^ e' i)) where
  toFun := repMap e' Ψ
  invFun := repMap e Ψ'
  left_inv := repMap_left_inv h
  right_inv := repMap_left_inv h.symm

/-- A function on $\mathbb Z_2^\iota$ which is periodic modulo $\Delta\mathbb Z_2^\iota$. -/
def DPeriodic (e : ι → ℕ) (f : (ι → ℚ_[2]) → ℂ) : Prop :=
  ∀ v z : ι → ℚ_[2], IsIntV v → IsIntV z → f (v + dlt e *ᵥ z) = f v

/-- **Sums over the discriminant groups agree**: for $\Delta$-periodic $f$, $\Delta'$-periodic $f'$ with
$f'(\Psi v) = f(v)$ on $\mathbb Z_2^\iota$. -/
theorem sum_reps_eq {e : ι → ℕ} {e' : ι' → ℕ} {Ψ : Matrix ι' ι ℚ_[2]} {Ψ' : Matrix ι ι' ℚ_[2]}
    (h : DeltaData e e' Ψ Ψ') {f : (ι → ℚ_[2]) → ℂ} {f' : (ι' → ℚ_[2]) → ℂ} (hf' : DPeriodic e' f')
    (hΨ : ∀ v, IsIntV v → f' (Ψ *ᵥ v) = f v) :
    ∑ r : (i : ι) → Fin (2 ^ e i), f (natVec r) = ∑ r : (i : ι') → Fin (2 ^ e' i), f' (natVec r) := by
  refine Fintype.sum_equiv (repEquiv h) _ _ fun r => ?_
  obtain ⟨z, hz, hzr⟩ := repMap_spec (e' := e') h.intΨ r
  rw [← hΨ _ (isIntV_natVec r), hzr, hf' _ _ (isIntV_natVec _) hz]
  rfl

/-! ### Shapes; admissible data give mutually inverse maps modulo $\Delta$ -/

/-- **$F\mathbb Z_2^\iota = \Delta\mathbb Z_2^\iota$**, $F$ symmetric and invertible. -/
structure Shape (F : Matrix ι ι ℚ_[2]) (e : ι → ℕ) : Prop where
  sym : Fᵀ = F
  det : F.det ≠ 0
  ex : ∃ U V : Matrix ι ι ℚ_[2], IsIntM U ∧ IsIntM V ∧ F = dlt e * U ∧ dlt e = F * V

theorem deltaData_of_admissible {F : Matrix ι ι ℚ_[2]} {F' : Matrix ι' ι' ℚ_[2]} {e : ι → ℕ} {e' : ι' → ℕ}
    {T : ℕ} (hS : Shape F e) (hS' : Shape F' e') (h : Admissible F F' T) :
    ∃ Ψ Ψ', DeltaData e e' Ψ Ψ' ∧ ∀ y, IsIntV y → ∃ z : ℚ_[2], ‖z‖ ≤ 1 ∧
      qv F'⁻¹ (Ψ *ᵥ y) - qv F⁻¹ y = (T : ℚ_[2]) * z := by
  obtain ⟨Ψ, Ψ', W, W', M, M', hΨ, hΨ', hW, hW', hM, hM', e1, e2, e3, e4, hq⟩ := h
  obtain ⟨U, V, hU, hV, hFU, hFV⟩ := hS.ex
  obtain ⟨U', V', hU', hV', hFU', hFV'⟩ := hS'.ex
  refine ⟨Ψ, Ψ', ⟨hΨ, hΨ', ⟨U' * W * V, (hU'.mul hW).mul hV, ?_⟩, ⟨U * W' * V', (hU.mul hW').mul hV', ?_⟩,
    ⟨U * M, hU.mul hM, ?_⟩, ⟨U' * M', hU'.mul hM', ?_⟩⟩, hq⟩
  · rw [hFV, ← Matrix.mul_assoc, e1, hFU']; simp only [Matrix.mul_assoc]
  · rw [hFV', ← Matrix.mul_assoc, e2, hFU]; simp only [Matrix.mul_assoc]
  · rw [e3, hFU, Matrix.mul_assoc]
  · rw [e4, hFU', Matrix.mul_assoc]

/-! ### Gauss sums -/

theorem qv_add_mulVec {F : Matrix ι ι ℚ_[2]} (hs : Fᵀ = F) (hd : F.det ≠ 0) (v y : ι → ℚ_[2]) :
    qv F⁻¹ (v + F *ᵥ y) = qv F⁻¹ v + 2 * (v ⬝ᵥ y) + qv F y := by
  have hu : IsUnit F.det := isUnit_iff_ne_zero.2 hd
  have h1 : F⁻¹ *ᵥ (F *ᵥ y) = y := by rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have h2 : (F *ᵥ y) ⬝ᵥ (F⁻¹ *ᵥ v) = y ⬝ᵥ v := by
    have : F *ᵥ y = y ᵥ* F := by rw [← vecMul_transpose, hs]
    rw [this, ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  unfold qv
  rw [mulVec_add, h1, add_dotProduct, dotProduct_add, dotProduct_add, h2, dotProduct_comm y v,
    dotProduct_comm (F *ᵥ y) y]
  ring

/-- The Gauss summand is $\Delta$-periodic (given $\|c\| \le 1$ and $c\,y^{\mathsf T}Fy \in 2\mathbb Z_2$). -/
theorem gauss_periodic {F : Matrix ι ι ℚ_[2]} {e : ι → ℕ} (hS : Shape F e) {c : ℚ_[2]} (hc : ‖c‖ ≤ 1)
    (hev : ∀ y, IsIntV y → ‖c * qv F y / 2‖ ≤ 1) :
    DPeriodic e (fun v => ch (c * qv F⁻¹ v)) := by
  intro v z hv hz
  obtain ⟨U, V, hU, hV, -, hFV⟩ := hS.ex
  have hy := hV.mulVec hz
  simp only
  rw [hFV, ← mulVec_mulVec, qv_add_mulVec hS.sym hS.det, add_assoc, mul_add]
  apply ch_add_of
  have : c * (2 * (v ⬝ᵥ V *ᵥ z) + qv F (V *ᵥ z)) / 2 = c * (v ⬝ᵥ V *ᵥ z) + c * qv F (V *ᵥ z) / 2 := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_mul_le_one' hc (hv.dot hy)) (hev _ hy))

/-- **Gauss sums of isomorphic discriminant forms agree.** -/
theorem gauss_eq_of_admissible {F : Matrix ι ι ℚ_[2]} {F' : Matrix ι' ι' ℚ_[2]} {e : ι → ℕ} {e' : ι' → ℕ}
    {T : ℕ} (hS : Shape F e) (hS' : Shape F' e') (h : Admissible F F' T) {c : ℚ_[2]} (hc : ‖c‖ ≤ 1)
    (hcT : ‖c * (T : ℚ_[2]) / 2‖ ≤ 1) (hev' : ∀ y, IsIntV y → ‖c * qv F' y / 2‖ ≤ 1) :
    ∑ r : (i : ι) → Fin (2 ^ e i), ch (c * qv F⁻¹ (natVec r)) =
      ∑ r : (i : ι') → Fin (2 ^ e' i), ch (c * qv F'⁻¹ (natVec r)) := by
  obtain ⟨Ψ, Ψ', hD, hq⟩ := deltaData_of_admissible hS hS' h
  refine sum_reps_eq (f := fun v => ch (c * qv F⁻¹ v)) hD (gauss_periodic hS' hc hev') fun v hv => ?_
  obtain ⟨z, hz, hzq⟩ := hq v hv
  have : c * qv F'⁻¹ (Ψ *ᵥ v) = c * qv F⁻¹ v + c * (T : ℚ_[2]) * z := by
    rw [mul_assoc, ← hzq]; ring
  rw [this]
  apply ch_add_of
  rw [show c * (T : ℚ_[2]) * z / 2 = (c * (T : ℚ_[2]) / 2) * z by ring]
  exact norm_mul_le_one' hcT hz

/-! ### Torsion counts -/

/-- $2^k v \in \Delta\mathbb Z_2^\iota$. -/
def TorsF (e : ι → ℕ) (k : ℕ) (v : ι → ℚ_[2]) : Prop :=
  ∃ y, IsIntV y ∧ ((2 : ℚ_[2]) ^ k) • v = dlt e *ᵥ y

open Classical in
/-- The indicator of the $2^k$-torsion. -/
noncomputable def torsInd (e : ι → ℕ) (k : ℕ) (v : ι → ℚ_[2]) : ℂ := if TorsF e k v then 1 else 0

theorem tors_periodic (e : ι → ℕ) (k : ℕ) : DPeriodic e (torsInd e k) := by
  intro v z hv hz
  have h : TorsF e k (v + dlt e *ᵥ z) ↔ TorsF e k v := by
    constructor
    · rintro ⟨y, hy, hyv⟩
      refine ⟨y - ((2 : ℚ_[2]) ^ k) • z, hy.sub (hz.smul_two_pow k), ?_⟩
      rw [mulVec_sub, mulVec_smul, ← hyv, smul_add]; abel
    · rintro ⟨y, hy, hyv⟩
      refine ⟨y + ((2 : ℚ_[2]) ^ k) • z, hy.add (hz.smul_two_pow k), ?_⟩
      rw [smul_add, hyv, mulVec_add, mulVec_smul]
  unfold torsInd; split_ifs <;> simp_all

theorem tors_map {e : ι → ℕ} {e' : ι' → ℕ} {Ψ : Matrix ι' ι ℚ_[2]} {Ψ' : Matrix ι ι' ℚ_[2]}
    (hD : DeltaData e e' Ψ Ψ') (k : ℕ) (v : ι → ℚ_[2]) (hv : IsIntV v) :
    TorsF e' k (Ψ *ᵥ v) ↔ TorsF e k v := by
  obtain ⟨P, hP, hP1⟩ := hD.r1
  obtain ⟨P', hP', hP2⟩ := hD.r2
  obtain ⟨N, hN, hN3⟩ := hD.r3
  constructor
  · rintro ⟨y', hy', hyv⟩
    refine ⟨P' *ᵥ y' - ((2 : ℚ_[2]) ^ k) • (N *ᵥ v), (hP'.mulVec hy').sub ((hN.mulVec hv).smul_two_pow k), ?_⟩
    have e1 := congrArg (fun w => Ψ' *ᵥ w) hyv
    simp only [mulVec_smul, mulVec_mulVec, hN3, hP2, add_mulVec, one_mulVec] at e1
    rw [← mulVec_mulVec, ← mulVec_mulVec, smul_add] at e1
    rw [mulVec_sub, mulVec_smul, ← e1]
    abel
  · rintro ⟨y, hy, hyv⟩
    refine ⟨P *ᵥ y, hP.mulVec hy, ?_⟩
    rw [← mulVec_smul, hyv, mulVec_mulVec, hP1, mulVec_mulVec]

/-- The numbers of $2^k$-torsion elements of the two discriminant groups agree. -/
theorem torsSum_eq {F : Matrix ι ι ℚ_[2]} {F' : Matrix ι' ι' ℚ_[2]} {e : ι → ℕ} {e' : ι' → ℕ}
    {T : ℕ} (hS : Shape F e) (hS' : Shape F' e') (h : Admissible F F' T) (k : ℕ) :
    ∑ r : (i : ι) → Fin (2 ^ e i), torsInd e k (natVec r) =
      ∑ r : (i : ι') → Fin (2 ^ e' i), torsInd e' k (natVec r) := by
  obtain ⟨Ψ, Ψ', hD, -⟩ := deltaData_of_admissible hS hS' h
  refine sum_reps_eq hD (tors_periodic e' k) fun v hv => ?_
  have := tors_map hD k v hv
  unfold torsInd; split_ifs <;> simp_all

theorem torsF_natVec_iff (e : ι → ℕ) (k : ℕ) (r : (i : ι) → Fin (2 ^ e i)) :
    TorsF e k (natVec r) ↔ ∀ i, 2 ^ e i ∣ 2 ^ k * (r i : ℕ) := by
  constructor
  · rintro ⟨y, hy, hyv⟩ i
    have e1 := congrFun hyv i
    rw [Pi.smul_apply, smul_eq_mul, dlt_mulVec] at e1
    have hn : ‖(((2 ^ k * (r i : ℕ) : ℕ) : ℤ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-(e i : ℕ) : ℤ) := by
      have : (((2 ^ k * (r i : ℕ) : ℕ) : ℤ) : ℚ_[2]) = (2 : ℚ_[2]) ^ e i * y i := by
        rw [← e1]; simp [natVec]
      rw [this, norm_mul, TwoAdic.norm_two_pow]
      exact mul_le_of_le_one_right (by positivity) (hy i)
    have := (Padic.norm_int_le_pow_iff_dvd (p := 2) _ (e i)).1 (by exact_mod_cast hn)
    exact_mod_cast this
  · intro hd
    choose q hq using hd
    refine ⟨fun i => (((q i : ℕ) : ℚ) : ℚ_[2]), fun i => norm_natCast_le _, funext fun i => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, dlt_mulVec]
    have := congrArg (fun t : ℕ => ((t : ℚ) : ℚ_[2])) (hq i)
    simp only [natVec]
    push_cast at this ⊢
    exact this

theorem card_dvd_filter (e k : ℕ) :
    (univ.filter (fun a : Fin (2 ^ e) => 2 ^ e ∣ 2 ^ k * (a : ℕ))).card = 2 ^ min k e := by
  rcases le_or_gt e k with hek | hke
  · rw [min_eq_right hek, Finset.filter_true_of_mem fun a _ => Dvd.dvd.mul_right (pow_dvd_pow 2 hek) _,
      card_univ, Fintype.card_fin]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hke
    rw [min_eq_left hke.le]
    have hiff : ∀ a : ℕ, 2 ^ (k + d + 1) ∣ 2 ^ k * a ↔ 2 ^ (d + 1) ∣ a := fun a => by
      rw [show k + d + 1 = k + (d + 1) by ring, pow_add]
      exact Nat.mul_dvd_mul_iff_left (by positivity)
    have hlt : ∀ b : Fin (2 ^ k), (b : ℕ) * 2 ^ (d + 1) < 2 ^ (k + d + 1) := fun b => by
      rw [show (2 : ℕ) ^ (k + d + 1) = 2 ^ k * 2 ^ (d + 1) by ring]
      exact (Nat.mul_lt_mul_right (pow_pos (by norm_num : (0 : ℕ) < 2) (d + 1))).2 b.2
    refine (Finset.card_bij (s := (univ : Finset (Fin (2 ^ k))))
      (fun b _ => (⟨(b : ℕ) * 2 ^ (d + 1), hlt b⟩ : Fin (2 ^ (k + d + 1)))) ?_ ?_ ?_).symm.trans (Finset.card_fin _)
    · intro b _
      simp only [mem_filter, mem_univ, true_and]
      exact (hiff _).2 (Dvd.intro_left _ rfl)
    · intro b _ b' _ hbb
      have := congrArg Fin.val hbb
      simp only at this
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by positivity) this)
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      obtain ⟨q, hq⟩ := (hiff _).1 ha
      have hq' : q < 2 ^ k := by
        have h1 := a.2
        have h2 : (2 : ℕ) ^ (k + d + 1) = 2 ^ k * 2 ^ (d + 1) := by ring
        rw [hq, h2, mul_comm (2 ^ (d + 1)) q] at h1
        exact Nat.lt_of_mul_lt_mul_right h1
      exact ⟨⟨q, hq'⟩, mem_univ _, Fin.ext (by simp [hq, mul_comm])⟩

/-- **The torsion count** $\prod_i 2^{\min(k, e_i)}$. -/
theorem torsSum_eq_prod (e : ι → ℕ) (k : ℕ) :
    ∑ r : (i : ι) → Fin (2 ^ e i), torsInd e k (natVec r) = ((∏ i, 2 ^ min k (e i) : ℕ) : ℂ) := by
  classical
  have h1 : ∀ r : (i : ι) → Fin (2 ^ e i), torsInd e k (natVec r) =
      ∏ i, (if 2 ^ e i ∣ 2 ^ k * (r i : ℕ) then (1 : ℂ) else 0) := fun r => by
    rw [Finset.prod_ite_zero, Finset.prod_const_one]
    unfold torsInd
    simp only [torsF_natVec_iff, mem_univ, true_implies]
  simp_rw [h1]
  have h2 := Fintype.prod_sum (fun i (a : Fin (2 ^ e i)) => if 2 ^ e i ∣ 2 ^ k * (a : ℕ) then (1 : ℂ) else 0)
  rw [← h2]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_boole, card_dvd_filter]
  push_cast; ring

/-- **Equal torsion counts**: $\sum_i \min(k, e_i) = \sum_{i'} \min(k, e'_{i'})$ for every $k$. -/
theorem sum_min_eq {F : Matrix ι ι ℚ_[2]} {F' : Matrix ι' ι' ℚ_[2]} {e : ι → ℕ} {e' : ι' → ℕ}
    {T : ℕ} (hS : Shape F e) (hS' : Shape F' e') (h : Admissible F F' T) (k : ℕ) :
    ∑ i, min k (e i) = ∑ i, min k (e' i) := by
  have h1 := torsSum_eq hS hS' h k
  rw [torsSum_eq_prod, torsSum_eq_prod] at h1
  have h2 : (∏ i, 2 ^ min k (e i) : ℕ) = ∏ i, 2 ^ min k (e' i) := by exact_mod_cast h1
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum] at h2
  exact Nat.pow_right_injective le_rfl h2

end QuadFormsKB.ConwaySloane.Mass.Gauss2
