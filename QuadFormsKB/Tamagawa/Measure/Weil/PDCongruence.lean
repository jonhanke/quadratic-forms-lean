import QuadFormsKB.Tamagawa.Measure.Weil.PDLocal
import QuadFormsKB.Tamagawa.Measure.LerayCongruence
import QuadFormsKB.Tamagawa.Measure.Weil.PDGoodRatio

/-!
# $PD^\times \cong SO(D^0)$ at small congruence subgroups: the Cayley identity

**Layer:** a field $K$, $D = (A,B)_K$; then $F_v$ for a finite place $v$ of a number field (dyadic included).

**Defines/proves**
* `adMat A B y`: the matrix of $\operatorname{ad}(y) = [y,\cdot\,]$ on $D^0$ in the basis $i,j,k$ (`adMat_eq`);
* **the Cayley identity** (`nMat_one_add_pure_mul`): $N(1+y)\,(2 - \operatorname{ad}y) = \operatorname{nrd}(1+y)\,
  (2+\operatorname{ad}y)$ for $y \in D^0$, i.e. conjugation by $1+y$ is the Cayley transform
  $(1+\tfrac12\operatorname{ad}y)(1-\tfrac12\operatorname{ad}y)^{-1}$ of $\tfrac12\operatorname{ad}y$ (Gibbs' vector
  parametrization of rotations);
* at a finite place $v$ with $|2|_v = q^{-s}$, $A, B$ integral, $m > s$: **conjugation by $1+y$ lies in the principal
  congruence subgroup $K_m = SO\cap(1+\pi^mM_3(\mathfrak o_v))$ iff $\operatorname{ad}(y) \in \pi^mM_3(\mathfrak o_v)$**,
  i.e. iff $y \in \Lambda'_m = \{y : 2y_0, 2y_1, 2Ay_2, 2By_2 \in \mathfrak p^m\}$ (`conjMat_mem_ballOne_iff`).

Source: Weil 1982, §3.7(a), p. 63 (the isomorphism $SO_3 \cong D^\times/G_m$); the Cayley transform for $SO_3$:
Voight 2021, §4.5 [unverified].
-/

open Matrix Quaternion NumberField IsDedekindDomain WithZero MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices

/-! ### The Cayley identity over a field -/

section Generic

variable {K : Type*} [Field K] (A B : K)

/-- The matrix of $\operatorname{ad}(y) : z \mapsto yz - zy$ on $D^0 = Ki \oplus Kj \oplus Kk$. -/
def adMat (y : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => imv (Quat.pure y * Quat.pure (Pi.single j (1 : K)) - Quat.pure (Pi.single j (1 : K)) * Quat.pure y : ℍ[K,A,B]) i

theorem adMat_eq (y : Fin 3 → K) : adMat A B y =
    !![0, 2 * B * y 2, -(2 * B * y 1); -(2 * A * y 2), 0, 2 * A * y 0; -(2 * y 1), 2 * y 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adMat, imv, Quat.pure, Pi.single_apply] <;> ring

/-- **The Cayley identity** $N(1+y)(2 - \operatorname{ad}y) = \operatorname{nrd}(1+y)(2 + \operatorname{ad}y)$. -/
@[kb "voight2021" "§4.5 [unverified]"]
theorem nMat_one_add_pure_mul (y : Fin 3 → K) :
    nMat (1 + Quat.pure y : ℍ[K,A,B]) * (2 - adMat A B y) = nrd (1 + Quat.pure y : ℍ[K,A,B]) • (2 + adMat A B y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [nMat, adMat, imv, Quat.pure, nrd, Matrix.mul_apply, Fin.sum_univ_three, Pi.single_apply, Matrix.ofNat_apply] <;>
  ring

theorem nrd_one_add_pure (y : Fin 3 → K) :
    nrd (1 + Quat.pure y : ℍ[K,A,B]) = 1 - A * y 0 ^ 2 - B * y 1 ^ 2 + A * B * y 2 ^ 2 := by
  simp [nrd, Quat.pure]

/-- The conjugation matrix of $u = 1 + y$ satisfies $c(u)(2 - \operatorname{ad}y) = 2 + \operatorname{ad}y$. -/
theorem conjGL_mul_eq (u : (ℍ[K,A,B])ˣ) (y : Fin 3 → K) (hu : (u : ℍ[K,A,B]) = 1 + Quat.pure y) :
    ((conjGL u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (2 - adMat A B y) = 2 + adMat A B y := by
  have hn : nrd (u : ℍ[K,A,B]) ≠ 0 := nrd_units_ne_zero u
  have hinv : nrd ((u⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) = (nrd (u : ℍ[K,A,B]))⁻¹ := by
    have h := nrd_mul (u : ℍ[K,A,B]) ((u⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])
    rw [Units.mul_inv, nrd_one] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  rw [conjGL_val, hinv, Matrix.smul_mul, hu, nMat_one_add_pure_mul, ← hu, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- $x = \operatorname{re}(x) + (\text{pure part of } x)$. -/
theorem eq_re_add_pure (x : ℍ[K,A,B]) : x = algebraMap K ℍ[K,A,B] x.re + Quat.pure (imv x) := by
  ext <;> simp [imv, Quat.pure]

/-- Scaling a unit with $\operatorname{re}\alpha \ne 0$ to the form $1 + y$. -/
theorem scale_val (α : (ℍ[K,A,B])ˣ) (h : (α : ℍ[K,A,B]).re ≠ 0) :
    ((Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom (Units.mk0 ((α : ℍ[K,A,B]).re)⁻¹ (inv_ne_zero h)) * α :
      (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) = 1 + Quat.pure (((α : ℍ[K,A,B]).re)⁻¹ • imv (α : ℍ[K,A,B])) := by
  rw [Units.val_mul]
  simp only [Units.coe_map, MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe, Units.val_mk0]
  conv_lhs => rw [eq_re_add_pure A B (α : ℍ[K,A,B])]
  ext <;> simp [imv, Quat.pure, h]

/-- **The trace of a conjugation:** $\operatorname{tr} c(\alpha) = 4\operatorname{re}(\alpha)^2/\operatorname{nrd}(\alpha)
- 1$ (from `trace_nMat_add_nrd`). -/
theorem trace_conjGL (α : (ℍ[K,A,B])ˣ) :
    ((conjGL α : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      4 * (α : ℍ[K,A,B]).re ^ 2 / nrd (α : ℍ[K,A,B]) - 1 := by
  have hn : nrd (α : ℍ[K,A,B]) ≠ 0 := nrd_units_ne_zero α
  have hinv : nrd ((α⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) = (nrd (α : ℍ[K,A,B]))⁻¹ := by
    have h := nrd_mul (α : ℍ[K,A,B]) ((α⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])
    rw [Units.mul_inv, nrd_one] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  rw [conjGL_val, hinv, Matrix.trace_smul, smul_eq_mul]
  have := trace_nMat_add_nrd (α : ℍ[K,A,B])
  rw [show (nMat (α : ℍ[K,A,B])).trace = 4 * (α : ℍ[K,A,B]).re ^ 2 - nrd (α : ℍ[K,A,B]) by
    linear_combination this]
  field_simp

end Generic

/-! ### Finite places: the congruence subgroups -/

section Place

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

open LerayPadic

/-- $\Lambda'_m = \{y \in D^0 : 2y_0, 2y_1, 2Ay_2, 2By_2 \in \mathfrak p_v^m\}$, the $y$ with
$\operatorname{ad}(y) \in \pi^mM_3(\mathfrak o_v)$. -/
def latP (m : ℕ) (A B : Fv) : Set (Fin 3 → Fv) :=
  {y | Valued.v (2 * y 0) ≤ exp (-(m : ℤ)) ∧ Valued.v (2 * y 1) ≤ exp (-(m : ℤ)) ∧
    Valued.v (2 * A * y 2) ≤ exp (-(m : ℤ)) ∧ Valued.v (2 * B * y 2) ≤ exp (-(m : ℤ))}

variable {v}

theorem adMat_le_iff {A B : Fv} (hA : Valued.v A ≤ 1) (hB : Valued.v B ≤ 1) (m : ℕ) (y : Fin 3 → Fv) :
    (∀ i l, Valued.v (adMat A B y i l) ≤ exp (-(m : ℤ))) ↔ y ∈ latP v m A B := by
  rw [adMat_eq]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h 2 1
    · simpa using h 2 0
    · simpa [mul_assoc] using h 1 0
    · simpa [mul_assoc] using h 0 1
  · rintro ⟨h0, h1, h2, h3⟩ i l
    have e1 : Valued.v (2 * B * y 1) ≤ exp (-(m : ℤ)) := by
      rw [show 2 * B * y 1 = B * (2 * y 1) by ring, map_mul]
      exact (mul_le_mul' hB h1).trans (by rw [one_mul])
    have e0 : Valued.v (2 * A * y 0) ≤ exp (-(m : ℤ)) := by
      rw [show 2 * A * y 0 = A * (2 * y 0) by ring, map_mul]
      exact (mul_le_mul' hA h0).trans (by rw [one_mul])
    simp only [map_mul] at h0 h1 h2 h3 e0 e1
    fin_cases i <;> fin_cases l <;> simp [Valuation.map_neg] <;> assumption

/-- Valuation of $x/2$: $|x/2|_v = q^{s}|x|_v$ for $|2|_v = q^{-s}$. -/
theorem valued_half_le {s m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s ≤ m) {x : Fv}
    (hx : Valued.v x ≤ exp (-(m : ℤ))) : Valued.v ((2 : Fv)⁻¹ * x) ≤ exp (-((m - s : ℕ) : ℤ)) := by
  rw [map_mul, map_inv₀, hs, ← WithZero.exp_neg, neg_neg]
  calc exp (s : ℤ) * Valued.v x ≤ exp (s : ℤ) * exp (-(m : ℤ)) := mul_le_mul_right hx _
    _ = exp (-((m - s : ℕ) : ℤ)) := by rw [← WithZero.exp_add]; congr 1; push_cast [Nat.cast_sub hsm]; ring

theorem two_sub_eq_smul (M : Matrix (Fin 3) (Fin 3) Fv) :
    (2 : Matrix (Fin 3) (Fin 3) Fv) - M = (2 : Fv) • (1 - (2 : Fv)⁻¹ • M) := by
  have h2 : (2 : Fv) ≠ 0 := two_ne_zero
  rw [smul_sub, smul_smul, mul_inv_cancel₀ h2, one_smul, two_smul, one_add_one_eq_two]

theorem two_add_eq_smul (M : Matrix (Fin 3) (Fin 3) Fv) :
    (2 : Matrix (Fin 3) (Fin 3) Fv) + M = (2 : Fv) • (1 + (2 : Fv)⁻¹ • M) := by
  have h2 : (2 : Fv) ≠ 0 := two_ne_zero
  rw [smul_add, smul_smul, mul_inv_cancel₀ h2, one_smul, two_smul, one_add_one_eq_two]

/-- **Forward direction:** for $y \in \Lambda'_m$ ($m > s$), conjugation by $1 + y$ lies in $1 + \pi^mM_3(\mathfrak o_v)$. -/
theorem conjMat_mem_ballOne {A B : Fv} (hA : Valued.v A ≤ 1) (hB : Valued.v B ≤ 1) {s m : ℕ}
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s < m) {y : Fin 3 → Fv} (hy : y ∈ latP v m A B)
    (u : (ℍ[Fv,A,B])ˣ) (hu : (u : ℍ[Fv,A,B]) = 1 + Quat.pure y) :
    ((conjGL u : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m := by
  set X := ((conjGL u : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv)
  set M := adMat A B y
  have hM : ∀ i l, Valued.v (M i l) ≤ exp (-(m : ℤ)) := (adMat_le_iff hA hB m y).mpr hy
  set A' := (2 : Fv)⁻¹ • M
  have hA' : ∀ i l, Valued.v (A' i l) ≤ exp (-((m - s : ℕ) : ℤ)) := fun i l => by
    simpa [A', Matrix.smul_apply, smul_eq_mul] using valued_half_le hs hsm.le (hM i l)
  set B' := 1 - A'
  have hB' : B' ∈ ballOne v (m - s) := fun i l => by
    simpa [B', Matrix.sub_apply, Valuation.map_neg] using hA' i l
  have hms : 1 ≤ m - s := by omega
  obtain ⟨hBi, -⟩ := inv_mem_ballOne v hms hB'
  have hdet : IsUnit B'.det := isUnit_iff_ne_zero.mpr (by
    intro h; have := valued_det_eq_one v hms hB'; rw [h, map_zero] at this; exact zero_ne_one this)
  have hBB : B' * B'⁻¹ = 1 := Matrix.mul_nonsing_inv B' hdet
  have hXB : X * B' = 1 + A' := by
    have h := conjGL_mul_eq A B u y hu
    rw [two_sub_eq_smul, two_add_eq_smul, Matrix.mul_smul] at h
    exact smul_right_injective _ (two_ne_zero : (2 : Fv) ≠ 0) h
  have hX1 : X - 1 = M * B'⁻¹ := by
    have : X = (1 + A') * B'⁻¹ := by rw [← hXB, Matrix.mul_assoc, hBB, Matrix.mul_one]
    rw [this]
    have hM2 : M = (1 + A') - B' := by
      simp only [B', A']
      rw [show (1 + (2 : Fv)⁻¹ • M) - (1 - (2 : Fv)⁻¹ • M) = (2 : Fv) • ((2 : Fv)⁻¹ • M) by
        rw [two_smul]; abel, smul_smul, mul_inv_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0), one_smul]
    conv_rhs => rw [hM2]
    rw [Matrix.sub_mul, hBB]
  intro i l
  rw [← Matrix.sub_apply, hX1]
  calc Valued.v ((M * B'⁻¹) i l) ≤ exp (-(m : ℤ)) * 1 :=
        valued_mul_apply_le v hM (ballOne_subset_intM v _ hBi) i l
    _ = _ := mul_one _

/-- **Backward direction:** if conjugation by $1 + y$ lies in $1 + \pi^mM_3(\mathfrak o_v)$ ($m > s$), then
$y \in \Lambda'_m$. -/
theorem mem_latP_of_conjMat_mem_ballOne {A B : Fv} (hA : Valued.v A ≤ 1) (hB : Valued.v B ≤ 1) {s m : ℕ}
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s < m) {y : Fin 3 → Fv}
    (u : (ℍ[Fv,A,B])ˣ) (hu : (u : ℍ[Fv,A,B]) = 1 + Quat.pure y)
    (hX : ((conjGL u : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m) : y ∈ latP v m A B := by
  set X := ((conjGL u : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv)
  set M := adMat A B y
  set C := 1 + (2 : Fv)⁻¹ • (X - 1)
  have hC : C ∈ ballOne v (m - s) := fun i l => by
    have := valued_half_le hs hsm.le (hX i l)
    simpa [C, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] using this
  have hms : 1 ≤ m - s := by omega
  obtain ⟨hCi, hCC⟩ := inv_mem_ballOne v hms hC
  have h := conjGL_mul_eq A B u y hu
  change X * (2 - M) = 2 + M at h
  have hCM : C * M = X - 1 := by
    have e : (2 : Fv) • (C * M) = (2 : Fv) • (X - 1) := by
      have h2 : (2 : Fv) • C = X + 1 := by
        simp only [C, smul_add, smul_smul, mul_inv_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0), one_smul, two_smul]
        abel
      rw [← Matrix.smul_mul, h2, Matrix.add_mul, Matrix.one_mul]
      have hXM : X * M = X * 2 - (2 + M) := by rw [← h, Matrix.mul_sub]; abel
      rw [hXM, mul_two, two_smul, ← one_add_one_eq_two]
      abel
    exact smul_right_injective _ (two_ne_zero : (2 : Fv) ≠ 0) e
  have hM' : M = C⁻¹ * (X - 1) := by rw [← hCM, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
  refine (adMat_le_iff hA hB m y).mp fun i l => ?_
  change Valued.v (M i l) ≤ _
  rw [hM']
  calc Valued.v ((C⁻¹ * (X - 1)) i l) ≤ 1 * exp (-(m : ℤ)) :=
        valued_mul_apply_le v (ballOne_subset_intM v _ hCi) hX i l
    _ = _ := one_mul _

/-- If $c(\alpha) \in 1 + \pi^mM_3(\mathfrak o_v)$ with $m > 2s$, then $\operatorname{re}\alpha \ne 0$: otherwise
$\operatorname{tr}c(\alpha) = -1$ (`trace_conjGL`) while $\operatorname{tr}c(\alpha) \equiv 3 \bmod \pi^m$. -/
theorem re_ne_zero_of_conjGL_mem_ballOne {A B : Fv} {s m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (h2s : 2 * s < m) (α : (ℍ[Fv,A,B])ˣ)
    (hX : ((conjGL α : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m) : (α : ℍ[Fv,A,B]).re ≠ 0 := by
  intro h0
  set X := ((conjGL α : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv)
  have htr : X.trace = -1 := by
    rw [trace_conjGL, h0]; simp
  have hsum : Valued.v (X - 1).trace ≤ exp (-(m : ℤ)) := by
    rw [Matrix.trace]
    exact Valuation.map_sum_le _ fun i _ => by rw [Matrix.diag_apply, Matrix.sub_apply]; exact hX i i
  rw [Matrix.trace_sub, htr, Matrix.trace_one, Fintype.card_fin] at hsum
  have h4 : Valued.v ((-1 : Fv) - ((3 : ℕ) : Fv)) = exp (-((2 * s : ℕ) : ℤ)) := by
    rw [show (-1 : Fv) - ((3 : ℕ) : Fv) = -(2 * 2) by push_cast; ring, Valuation.map_neg, map_mul, hs,
      ← WithZero.exp_add]
    congr 1; push_cast; ring
  rw [h4, WithZero.exp_le_exp] at hsum
  omega

end Place

/-! ### The quaternion side of $K_m$: the subgroup $\Lambda^{(m)}_v = c^{-1}(K_m) \cap \Lambda_v^\times$ -/

section LocalCong

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F)

local notation "Fv" => v.adicCompletion F
local notation "Q₀" => QuatZeta.pureFormO a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (QuatZeta.pureFormO a b)
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)

open LerayPadic

/-- $\Lambda_v^\times$ as a subgroup of $(D\otimes F_v)^\times$. -/
def lamLocUnitsSub : Subgroup (QuatV (a : F) (b : F) v)ˣ where
  carrier := lamLocUnits (a : F) (b : F) v
  one_mem' := one_mem_lamLocUnits _ _ v
  mul_mem' hx hy := lamLocUnits_mul_mem (fun w => valued_algebraMap_le_one a w)
    (fun w => valued_algebraMap_le_one b w) hx hy
  inv_mem' hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

/-- **The quaternion side of the principal congruence subgroup:** $\Lambda^{(m)}_v = c^{-1}(K_m) \cap \Lambda_v^\times$. -/
def lamCong (m : ℕ) (hm : 1 ≤ m) : Subgroup (QuatV (a : F) (b : F) v)ˣ :=
  (congSub v Q₀ m hm).comap (conjOrth QF (hQF a b)) ⊓ lamLocUnitsSub v a b

theorem conjOrth_coeM (u : (QuatV (a : F) (b : F) v)ˣ) :
    (((conjOrth QF (hQF a b) u : orthGroup QF Fv) : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) =
      ((conjGL u : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) := rfl

variable {v a b}

theorem valued_mul_of_valued_eq_one {r x : Fv} (hr : Valued.v r = 1) : Valued.v (r * x) = Valued.v x := by
  rw [map_mul, hr, one_mul]

/-- Membership in $\Lambda'_m$ is unchanged by scaling with a unit. -/
theorem smul_mem_latP_iff {m : ℕ} {r : Fv} (hr : Valued.v r = 1) (y : Fin 3 → Fv) :
    r • y ∈ latP v m Av Bv ↔ y ∈ latP v m Av Bv := by
  simp only [latP, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul, hr, one_mul]

/-- The small terms: for $y \in \Lambda'_m$ ($m > s$), $|\operatorname{nrd}(1+y)|_v = 1$. -/
theorem valued_nrd_one_add_pure {s m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s < m)
    {y : Fin 3 → Fv} (hy : y ∈ latP v m Av Bv) :
    Valued.v (nrd (1 + Quat.pure y : ℍ[Fv,Av,Bv])) = 1 := by
  have hA := valued_algebraMap_le_one a v
  have hB := valued_algebraMap_le_one b v
  obtain ⟨h0, h1, h2, h3⟩ := hy
  have hlt : exp (-((m - s : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hy0 : Valued.v (y 0) < 1 := by
    have := valued_half_le hs hsm.le h0
    rw [← mul_assoc, inv_mul_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0), one_mul] at this
    exact this.trans_lt hlt
  have hy1 : Valued.v (y 1) < 1 := by
    have := valued_half_le hs hsm.le h1
    rw [← mul_assoc, inv_mul_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0), one_mul] at this
    exact this.trans_lt hlt
  have hAy2 : Valued.v (Av * y 2) < 1 := by
    have := valued_half_le hs hsm.le h2
    rw [show (2 : Fv)⁻¹ * (2 * Av * y 2) = Av * y 2 by field_simp] at this
    exact this.trans_lt hlt
  have hBy2 : Valued.v (Bv * y 2) < 1 := by
    have := valued_half_le hs hsm.le h3
    rw [show (2 : Fv)⁻¹ * (2 * Bv * y 2) = Bv * y 2 by field_simp] at this
    exact this.trans_lt hlt
  have hsmall : Valued.v (-(Av * y 0 ^ 2) - Bv * y 1 ^ 2 + (Av * y 2) * (Bv * y 2)) < 1 := by
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ((Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)) ?_)
    · rw [Valuation.map_neg, map_mul, map_pow]
      exact (mul_le_of_le_one_left' hA).trans_lt (pow_lt_one₀ zero_le hy0 two_ne_zero)
    · rw [map_mul, map_pow]
      exact (mul_le_of_le_one_left' hB).trans_lt (pow_lt_one₀ zero_le hy1 two_ne_zero)
    · rw [map_mul]; exact (mul_le_of_le_one_right' hBy2.le).trans_lt hAy2
  rw [nrd_one_add_pure, show 1 - Av * y 0 ^ 2 - Bv * y 1 ^ 2 + Av * Bv * y 2 ^ 2 =
    1 + (-(Av * y 0 ^ 2) - Bv * y 1 ^ 2 + (Av * y 2) * (Bv * y 2)) by ring]
  exact Valuation.map_one_add_of_lt _ hsmall

/-- $u = r\,(1 + r^{-1}\operatorname{im}u)$ for $r = \operatorname{re}u \ne 0$. -/
theorem eq_smul_one_add_pure {K : Type*} [Field K] {A B : K} (x : ℍ[K,A,B]) (h : x.re ≠ 0) :
    x = x.re • (1 + Quat.pure (x.re⁻¹ • imv x)) := by
  ext <;> simp [imv, Quat.pure, h]

theorem valued_eq_one_of_sq {r : Fv} (h : Valued.v r ^ 2 = 1) : Valued.v r = 1 := by
  rcases lt_trichotomy (Valued.v r) 1 with hlt | heq | hgt
  · exfalso
    have : Valued.v r ^ 2 < 1 := by
      rw [pow_two]; exact (mul_le_of_le_one_left' hlt.le).trans_lt hlt
    rw [h] at this; exact lt_irrefl _ this
  · exact heq
  · exfalso
    have : 1 < Valued.v r ^ 2 := by
      rw [pow_two]; exact hgt.trans_le (le_mul_of_one_le_left' hgt.le)
    rw [h] at this; exact lt_irrefl _ this

variable (v a b) in
/-- **The quaternion side of $K_m$ in coordinates** ($|2|_v = q^{-s}$, $|a|_v = q^{-e_a}$, $m > 2s$,
$m \ge s + e_a$): $u \in \Lambda^{(m)}_v$ iff $\operatorname{re}u \in \mathfrak o_v^\times$ and
$\operatorname{im}u \in \Lambda'_m$. -/
theorem mem_lamCong_iff {s eA m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hA : Valued.v Av = exp (-(eA : ℤ))) (h2s : 2 * s < m) (hmA : s + eA ≤ m) (hm : 1 ≤ m)
    (u : (QuatV (a : F) (b : F) v)ˣ) :
    u ∈ lamCong v a b m hm ↔ Valued.v (u : QuatV (a : F) (b : F) v).re = 1 ∧
      imv (u : QuatV (a : F) (b : F) v) ∈ latP v m Av Bv := by
  have hAi := valued_algebraMap_le_one a v
  have hBi := valued_algebraMap_le_one b v
  have hsm : s < m := by omega
  set x := (u : QuatV (a : F) (b : F) v) with hx
  constructor
  · rintro ⟨hc, hl⟩
    have hX : ((conjGL u : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m := hc
    have hr0 : x.re ≠ 0 := re_ne_zero_of_conjGL_mem_ballOne hs h2s u hX
    set w := Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom (Units.mk0 x.re⁻¹ (inv_ne_zero hr0)) * u
    have hw := scale_val Av Bv u hr0
    have hwX : ((conjGL w : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m := by
      rw [conjGL_smul]; exact hX
    have hy := mem_latP_of_conjMat_mem_ballOne hAi hBi hs hsm w hw hwX
    have hn := valued_nrd_one_add_pure (a := a) (b := b) hs hsm hy
    have hnu : Valued.v (nrd x) = 1 := by
      have := ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w)
        (fun w => valued_algebraMap_le_one b w) u).mp hl).2
      rwa [nrdLoc_eq_nrd] at this
    have hxe := eq_smul_one_add_pure x hr0
    have hre : Valued.v x.re = 1 := by
      have h2 : Valued.v (nrd x) = Valued.v x.re ^ 2 * Valued.v (nrd (1 + Quat.pure (x.re⁻¹ • imv x) :
          QuatV (a : F) (b : F) v)) := by
        conv_lhs => rw [hxe]
        rw [nrd_smul, map_mul, map_pow]
      rw [hnu, hn, mul_one] at h2
      exact valued_eq_one_of_sq h2.symm
    refine ⟨hre, ?_⟩
    have : imv x = x.re • (x.re⁻¹ • imv x) := by rw [smul_smul, mul_inv_cancel₀ hr0, one_smul]
    rw [this, smul_mem_latP_iff hre]
    exact hy
  · rintro ⟨hre, hy⟩
    have hr0 : x.re ≠ 0 := fun h0 => by rw [h0, map_zero] at hre; exact zero_ne_one hre
    have hri : Valued.v x.re⁻¹ = 1 := by rw [map_inv₀, hre, inv_one]
    set y := x.re⁻¹ • imv x
    have hy' : y ∈ latP v m Av Bv := (smul_mem_latP_iff hri _).mpr hy
    set w := Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom (Units.mk0 x.re⁻¹ (inv_ne_zero hr0)) * u
    have hw := scale_val Av Bv u hr0
    refine ⟨?_, ?_⟩
    · show ((conjGL u : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m
      rw [← conjGL_smul u (Units.mk0 x.re⁻¹ (inv_ne_zero hr0))]
      exact conjMat_mem_ballOne hAi hBi hs hsm hy' w hw
    · refine (mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w)
        (fun w => valued_algebraMap_le_one b w) u).mpr ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3⟩ := hy
        have hO : ∀ c : Fv, Valued.v c ≤ 1 → c ∈ v.adicCompletionIntegers F := fun c hc =>
          (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc
        have hle : ∀ {k : ℕ}, exp (-(k : ℤ)) ≤ (1 : ℤᵐ⁰) := fun {k} => by
          rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
        refine ⟨hO _ hre.le, hO _ ?_, hO _ ?_, hO _ ?_⟩
        · have := valued_half_le hs hsm.le h0
          rw [← mul_assoc, inv_mul_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0), one_mul] at this
          exact this.trans hle
        · have := valued_half_le hs hsm.le h1
          rw [← mul_assoc, inv_mul_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0), one_mul] at this
          exact this.trans hle
        · -- `|2 a x_3| ≤ q^{-m}` and `|2a| = q^{-(s+e_a)}` give `|x_3| ≤ q^{-(m - s - e_a)} ≤ 1`
          have h2' : Valued.v (2 * Av) * Valued.v (imv x 2) ≤ exp (-(m : ℤ)) := by
            rw [← map_mul]; exact h2
          rw [map_mul, hs, hA, ← WithZero.exp_add] at h2'
          by_contra hgt
          push Not at hgt
          have : exp (-(s : ℤ) + -(eA : ℤ)) * 1 < exp (-(s : ℤ) + -(eA : ℤ)) * Valued.v (imv x 2) :=
            mul_lt_mul_of_pos_left hgt (by simp)
          rw [mul_one] at this
          have h3' := this.trans_le h2'
          rw [WithZero.exp_lt_exp] at h3'
          omega
      · show Valued.v (nrdLoc _ _ x) = 1
        rw [nrdLoc_eq_nrd]
        have hxe := eq_smul_one_add_pure x hr0
        calc Valued.v (nrd x) = Valued.v (nrd (x.re • (1 + Quat.pure (x.re⁻¹ • imv x)) :
              QuatV (a : F) (b : F) v)) := by rw [← hxe]
          _ = 1 := by
            rw [nrd_smul, map_mul, map_pow, hre, one_pow, one_mul]
            exact valued_nrd_one_add_pure (a := a) (b := b) hs hsm hy'

variable (v a b) in
/-- **$c(\Lambda^{(m)}_v) = K_m$** ($a, b \ne 0$; hypotheses as in `mem_lamCong_iff`): every element of the principal
congruence subgroup is a conjugation by some $u = 1 + y$, $y \in \Lambda'_m$. -/
@[kb "weil1982" "§3.7(a), p. 63"]
theorem map_lamCong {s eA m : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hA : Valued.v Av = exp (-(eA : ℤ))) (h2s : 2 * s < m) (hmA : s + eA ≤ m) (hm : 1 ≤ m) :
    (lamCong v a b m hm).map (conjOrth QF (hQF a b)) = congSub v Q₀ m hm := by
  have hAi := valued_algebraMap_le_one a v
  have hBi := valued_algebraMap_le_one b v
  have hsm : s < m := by omega
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩; exact hu.1
  · intro g hg
    have hgX : ((g : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m := hg
    have hdet : ((g : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv).det = 1 := by
      rcases det_eq_one_or_neg_one QF (Measure.nondegenerate_QF Q₀ (nondegenerate_pureFormO a b ha hb)) g with h | h
      · exact h
      · exfalso
        have := valued_det_sub_one_le v hgX
        rw [h, show (-1 : Fv) - 1 = -2 by ring, Valuation.map_neg, hs, WithZero.exp_le_exp] at this
        omega
    have ha' : (a : F) ≠ 0 := by exact_mod_cast ha
    have hb' : (b : F) ≠ 0 := by exact_mod_cast hb
    obtain ⟨α, hα⟩ := conjSOK_surjective (K := Fv) QF (hQF a b) ha' hb' ⟨g, mem_soSub.mpr hdet⟩
    have hαX : ((conjGL α : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) =
        ((g : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) := by
      rw [← conjSOK_coe QF (hQF a b) α, hα]
    have hr0 : (α : QuatV (a : F) (b : F) v).re ≠ 0 :=
      re_ne_zero_of_conjGL_mem_ballOne hs h2s α (by rw [hαX]; exact hgX)
    set w := Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom
      (Units.mk0 (α : QuatV (a : F) (b : F) v).re⁻¹ (inv_ne_zero hr0)) * α
    have hw := scale_val Av Bv α hr0
    have hwX : ((conjGL w : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) ∈ ballOne v m := by
      rw [conjGL_smul, hαX]; exact hgX
    have hy := mem_latP_of_conjMat_mem_ballOne hAi hBi hs hsm w hw hwX
    refine ⟨w, (mem_lamCong_iff v a b hs hA h2s hmA hm w).mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hw]; simp [Quat.pure]
    · rw [hw]; simpa [imv, Quat.pure] using hy
    · ext : 2
      change ((conjGL w : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) = _
      rw [conjGL_smul, hαX]

end LocalCong


/-! ### $\omega_v(\Lambda^{(m)}_v)$: a box in the coordinates $1, i, j, k$ -/

section Volume

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)

/-- The coordinate sets $\{x : |2x|_v \le q^{-m}\}$ and $\{x : |2ax|_v, |2bx|_v \le q^{-m}\}$. -/
def latTwo (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) : Set (v.adicCompletion F) :=
  {x | Valued.v (2 * x) ≤ exp (-(m : ℤ))}

def latTwoAB (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (A B : v.adicCompletion F) : Set (v.adicCompletion F) :=
  {x | Valued.v (2 * A * x) ≤ exp (-(m : ℤ)) ∧ Valued.v (2 * B * x) ≤ exp (-(m : ℤ))}

theorem measurableSet_latTwo (m : ℕ) : MeasurableSet (latTwo v m) := by
  have : latTwo v m = (fun x : Fv => 2 * x) ⁻¹' (Analysis.latticeV v m : Set Fv) := by
    ext x; simp [latTwo, Analysis.mem_latticeV]
  rw [this]
  exact (Analysis.measurableSet_latticeV v m).preimage (continuous_const.mul continuous_id).measurable

theorem measurableSet_latTwoAB (m : ℕ) (A B : Fv) : MeasurableSet (latTwoAB v m A B) := by
  have : latTwoAB v m A B = (fun x : Fv => 2 * A * x) ⁻¹' (Analysis.latticeV v m : Set Fv) ∩
      (fun x : Fv => 2 * B * x) ⁻¹' (Analysis.latticeV v m : Set Fv) := by
    ext x; simp [latTwoAB, Analysis.mem_latticeV]
  rw [this]
  exact ((Analysis.measurableSet_latticeV v m).preimage (continuous_const.mul continuous_id).measurable).inter
    ((Analysis.measurableSet_latticeV v m).preimage (continuous_const.mul continuous_id).measurable)

variable (v a b) in
/-- **$\omega_v(\Lambda^{(m)}_v) = \operatorname{vol}(\mathfrak o_v^\times)\cdot\operatorname{vol}(L)^2\cdot
\operatorname{vol}(L')$** for the self-dual coordinate measure, $L = \{|2x| \le q^{-m}\}$, $L' = \{|2ax|, |2bx| \le
q^{-m}\}$ (on $\Lambda^{(m)}_v$ the norm is a unit, so $\omega_v = dx_v$ there). -/
theorem omegaQuatV_lamCong {s eA m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hA : Valued.v Av = exp (-(eA : ℤ))) (h2s : 2 * s < m) (hmA : s + eA ≤ m) (hm : 1 ≤ m) :
    omegaQuatV v (a : F) (b : F) (lamCong v a b m hm) =
      Analysis.selfDualV v (unitsV v) * Analysis.selfDualV v (latTwo v m) ^ 2 *
        Analysis.selfDualV v (latTwoAB v m Av Bv) := by
  rw [pow_two, ← mul_assoc]
  set T : Set (Fin 4 → Fv) := Set.univ.pi ![unitsV v, latTwo v m, latTwo v m, latTwoAB v m Av Bv]
  have hT : ∀ x : QuatV (a : F) (b : F) v, quatLocCoord _ _ x ∈ T ↔
      Valued.v x.re = 1 ∧ imv x ∈ latP v m Av Bv := by
    intro x
    simp only [T, Set.mem_univ_pi, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
    simp [QuaternionAlgebra.linearEquivTuple, unitsV, latTwo, latTwoAB, latP, imv]
    tauto
  have hmem := mem_lamCong_iff v a b hs hA h2s hmA hm
  have hset : (lamCong v a b m hm : Set (QuatV (a : F) (b : F) v)ˣ) =
      Units.val ⁻¹' (quatLocCoord _ _ ⁻¹' T) := by
    ext u; simp only [SetLike.mem_coe, Set.mem_preimage, hT, hmem]
  have hTm : MeasurableSet T := MeasurableSet.univ_pi fun i => by
    fin_cases i
    · exact measurableSet_unitsV v
    · exact measurableSet_latTwo m
    · exact measurableSet_latTwo m
    · exact measurableSet_latTwoAB m _ _
  have hLm : MeasurableSet (lamCong v a b m hm : Set (QuatV (a : F) (b : F) v)ˣ) := by
    rw [hset]
    exact (hTm.preimage (continuous_quatLocCoord _ _).measurable).preimage Units.continuous_val.measurable
  have h1 : ∀ u ∈ (lamCong v a b m hm : Set (QuatV (a : F) (b : F) v)ˣ),
      distribHaarChar (QuatV (a : F) (b : F) v) u = 1 := by
    intro u hu
    have hu' : nrdLocUnit _ _ u ∈ unitsVSub v := ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w)
      (fun w => valued_algebraMap_le_one b w) u).mp hu.2).2
    rw [distribHaarChar_quatLoc, distribHaarChar_eq_one_of_mem_unitsVSub hu', one_pow]
  rw [omegaQuatV, omegaQuatLoc, unitsHaar_apply_of_forall_eq_one (isOpenEmbedding_val_quatLoc _ _)
    (continuous_distribHaarChar_quatLoc _ _ (continuous_distribHaarChar_adic v)) _ hLm h1]
  have himg : Units.val '' (lamCong v a b m hm : Set (QuatV (a : F) (b : F) v)ˣ) = quatLocCoord _ _ ⁻¹' T := by
    rw [hset]
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx' := (hT x).mp hx
      have hn : nrdLoc _ _ x ≠ 0 := by
        intro h0
        have hr0 : x.re ≠ 0 := fun h => by rw [h, map_zero] at hx'; exact zero_ne_one hx'.1
        have := valued_nrd_one_add_pure (a := a) (b := b) hs (by omega)
          ((smul_mem_latP_iff (r := x.re⁻¹) (by rw [map_inv₀, hx'.1, inv_one]) _).mpr hx'.2)
        rw [nrdLoc_eq_nrd, eq_smul_one_add_pure x hr0, nrd_smul] at h0
        rcases mul_eq_zero.mp h0 with h | h
        · exact hr0 (pow_eq_zero_iff two_ne_zero |>.mp h)
        · rw [h, map_zero] at this; exact zero_ne_one this
      obtain ⟨u, rfl⟩ := (isUnit_iff_nrdLoc_ne_zero _ _ x).mpr hn
      exact ⟨u, hx, rfl⟩
  rw [himg, quatLocVol, Measure.map_apply (quatLocCLE _ _).symm.continuous.measurable
    (hTm.preimage (continuous_quatLocCoord _ _).measurable)]
  have hpre : (quatLocCLE _ _).symm ⁻¹' (quatLocCoord (Av) (Bv) ⁻¹' T) = T := by
    ext c
    simp only [Set.mem_preimage]
    change (quatLocCoord _ _) ((quatLocCoord _ _).symm c) ∈ T ↔ c ∈ T
    rw [LinearEquiv.apply_symm_apply]
  rw [hpre, Measure.pi_pi, Fin.prod_univ_four]
  rfl

end Volume


/-! ### The local ratio $r_v = |8a^3b^3|_v\,\mathrm{vol}(\mathfrak o_v)^3$ at every finite place -/

section Ratio

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)

open LocalDensity LerayPadic LocalZeta

omit [NumberField F] in
theorem hessian_pureFormO (a b : 𝓞 F) :
    (QuatZeta.pureFormO a b).hessian = Matrix.diagonal ![-2 * a, -2 * b, 2 * (a * b)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuadForm.hessian, QuatZeta.pureFormO, QuadForm.diag, Matrix.diagonal, map_ofNat] <;> ring

theorem hessian_Qp_pureFormO (a b : 𝓞 F) : (NF.Qp v (QuatZeta.pureFormO a b)).hessian =
    Matrix.diagonal (fun i => NF.ι v (![-2 * a, -2 * b, 2 * (a * b)] i)) := by
  rw [NF.Qp, QuadForm.hessian_map, hessian_pureFormO, Matrix.diagonal_map (map_zero _)]

theorem coe_ι (x : 𝓞 F) : ((NF.ι v x : 𝔬) : Fv) = algebraMap F Fv (x : F) := by
  rw [← IsScalarTower.algebraMap_apply]; rfl

/-- $\pi^e \,\|\, z$ from $|z|_v = q^{-e}$. -/
theorem pow_dvd_of_valued {z : 𝔬} {e : ℕ} (h : Valued.v (z : Fv) = exp (-(e : ℤ))) :
    πv ^ e ∣ z ∧ ¬ πv ^ (e + 1) ∣ z := by
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton, NF.mem_span_π_pow, NF.mem_span_π_pow, h]
  refine ⟨le_rfl, ?_⟩
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem exp_mul_le_iff (y : ℤᵐ⁰) (z w : ℤ) : exp z * y ≤ exp w ↔ y ≤ exp (w - z) := by
  rw [mul_comm, ← le_div_iff₀ (zero_lt_iff.mpr (WithZero.exp_ne_zero)), ← WithZero.exp_sub]

theorem latTwo_eq {s m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s ≤ m) :
    latTwo v m = (Analysis.latticeV v ((m - s : ℕ) : ℤ) : Set Fv) := by
  ext x
  simp only [latTwo, Set.mem_ofPred_eq, SetLike.mem_coe, Analysis.mem_latticeV, map_mul, hs, exp_mul_le_iff]
  rw [show -(m : ℤ) - -(s : ℤ) = -((m - s : ℕ) : ℤ) by push_cast [Nat.cast_sub hsm]; ring]

theorem latTwoAB_eq {s eA eB m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hA : Valued.v Av = exp (-(eA : ℤ))) (hB : Valued.v Bv = exp (-(eB : ℤ))) (hm : s + min eA eB ≤ m) :
    latTwoAB v m Av Bv = (Analysis.latticeV v ((m - s - min eA eB : ℕ) : ℤ) : Set Fv) := by
  ext x
  simp only [latTwoAB, Set.mem_ofPred_eq, SetLike.mem_coe, Analysis.mem_latticeV, map_mul, hs, hA, hB,
    ← WithZero.exp_add, exp_mul_le_iff]
  have key : ∀ e : ℕ, -(m : ℤ) - (-(s : ℤ) + -(e : ℤ)) = -(m : ℤ) + s + e := fun e => by ring
  simp only [key]
  rcases le_total eA eB with h | h
  · rw [min_eq_left h, show -((m - s - eA : ℕ) : ℤ) = -(m : ℤ) + s + eA by omega]
    exact ⟨fun hh => hh.1, fun hh => ⟨hh, hh.trans (WithZero.exp_le_exp.mpr (by omega))⟩⟩
  · rw [min_eq_right h, show -((m - s - eB : ℕ) : ℤ) = -(m : ℤ) + s + eB by omega]
    exact ⟨fun hh => hh.2, fun hh => ⟨hh.trans (WithZero.exp_le_exp.mpr (by omega)), hh⟩⟩

theorem selfDualV_latticeV_nat (k : ℕ) :
    Analysis.selfDualV v (Analysis.latticeV v (k : ℤ)) =
      Analysis.selfDualV v (Analysis.latticeV v 0) / (DVR.q 𝔬 : ℝ≥0∞) ^ k := by
  have h := measure_latticeV_zero v (Analysis.selfDualV v) k
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (q_pos v).ne')
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [h, mul_comm, ENNReal.mul_div_cancel_right hq0 hqt]

theorem qpow_cancel {q : ℝ≥0∞} (h0 : q ≠ 0) (ht : q ≠ ⊤) (A B t : ℕ) :
    q ^ (A + t) * q⁻¹ ^ (B + t) = q ^ A * q⁻¹ ^ B := by
  rw [pow_add, pow_add]
  calc q ^ A * q ^ t * (q⁻¹ ^ B * q⁻¹ ^ t) = q ^ A * q⁻¹ ^ B * (q * q⁻¹) ^ t := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel h0 ht, one_pow, mul_one]

variable (v a b) in
/-- **The local ratio at every finite place** (dyadic and ramified places included). With $|2|_v = q^{-s}$,
$|a|_v = q^{-e_a}$, $|b|_v = q^{-e_b}$ and $m \ge 2d+1$, $d = 3s + 2e_a + 2e_b$ ($\pi^d \,\|\, \det H_{Q_0}$):
$$\omega_v(\Lambda^{(m)}_v)\cdot q^{3(s+e_a+e_b)} = \omega_v(\mathfrak o_v^\times)\cdot\mathrm{vol}(\mathfrak o_v)^3\cdot
\mu_v(K_m),$$
where $\Lambda^{(m)}_v = c^{-1}(K_m)\cap\Lambda_v^\times$ (`lamCong`; $c(\Lambda^{(m)}_v) = K_m$ by `map_lamCong`),
$\omega_v$ = $\|\operatorname{nrd}\|_v^{-2}dx_v$ and $|x|_v^{-1}dx_v$ (self-dual $dx_v$), $\mu_v$ =
gauge-form measure. So Weil's quotient measure $\omega_v^{D^\times}/\omega_v^{G_m}$ on $PD^\times(F_v)$ and $\mu_v$ on
$SO(D^0)(F_v)$ differ by $r_v = |8a^3b^3|_v\,\mathrm{vol}(\mathfrak o_v)^3 = |8a^3b^3|_v\,|\mathfrak d_v|^{3/2}$ (Weil's
Thm 2.3.1: the ratio of two $F$-rational gauge forms is a global constant $c = 8a^3b^3$). -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (local ratios of gauge-form measures) [unverified]"]
theorem omegaQuatV_lamCong_mul {s eA eB m : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hA : Valued.v Av = exp (-(eA : ℤ)))
    (hB : Valued.v Bv = exp (-(eB : ℤ))) (hm : 2 * (3 * s + 2 * eA + 2 * eB) + 1 ≤ m) :
    omegaQuatV v (a : F) (b : F) (lamCong v a b m (by omega)) * (DVR.q 𝔬 : ℝ≥0∞) ^ (3 * (s + eA + eB)) =
      omegaV v (unitsVSub v) * Analysis.selfDualV v (Analysis.latticeV v 0) ^ 3 *
        Measure.muLoc v (QuatZeta.pureFormO a b) 1 (congSub v (QuatZeta.pureFormO a b) m (by omega) : Set _) := by
  set d := 3 * s + 2 * eA + 2 * eB
  set j := 2 * d + 1
  set μ := min eA eB
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast (q_pos v).ne'
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- the quaternion side
  rw [omegaQuatV_lamCong v a b hs hA (by omega) (by omega) (by omega), latTwo_eq hs (by omega),
    latTwoAB_eq hs hA hB (by omega), selfDualV_latticeV_nat, selfDualV_latticeV_nat, ← omegaV_unitsVSub]
  -- the orthogonal side
  set h : Fin 3 → 𝔬 := fun i => NF.ι v (![-2 * a, -2 * b, 2 * (a * b)] i)
  set e : Fin 3 → ℕ := ![s + eA, s + eB, s + eA + eB]
  have he0 : e 0 = s + eA := rfl
  have he1 : e 1 = s + eB := rfl
  have he2 : e 2 = s + eA + eB := rfl
  have hval : ∀ i, Valued.v ((h i : 𝔬) : Fv) = exp (-(e i : ℤ)) := by
    intro i
    fin_cases i
    · show Valued.v ((NF.ι v (-2 * a) : 𝔬) : Fv) = exp (-((s + eA : ℕ) : ℤ))
      rw [coe_ι, show ((-2 * a : 𝓞 F) : F) = -(2 * (a : F)) by
        rw [show ((-2 * a : 𝓞 F) : F) = algebraMap (𝓞 F) F (-2 * a) from rfl, map_mul, map_neg, map_ofNat]; ring, map_neg, map_mul, map_ofNat,
        Valuation.map_neg, map_mul, hs, hA, ← WithZero.exp_add]
      congr 1; push_cast; ring
    · show Valued.v ((NF.ι v (-2 * b) : 𝔬) : Fv) = exp (-((s + eB : ℕ) : ℤ))
      rw [coe_ι, show ((-2 * b : 𝓞 F) : F) = -(2 * (b : F)) by
        rw [show ((-2 * b : 𝓞 F) : F) = algebraMap (𝓞 F) F (-2 * b) from rfl, map_mul, map_neg, map_ofNat]; ring, map_neg, map_mul, map_ofNat,
        Valuation.map_neg, map_mul, hs, hB, ← WithZero.exp_add]
      congr 1; push_cast; ring
    · show Valued.v ((NF.ι v (2 * (a * b)) : 𝔬) : Fv) = exp (-((s + eA + eB : ℕ) : ℤ))
      rw [coe_ι, show ((2 * (a * b) : 𝓞 F) : F) = 2 * ((a : F) * (b : F)) by
        rw [show ((2 * (a * b) : 𝓞 F) : F) = algebraMap (𝓞 F) F (2 * (a * b)) from rfl, map_mul, map_mul,
          map_ofNat], map_mul, map_mul,
        map_ofNat, map_mul, map_mul, hs, hA, hB, ← WithZero.exp_add, ← WithZero.exp_add]
      congr 1; push_cast; ring
  have hdiv := fun i => pow_dvd_of_valued (hval i)
  have hdet : Valued.v (((NF.Qp v (QuatZeta.pureFormO a b)).hessian.det : 𝔬) : Fv) = exp (-(d : ℤ)) := by
    rw [hessian_Qp_pureFormO, Matrix.det_diagonal, Fin.prod_univ_three]
    change Valued.v ((h 0 : Fv) * (h 1 : Fv) * (h 2 : Fv)) = _
    rw [map_mul, map_mul, hval 0, hval 1, hval 2, ← WithZero.exp_add, ← WithZero.exp_add, he0, he1, he2]
    congr 1; simp only [d]; push_cast; ring
  obtain ⟨hd, hd'⟩ := pow_dvd_of_valued hdet
  have hQ := nondegenerate_pureFormO a b ha hb
  rw [muLoc_congSub_eq v _ hQ m (by omega) d j hd hd' le_rfl (by omega),
    card_kerD_diag3 v _ h (hessian_Qp_pureFormO a b) j e (fun i => (hdiv i).1) (fun i => (hdiv i).2)
      (fun i => by
        have : e i ≤ s + eA + eB := by fin_cases i <;> simp [e] <;> omega
        omega)]
  have hmin02 : min (e 0) (e 2) = s + eA := by rw [he0, he2]; exact min_eq_left (by omega)
  have hmin12 : min (e 1) (e 2) = s + eB := by rw [he1, he2]; exact min_eq_left (by omega)
  have hmin01 : min (e 0) (e 1) = s + μ := by rw [he0, he1, min_add_add_left]
  rw [hmin02, hmin12, hmin01, he0, he1, he2]
  simp only [Nat.cast_mul, Nat.cast_pow]
  -- arithmetic in `ℝ≥0∞`
  set q := (DVR.q 𝔬 : ℝ≥0∞)
  set U := omegaV v (unitsVSub v)
  set ν := Analysis.selfDualV v (Analysis.latticeV v 0)
  simp only [div_eq_mul_inv, ENNReal.inv_pow]
  have e1 : U * (ν * q⁻¹ ^ (m - s)) ^ 2 * (ν * q⁻¹ ^ (m - s - μ)) * q ^ (3 * (s + eA + eB)) =
      U * ν ^ 3 * (q ^ (3 * (s + eA + eB)) * q⁻¹ ^ ((m - s) + (m - s) + (m - s - μ))) := by
    simp only [pow_add]; ring
  have e2 : U * ν ^ 3 * (q ^ (s + eA) * q ^ (s + eB) * q ^ (s + eA + eB) *
      (q ^ (s + μ) * q ^ j * (q ^ (s + eA) * q ^ j) * (q ^ (s + eB) * q ^ j)) * q⁻¹ ^ ((m + j) * (3 * (3 - 1) / 2))) =
      U * ν ^ 3 * (q ^ ((s + eA) + (s + eB) + (s + eA + eB) + (s + μ + j) + (s + eA + j) + (s + eB + j)) *
        q⁻¹ ^ ((m + j) * (3 * (3 - 1) / 2))) := by
    simp only [pow_add]; ring
  rw [e1, e2]
  congr 1
  have hμ : μ ≤ eA := min_le_left _ _
  rw [show (s + eA) + (s + eB) + (s + eA + eB) + (s + μ + j) + (s + eA + j) + (s + eB + j) =
      3 * (s + eA + eB) + (3 * s + μ + 3 * j) by ring,
    show (m + j) * (3 * (3 - 1) / 2) = ((m - s) + (m - s) + (m - s - μ)) + (3 * s + μ + 3 * j) by
      simp only [show 3 * (3 - 1) / 2 = 3 by norm_num]; omega,
    qpow_cancel hq0 hqt]

end Ratio

end QuadFormsKB.Tamagawa.Measure.Weil
