/-
# O'Meara §101A: the orthogonal group over a valuated field

**Layer:** $V = F_\mathfrak p^n$ for a finite place $\mathfrak p$ of a number field $F$, with the standard base
$e_0, \dots, e_{n-1}$ (O'Meara's $x_1, \dots, x_n$; the shift of indices does not matter here), and the quadratic
form $Q$ = `Q : QuadForm F n`; isometries are `orthGroup Q F_𝔭` (`Lattices/Genus.lean`).

O'Meara (1973 printing, §101A, pp. 285–289) works over an arbitrary valuated field with a real-valued absolute value
$\lvert\cdot\rvert_\mathfrak p$. Here the field is a completion $F_\mathfrak p$ at a finite place, and the absolute
value is Mathlib's valuation `Valued.v : F_𝔭 → ℤᵐ⁰` (values $0$ and $\exp(k)$, $k \in \mathbb Z$), which is an
order-preserving, multiplicative reparametrization of $\lvert\cdot\rvert_\mathfrak p$; all statements below are
inequalities and equalities between such values, so nothing is lost. Archimedean places are not treated.

**Defines**
* `vecNorm v x` $= \lVert x\rVert_\mathfrak p = \max_i \lvert x_i\rvert_\mathfrak p$ for $x \in F_\mathfrak p^n$;
* `matNorm v A` $= \lVert A\rVert_\mathfrak p = \max_{i,j} \lvert a_{ij}\rvert_\mathfrak p$ for an $n \times n$ matrix.

**Proves**
* the norm axioms in their ultrametric form, and local constancy away from $0$ (§101A, p. 285): `vecNorm_eq_zero_iff`,
  `vecNorm_smul`, `vecNorm_add_le`, `vecNorm_add_eq_max_of_ne`, `vecNorm_eventually_eq`;
* the multiplicative laws (p. 286–287): `vecNorm_mulVec_le`, `matNorm_mul_le`;
* Example 101:1 (change of base, pp. 287–288): `vecNorm_le_matNorm_mul_vecNorm_inv`, `vecNorm_inv_mulVec_le`,
  `matNorm_conj_le`, and for a base of the global space, equality at almost all $\mathfrak p$:
  `eventually_vecNorm_inv_mulVec_eq`, `eventually_matNorm_conj_eq`;
* Example 101:3 (p. 288): $O^+(V_\mathfrak p)$ is open and closed in $O(V_\mathfrak p)$ (`isClopen_soSub`);
* Example 101:4 (i) (p. 288): the isometries $\sigma$ with $\lVert\sigma\rVert = 1$ are exactly the elements of
  $O(M)$, $M = \mathfrak o_\mathfrak p^n$ (`mem_stdStab_iff_matNorm_le_one`, `mem_stdStab_iff_matNorm_eq_one`).
  Parts (ii) and (iii) are `Lattices.exists_mem_nhds_locAct_eq` (cited in `CitationsX.lean`).
-/
import QuadFormsKB.Lattices.SAApprox
import QuadFormsKB.Tamagawa.LocalVolume

open NumberField IsDedekindDomain Matrix WithZero Topology Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Norms

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-! ### The norm on $V_\mathfrak p$ -/

/-- **The norm** $\lVert x\rVert_\mathfrak p = \max_i \lvert x_i\rvert_\mathfrak p$ of a vector
$x = \sum_i x_i e_i \in F_\mathfrak p^n$ with respect to the standard base (O'Meara 1973, §101A, p. 285), with values in
`ℤᵐ⁰` (`Valued.v`); for $n = 0$ it is $0$. -/
@[kb "omeara1963" "§101A, p. 285 (the norm ‖x‖_𝔭 with respect to a base)"]
def vecNorm (x : Fin n → Fv) : ℤᵐ⁰ := Finset.univ.sup fun i => Valued.v (x i)

/-- **The norm of a matrix** $\lVert (a_{ij})\rVert_\mathfrak p = \max_{i,j} \lvert a_{ij}\rvert_\mathfrak p$
(O'Meara 1973, §101A, pp. 286–287; it is the norm of the linear map with this matrix in the standard base). -/
@[kb "omeara1963" "§101A, pp. 286–287 (the norm ‖σ‖_𝔭 of a linear map, of a matrix)"]
def matNorm (A : Matrix (Fin n) (Fin n) Fv) : ℤᵐ⁰ := Finset.univ.sup fun i => vecNorm v (A i)

variable {v}

theorem vecNorm_le_iff {x : Fin n → Fv} {c : ℤᵐ⁰} : vecNorm v x ≤ c ↔ ∀ i, Valued.v (x i) ≤ c := by
  simp [vecNorm, Finset.sup_le_iff]

theorem le_vecNorm (x : Fin n → Fv) (i : Fin n) : Valued.v (x i) ≤ vecNorm v x :=
  vecNorm_le_iff.mp le_rfl i

theorem matNorm_le_iff {A : Matrix (Fin n) (Fin n) Fv} {c : ℤᵐ⁰} :
    matNorm v A ≤ c ↔ ∀ i j, Valued.v (A i j) ≤ c := by
  simp [matNorm, Finset.sup_le_iff, vecNorm_le_iff]

theorem le_matNorm (A : Matrix (Fin n) (Fin n) Fv) (i j : Fin n) : Valued.v (A i j) ≤ matNorm v A :=
  matNorm_le_iff.mp le_rfl i j

/-- The maximum is attained (for $n \ge 1$). -/
theorem exists_vecNorm_eq [NeZero n] (x : Fin n → Fv) : ∃ i, vecNorm v x = Valued.v (x i) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun i => Valued.v (x i)
  exact ⟨i, hi⟩

theorem vecNorm_of_eq_zero (hn : n = 0) (x : Fin n → Fv) : vecNorm v x = 0 := by
  subst hn; simp [vecNorm]

/-- **$\lVert x\rVert = 0$ if and only if $x = 0$** (O'Meara 1973, §101A, p. 285, property (1)). -/
@[kb "omeara1963" "§101A, p. 285 (norm property (1))"]
theorem vecNorm_eq_zero_iff {x : Fin n → Fv} : vecNorm v x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have := le_vecNorm (v := v) x i
    rw [h] at this
    exact (Valuation.zero_iff _).mp (le_antisymm this zero_le)
  · rintro rfl
    exact le_antisymm (vecNorm_le_iff.mpr fun i => by simp) zero_le

/-- **$\lVert \alpha x\rVert = \lvert\alpha\rvert\,\lVert x\rVert$** (O'Meara 1973, §101A, p. 285, property (2)). -/
@[kb "omeara1963" "§101A, p. 285 (norm property (2))"]
theorem vecNorm_smul (a : Fv) (x : Fin n → Fv) : vecNorm v (a • x) = Valued.v a * vecNorm v x := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [vecNorm_of_eq_zero hn, vecNorm_of_eq_zero hn, mul_zero]
  · have : NeZero n := ⟨hn.ne'⟩
    refine le_antisymm (vecNorm_le_iff.mpr fun i => ?_) ?_
    · rw [Pi.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_mul_right (le_vecNorm x i) _
    · obtain ⟨i, hi⟩ := exists_vecNorm_eq (v := v) x
      rw [hi, ← map_mul]
      exact le_vecNorm (a • x) i

/-- **The ultrametric inequality** $\lVert x + y\rVert \le \max(\lVert x\rVert, \lVert y\rVert)$ (O'Meara 1973, §101A,
p. 285; this implies property (3), the triangle inequality). -/
@[kb "omeara1963" "§101A, p. 285 (‖x + y‖ ≤ max(‖x‖, ‖y‖))"]
theorem vecNorm_add_le (x y : Fin n → Fv) : vecNorm v (x + y) ≤ max (vecNorm v x) (vecNorm v y) :=
  vecNorm_le_iff.mpr fun i => (Valuation.map_add _ _ _).trans (max_le_max (le_vecNorm x i) (le_vecNorm y i))

theorem vecNorm_add_eq_of_lt {x y : Fin n → Fv} (h : vecNorm v y < vecNorm v x) :
    vecNorm v (x + y) = vecNorm v x := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [vecNorm_of_eq_zero hn, vecNorm_of_eq_zero hn]
  have : NeZero n := ⟨hn.ne'⟩
  refine le_antisymm ((vecNorm_add_le x y).trans (max_eq_left h.le).le) ?_
  obtain ⟨i, hi⟩ := exists_vecNorm_eq (v := v) x
  have hlt : Valued.v (y i) < Valued.v (x i) := (le_vecNorm y i).trans_lt (hi ▸ h)
  rw [hi, ← Valuation.map_add_eq_of_lt_left _ hlt]
  exact le_vecNorm (x + y) i

/-- **$\lVert x + y\rVert = \max(\lVert x\rVert, \lVert y\rVert)$ if $\lVert x\rVert \ne \lVert y\rVert$**
(O'Meara 1973, §101A, p. 285). -/
@[kb "omeara1963" "§101A, p. 285 (‖x + y‖ = max(‖x‖, ‖y‖) if ‖x‖ ≠ ‖y‖)"]
theorem vecNorm_add_eq_max_of_ne {x y : Fin n → Fv} (h : vecNorm v x ≠ vecNorm v y) :
    vecNorm v (x + y) = max (vecNorm v x) (vecNorm v y) := by
  rcases h.lt_or_gt with h | h
  · rw [add_comm, vecNorm_add_eq_of_lt h, max_eq_right h.le]
  · rw [vecNorm_add_eq_of_lt h, max_eq_left h.le]

/-- **The norm is locally constant away from $0$:** every $x_0 \ne 0$ has a neighbourhood throughout which
$\lVert x\rVert = \lVert x_0\rVert$ (O'Meara 1973, §101A, p. 285). -/
@[kb "omeara1963" "§101A, p. 285 (‖x‖ = ‖x₀‖ near x₀ ≠ 0)"]
theorem vecNorm_eventually_eq {x₀ : Fin n → Fv} (hx₀ : x₀ ≠ 0) :
    ∀ᶠ x in 𝓝 x₀, vecNorm v x = vecNorm v x₀ := by
  have hc : vecNorm v x₀ ≠ 0 := fun h => hx₀ (vecNorm_eq_zero_iff.mp h)
  set k : ℤ := 1 - log (vecNorm v x₀)
  filter_upwards [ball_add_mem_nhds v x₀ k] with x hx
  have hlt : vecNorm v (x - x₀) < vecNorm v x₀ := by
    refine lt_of_le_of_lt (vecNorm_le_iff.mpr fun i => (mem_ball v).mp hx i) ?_
    rw [← exp_log hc, exp_lt_exp]; omega
  rw [show x = x₀ + (x - x₀) by abel]
  exact vecNorm_add_eq_of_lt hlt

/-! ### Matrices -/

/-- **$\lVert \sigma x\rVert \le \lVert\sigma\rVert\,\lVert x\rVert$** in the non-archimedean case (O'Meara 1973,
§101A, pp. 286–287). -/
@[kb "omeara1963" "§101A, pp. 286–287 (‖σx‖ ≤ ‖σ‖‖x‖, non-archimedean)"]
theorem vecNorm_mulVec_le (A : Matrix (Fin n) (Fin n) Fv) (x : Fin n → Fv) :
    vecNorm v (A *ᵥ x) ≤ matNorm v A * vecNorm v x := by
  refine vecNorm_le_iff.mpr fun i => ?_
  rw [mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_mul' (le_matNorm A i j) (le_vecNorm x j)

/-- **$\lVert \sigma\tau\rVert \le \lVert\sigma\rVert\,\lVert\tau\rVert$** in the non-archimedean case (O'Meara 1973,
§101A, p. 287). -/
@[kb "omeara1963" "§101A, p. 287 (‖στ‖ ≤ ‖σ‖‖τ‖, non-archimedean)"]
theorem matNorm_mul_le (A B : Matrix (Fin n) (Fin n) Fv) :
    matNorm v (A * B) ≤ matNorm v A * matNorm v B := by
  refine matNorm_le_iff.mpr fun i j => ?_
  rw [mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (le_matNorm A i k) (le_matNorm B k j)

/-- $\lvert\det A\rvert \le \lVert A\rVert^n$. -/
theorem valued_det_le (A : Matrix (Fin n) (Fin n) Fv) : Valued.v A.det ≤ matNorm v A ^ n := by
  rw [det_apply]
  refine Valuation.map_sum_le _ fun π _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, map_mul]
  have hs : Valued.v ((((Equiv.Perm.sign π : ℤˣ) : ℤ)) : Fv) ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  calc Valued.v ((((Equiv.Perm.sign π : ℤˣ) : ℤ)) : Fv) * Valued.v (∏ i, A (π i) i)
      ≤ 1 * Valued.v (∏ i, A (π i) i) := mul_le_mul_left hs _
    _ = ∏ i, Valued.v (A (π i) i) := by rw [one_mul, map_prod]
    _ ≤ ∏ _i : Fin n, matNorm v A := Finset.prod_le_prod' fun i _ => le_matNorm A _ _
    _ = matNorm v A ^ n := by simp

/-- An integral matrix with unit determinant has an integral inverse. -/
theorem matNorm_inv_le_one {A : Matrix (Fin n) (Fin n) Fv} (hA : matNorm v A ≤ 1)
    (hdet : Valued.v A.det = 1) : matNorm v A⁻¹ ≤ 1 := by
  have hd0 : A.det ≠ 0 := fun h => by rw [h, map_zero] at hdet; exact zero_ne_one hdet
  refine matNorm_le_iff.mpr fun i j => ?_
  rw [inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv', map_inv₀, hdet, inv_one, one_mul,
    adjugate_apply]
  refine (valued_det_le (v := v) _).trans ?_
  refine pow_le_one' ((matNorm_le_iff (v := v)).mpr fun k l => ?_) n
  by_cases hk : k = j
  · subst hk
    rw [updateRow_self]
    by_cases hl : l = i
    · subst hl; simp
    · simp [hl]
  · rw [updateRow_ne hk]; exact (le_matNorm A k l).trans hA

/-- Integral matrices are exactly those mapping $\mathfrak o_\mathfrak p^n$ into itself. -/
theorem matNorm_le_one_iff (A : Matrix (Fin n) (Fin n) Fv) :
    matNorm v A ≤ 1 ↔ ∀ y ∈ std v, A *ᵥ y ∈ std v := by
  constructor
  · intro hA y hy
    have hy' : vecNorm v y ≤ 1 := vecNorm_le_iff.mpr fun i => by simpa using (mem_ball v).mp hy i
    have := (vecNorm_mulVec_le (v := v) A y).trans (mul_le_one' hA hy')
    exact (mem_ball v).mpr fun i => by simpa using (le_vecNorm _ i).trans this
  · intro h
    refine matNorm_le_iff.mpr fun i j => ?_
    have hy : (Pi.single j 1 : Fin n → Fv) ∈ std v := (mem_ball v).mpr fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    have := (mem_ball v).mp (h _ hy) i
    simpa [mulVec_single] using this

/-! ### Example 101:1: change of base -/

/-- **Example 101:1, first inequality** (O'Meara 1973, pp. 287–288, non-archimedean case). Let the new base
$x'_0, \dots, x'_{n-1}$ be the columns of $P \in \mathrm{GL}_n(F_\mathfrak p)$, so that the coordinates of $x$ in the
new base are $P^{-1}x$ and $\lVert x\rVert' = \lVert P^{-1}x\rVert$. Then $\lVert x\rVert \le \lVert P\rVert\,\lVert x\rVert'$
(O'Meara: $\lVert x\rVert/\lVert a_{ij}\rVert \le \lVert x\rVert'$). -/
@[kb "omeara1963" "§101A, 101:1, pp. 287–288 (change of base, non-archimedean)"]
theorem vecNorm_le_matNorm_mul_vecNorm_inv (P : GL (Fin n) Fv) (x : Fin n → Fv) :
    vecNorm v x ≤ matNorm v P.val * vecNorm v ((P⁻¹).val *ᵥ x) := by
  conv_lhs => rw [← mulVec_inv_mulVec P x]
  exact vecNorm_mulVec_le _ _

/-- **Example 101:1, second inequality** (O'Meara 1973, pp. 287–288): $\lVert x\rVert' \le \lVert P^{-1}\rVert\,\lVert x\rVert$
(O'Meara: $\lVert x\rVert' \le \lVert b_{ij}\rVert\,\lVert x\rVert$). -/
@[kb "omeara1963" "§101A, 101:1, pp. 287–288 (change of base, non-archimedean)"]
theorem vecNorm_inv_mulVec_le (P : GL (Fin n) Fv) (x : Fin n → Fv) :
    vecNorm v ((P⁻¹).val *ᵥ x) ≤ matNorm v (P⁻¹).val * vecNorm v x :=
  vecNorm_mulVec_le _ _

/-- **Example 101:1 for linear maps** (O'Meara 1973, pp. 287–288): the matrix of $\sigma$ in the new base is
$P^{-1}\sigma P$, and $\lVert\sigma\rVert' = \lVert P^{-1}\sigma P\rVert \le \lVert P^{-1}\rVert\,\lVert\sigma\rVert\,\lVert P\rVert$
(the other inequality is the same statement for $P^{-1}$). -/
@[kb "omeara1963" "§101A, 101:1, pp. 287–288 (change of base for ‖σ‖)"]
theorem matNorm_conj_le (P : GL (Fin n) Fv) (A : Matrix (Fin n) (Fin n) Fv) :
    matNorm v ((P⁻¹).val * A * P.val) ≤ matNorm v (P⁻¹).val * matNorm v A * matNorm v P.val :=
  (matNorm_mul_le _ _).trans (mul_le_mul_left (matNorm_mul_le _ _) _)

/-- If $P$ and $P^{-1}$ are integral, the norms with respect to the columns of $P$ are the standard norms. -/
theorem matNorm_conj_eq {P : GL (Fin n) Fv} (h1 : matNorm v P.val ≤ 1) (h2 : matNorm v (P⁻¹).val ≤ 1)
    (A : Matrix (Fin n) (Fin n) Fv) : matNorm v ((P⁻¹).val * A * P.val) = matNorm v A := by
  refine le_antisymm ((matNorm_conj_le P A).trans ?_) ?_
  · calc matNorm v (P⁻¹).val * matNorm v A * matNorm v P.val ≤ 1 * matNorm v A * 1 :=
          mul_le_mul' (mul_le_mul_left h2 _) h1
      _ = matNorm v A := by rw [one_mul, mul_one]
  · have e : A = P.val * ((P⁻¹).val * A * P.val) * (P⁻¹).val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    conv_lhs => rw [e]
    calc matNorm v (P.val * ((P⁻¹).val * A * P.val) * (P⁻¹).val)
        ≤ matNorm v P.val * matNorm v ((P⁻¹).val * A * P.val) * matNorm v (P⁻¹).val :=
          (matNorm_mul_le _ _).trans (mul_le_mul_left (matNorm_mul_le _ _) _)
      _ ≤ 1 * matNorm v ((P⁻¹).val * A * P.val) * 1 := mul_le_mul' (mul_le_mul_left h1 _) h2
      _ = _ := by rw [one_mul, mul_one]

theorem vecNorm_inv_mulVec_eq {P : GL (Fin n) Fv} (h1 : matNorm v P.val ≤ 1) (h2 : matNorm v (P⁻¹).val ≤ 1)
    (x : Fin n → Fv) : vecNorm v ((P⁻¹).val *ᵥ x) = vecNorm v x := by
  refine le_antisymm ((vecNorm_inv_mulVec_le P x).trans ?_) ((vecNorm_le_matNorm_mul_vecNorm_inv P x).trans ?_)
  · exact (mul_le_mul_left h2 _).trans (by rw [one_mul])
  · exact (mul_le_mul_left h1 _).trans (by rw [one_mul])

end Norms

/-- A rational $P \in \mathrm{GL}_n(F)$ is integral at almost all $\mathfrak p$. -/
theorem eventually_matNorm_le_one (P : GL (Fin n) F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      matNorm v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) P).val ≤ 1 := by
  filter_upwards [eventually_locAct_std P] with v hv
  refine (matNorm_le_one_iff _).mpr fun y hy => ?_
  rw [← hv]; exact ⟨y, hy, rfl⟩

theorem eventually_matNorm_inv_le_one (P : GL (Fin n) F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      matNorm v ((Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) P)⁻¹).val ≤ 1 := by
  filter_upwards [eventually_matNorm_le_one P⁻¹] with v hv
  rwa [map_inv] at hv

/-- **Example 101:1 over a global field** (O'Meara 1973, §101B, p. 289, from 101:1): for a base of $V = F^n$ given by
the columns of $P \in \mathrm{GL}_n(F)$, the norms $\lVert\cdot\rVert'_\mathfrak p$ with respect to it agree with the
standard norms at almost all $\mathfrak p$: $\lVert P^{-1}x\rVert_\mathfrak p = \lVert x\rVert_\mathfrak p$ for every
$x \in F_\mathfrak p^n$. -/
@[kb "omeara1963" "§101A, 101:1, p. 288; §101B, p. 289 (‖ ‖'_𝔭 = ‖ ‖_𝔭 for almost all 𝔭)"]
theorem eventually_vecNorm_inv_mulVec_eq (P : GL (Fin n) F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x : Fin n → v.adicCompletion F,
      vecNorm v ((Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) P)⁻¹.val *ᵥ x) =
        vecNorm v x := by
  filter_upwards [eventually_matNorm_le_one P, eventually_matNorm_inv_le_one P] with v h1 h2 x
  exact vecNorm_inv_mulVec_eq h1 h2 x

/-- **Example 101:1 over a global field, for linear maps** (O'Meara 1973, §101B, p. 289): with respect to the base
given by the columns of $P \in \mathrm{GL}_n(F)$, $\lVert\sigma\rVert'_\mathfrak p = \lVert\sigma\rVert_\mathfrak p$ for
every $\sigma$, at almost all $\mathfrak p$. -/
@[kb "omeara1963" "§101A, 101:1, p. 288; §101B, p. 289 (‖σ‖'_𝔭 = ‖σ‖_𝔭 for almost all 𝔭)"]
theorem eventually_matNorm_conj_eq (P : GL (Fin n) F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ A : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      matNorm v ((Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) P)⁻¹.val * A *
        (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) P).val) = matNorm v A := by
  filter_upwards [eventually_matNorm_le_one P, eventually_matNorm_inv_le_one P] with v h1 h2 A
  exact matNorm_conj_eq h1 h2 A

/-! ### Examples 101:3 and 101:4 -/

section Orth

variable (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **Example 101:3** (O'Meara 1973, §101A, p. 288): **$O^+(V_\mathfrak p)$ is an open and closed subgroup of
$O(V_\mathfrak p)$** (continuity of the determinant, which takes only the values $\pm 1$ on $O(V_\mathfrak p)$ for a
regular space). Here $O(V_\mathfrak p)$ = `orthGroup Q F_𝔭` carries the subspace topology of
$\mathrm{GL}_n(F_\mathfrak p)$, and $O^+(V_\mathfrak p)$ = `Tamagawa.soSub Q F_𝔭`. -/
@[kb "omeara1963" "§101A, 101:3, p. 288"]
theorem isClopen_soSub (hQ : Q.Nondegenerate) :
    IsClopen (Tamagawa.soSub Q Fv : Set (orthGroup Q Fv)) := by
  have one_ne_neg_one : (1 : Fv) ≠ -1 := by
    intro h
    have : (2 : Fv) = 0 := by linear_combination h
    exact two_ne_zero this
  have hc : Continuous fun g : orthGroup Q Fv => ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv).det :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_det
  have e1 : (Tamagawa.soSub Q Fv : Set (orthGroup Q Fv)) =
      (fun g : orthGroup Q Fv => ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv).det) ⁻¹' {1} := rfl
  have e2 : (Tamagawa.soSub Q Fv : Set (orthGroup Q Fv)) =
      (fun g : orthGroup Q Fv => ((g : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv).det) ⁻¹' {-1}ᶜ := by
    ext g
    simp only [SetLike.mem_coe, Tamagawa.mem_soSub, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    rcases Tamagawa.det_eq_one_or_neg_one Q hQ g with h | h
    · rw [h]; simp only [true_iff]; intro h'; exact one_ne_neg_one h'
    · rw [h]; simp only [not_true_eq_false, iff_false]; exact fun h' => one_ne_neg_one h'.symm
  exact ⟨e1 ▸ isClosed_singleton.preimage hc, e2 ▸ isClosed_singleton.isOpen_compl.preimage hc⟩

/-- **Example 101:4 (i)** (O'Meara 1973, §101A, p. 288): over the local field $F_\mathfrak p$, an isometry $\sigma$ of the
regular space $V_\mathfrak p$ lies in $O(M)$ for the lattice $M = \mathfrak o_\mathfrak p e_0 + \dots + \mathfrak o_\mathfrak p
e_{n-1}$ spanned by the base (`stdStab Q 𝔭`) **if and only if $\lVert\sigma\rVert \le 1$**. (O'Meara's proof:
$\det\sigma = \pm 1$ is a unit, so $\lVert\sigma\rVert \le 1$ gives $\sigma M \subseteq M$ and then $\sigma M = M$.) -/
@[kb "omeara1963" "§101A, 101:4 (i), p. 288"]
theorem mem_stdStab_iff_matNorm_le_one (hQ : Q.Nondegenerate) (σ : orthGroup Q Fv) :
    σ ∈ stdStab Q v ↔ matNorm v ((σ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) ≤ 1 := by
  constructor
  · intro h
    refine (matNorm_le_one_iff _).mpr fun y hy => ?_
    rw [← show locAct v (σ : GL (Fin n) Fv) (std v) = std v from h]
    exact ⟨y, hy, rfl⟩
  · intro h
    have hdet : Valued.v ((σ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv).det = 1 := by
      rcases Tamagawa.det_eq_one_or_neg_one Q hQ σ with h' | h' <;> simp [h']
    have hinv := matNorm_inv_le_one h hdet
    rw [← Matrix.coe_units_inv] at hinv
    have h1 := (matNorm_le_one_iff _).mp h
    have h2 := (matNorm_le_one_iff _).mp hinv
    change locAct v (σ : GL (Fin n) Fv) (std v) = std v
    refine le_antisymm ?_ fun y hy => ⟨((σ : GL (Fin n) Fv)⁻¹ : GL (Fin n) Fv).val *ᵥ y, h2 y hy,
      mulVec_inv_mulVec _ y⟩
    rintro _ ⟨y, hy, rfl⟩
    exact h1 y hy

/-- **Example 101:4 (i), the norm-one form** (O'Meara 1973, §101A, p. 288): for $n \ge 1$, the elements of $O(M)$,
$M = \mathfrak o_\mathfrak p^n$, are precisely the isometries with $\lVert\sigma\rVert = 1$; in particular these form a
group. (For $n = 0$ the norm is $0$ by convention, so the hypothesis $n \ge 1$ is needed for this form.) -/
@[kb "omeara1963" "§101A, 101:4 (i), p. 288 (O(M) = {σ : ‖σ‖ = 1})"]
theorem mem_stdStab_iff_matNorm_eq_one [NeZero n] (hQ : Q.Nondegenerate) (σ : orthGroup Q Fv) :
    σ ∈ stdStab Q v ↔ matNorm v ((σ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) = 1 := by
  rw [mem_stdStab_iff_matNorm_le_one Q v hQ]
  refine ⟨fun h => le_antisymm h ?_, fun h => h.le⟩
  have hdet : Valued.v ((σ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv).det = 1 := by
    rcases Tamagawa.det_eq_one_or_neg_one Q hQ σ with h' | h' <;> simp [h']
  by_contra hlt
  push Not at hlt
  have := (valued_det_le (v := v) ((σ : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv)).trans
    (pow_le_of_le_one zero_le hlt.le (NeZero.ne n))
  rw [hdet] at this
  exact absurd this (not_le.mpr hlt)

end Orth

end QuadFormsKB.Lattices
