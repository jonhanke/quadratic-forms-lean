/-
# O'Meara §95: the reduction $O_4(V) \to O_2(\bar V)$ of step 4 of the proof of 95:1

**Setting.** $R$ is a discrete valuation ring (O'Meara's $\mathfrak o$) with residue field $\bar F$ (`ResidueField R`)
and fraction field $F$, $2 \ne 0$ in $F$ and in $\bar F$, $\pi$ a prime element; $(V, Q)$ a quadratic space over $F$
with a normalized orthogonal base `N : S95.NormalBasis Q π` ($Q(e_0) = a_0$, $Q(e_1) = a_1$, $Q(e_2) = \pi a_2$,
$Q(e_3) = \pi a_3$, $a_i \in \mathfrak u$; `Sec95Basis.lean`). The two coordinate facts of `Sec95Coord.lean` are
hypotheses here: `hint` ($Q(z) \in \mathfrak o$ implies that the coordinates of $z$ are integral) and `hpi`
($Q(z) \in \mathfrak p$ implies that the coordinates $0, 1$ of $z$ lie in $\mathfrak p$).

**The construction** (O'Meara 1973 printing, proof of 95:1, step 4, pp. 282–283). With $L = \sum\mathfrak oe_i$ and
$L^{\mathfrak p} = \mathfrak pe_0 + \mathfrak pe_1 + \mathfrak oe_2 + \mathfrak oe_3$, the space
$\bar V = L/L^{\mathfrak p}$ has base $\bar e_0, \bar e_1$ and the form
$\bar Q = \langle \bar a_0, \bar a_1\rangle$ (`NormalBasis.Qbar`, on $\bar F^2$). Every $\sigma \in O(V)$ maps $L$
and $L^{\mathfrak p}$ onto themselves, so its matrix in the base $e$ is integral with the block of rows $0, 1$ and
columns $2, 3$ in $\mathfrak p$ (`NormalBasis.coef_integral`, `NormalBasis.coef_pi`); $\bar\sigma$ is the residue of
the block of rows and columns $0, 1$ (`NormalBasis.red`). This gives a homomorphism $O_4(V) \to O_2(\bar V)$
(`NormalBasis.redHom`, `NormalBasis.redHom_mem_orth`) with $\bar\tau_x = \tau_{\bar x}$ for $x = se_0 + te_1$
(`NormalBasis.redHom_symmetry01`) and $\bar\tau_u = 1$ for $u = s'e_2 + t'e_3$ (`NormalBasis.redHom_symmetry23`).

**Proves** `NormalBasis.symmetry_prod_not_mem_omega`: for $x = se_0 + te_1$, $y = s'e_0 + t'e_1$ with unit values
whose product has a non-square residue, and any $u, w$ in $Fe_2 + Fe_3$,
$\tau_x\tau_y\tau_u\tau_w \notin \Omega(V)$ (O'Meara: "Then $\bar\sigma \in \Omega_2(\bar V) = O'_2(\bar V)$ ... Hence
$\theta(\bar\sigma) = Q(\bar x)Q(\bar y) = \bar\Delta$ ... This is absurd").
-/
import QuadFormsKB.Literature.OMeara.Sec95Basis
import QuadFormsKB.Literature.OMeara.Sec95Omega
import QuadFormsKB.Literature.OMeara.Sec62

open QuadraticMap Module IsLocalRing
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace S95

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {Q : QuadraticForm F V} {π : R}

open Classical in
/-- The element of $R$ mapped to $x \in F$ ($0$ if $x \notin \mathfrak o$). -/
def toR (x : F) : R := if h : ∃ c : R, algebraMap R F c = x then h.choose else 0

theorem algebraMap_toR {x : F} (h : ∃ c : R, algebraMap R F c = x) : algebraMap R F (toR (R := R) x) = x := by
  classical
  unfold toR
  split_ifs
  exact h.choose_spec

theorem toR_algebraMap (c : R) : toR (R := R) (algebraMap R F c) = c :=
  IsFractionRing.injective R F (algebraMap_toR ⟨c, rfl⟩)

/-- The embedding of the indices $0, 1$ into $\{0, 1, 2, 3\}$. -/
def emb : Fin 2 → Fin 4 := Fin.castLE (by norm_num)

@[simp] theorem emb_zero : emb 0 = 0 := rfl
@[simp] theorem emb_one : emb 1 = 1 := rfl

namespace NormalBasis

variable (N : NormalBasis Q π)

/-- The entry $(i, j)$ of the matrix of $\sigma$ in the base $e$: the coordinate $i$ of $\sigma e_j$. -/
def coef (σ : V ≃ₗ[F] V) (i j : Fin 4) : F := N.e.repr (σ (N.e j)) i

theorem coef_mul (σ τ : V ≃ₗ[F] V) (i j : Fin 4) :
    N.coef (σ * τ) i j = ∑ k, N.coef σ i k * N.coef τ k j := by
  simp only [coef, LinearEquiv.mul_apply]
  conv_lhs => rw [← N.e.sum_repr (τ (N.e j))]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem coef_one (i j : Fin 4) : N.coef 1 i j = if i = j then 1 else 0 := by
  simp only [coef, LinearEquiv.coe_one, id, Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp_all [eq_comm]

/-- Every $Q(e_j)$ lies in $\mathfrak o$. -/
theorem exists_Q_e (j : Fin 4) : ∃ r : R, Q (N.e j) = algebraMap R F r := by
  fin_cases j
  exacts [⟨_, N.Q0⟩, ⟨_, N.Q1⟩, ⟨_, N.Q2⟩, ⟨_, N.Q3⟩]

variable {N}

/-- The matrix of $\sigma \in O(V)$ is integral ($\sigma L = L$). -/
theorem coef_integral (hint : ∀ (z : V) (r : R), Q z = algebraMap R F r → ∀ i, ∃ c : R, N.e.repr z i = algebraMap R F c)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ OMeara.orth Q) (i j : Fin 4) : ∃ c : R, N.coef σ i j = algebraMap R F c := by
  obtain ⟨r, hr⟩ := N.exists_Q_e j
  exact hint _ r (by rw [hσ, hr]) i

/-- The block of rows $0, 1$ and columns $2, 3$ of the matrix of $\sigma \in O(V)$ lies in $\mathfrak p$
($\sigma L^{\mathfrak p} = L^{\mathfrak p}$). -/
theorem coef_pi (hpi : ∀ (z : V) (r : R), Q z = algebraMap R F (π * r) → ∀ i : Fin 4, (i = 0 ∨ i = 1) →
      ∃ c : R, N.e.repr z i = algebraMap R F (π * c))
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ OMeara.orth Q) {i j : Fin 4} (hi : i = 0 ∨ i = 1) (hj : j = 2 ∨ j = 3) :
    ∃ c : R, N.coef σ i j = algebraMap R F (π * c) := by
  rcases hj with rfl | rfl
  · exact hpi _ _ (by rw [hσ, N.Q2]) i hi
  · exact hpi _ _ (by rw [hσ, N.Q3]) i hi

variable (N)

/-- The integral matrix of $\sigma$. -/
def M (σ : V ≃ₗ[F] V) : Matrix (Fin 4) (Fin 4) R := fun i j => toR (N.coef σ i j)

/-- **The reduction $\bar\sigma$** (O'Meara 1973, proof of 95:1, step 4, p. 282): the residue of the block of rows
and columns $0, 1$ of the matrix of $\sigma$, i.e. the matrix of the map $\bar V \to \bar V$ induced by $\sigma$ in
the base $\bar e_0, \bar e_1$. -/
def red (σ : V ≃ₗ[F] V) : Matrix (Fin 2) (Fin 2) (ResidueField R) :=
  fun i j => residue R (N.M σ (emb i) (emb j))

/-- The form $\bar Q = \langle \bar a_0, \bar a_1\rangle$ on $\bar V = \bar F^2$. -/
def Qbar : QuadraticForm (ResidueField R) (Fin 2 → ResidueField R) :=
  weightedSumSquares (ResidueField R) fun i : Fin 2 => residue R (N.a (emb i))

/-- The vector $\sum_k c_ke_k$ with integral coordinates $c_k \in \mathfrak o$. -/
def vec (c : Fin 4 → R) : V := ∑ k, algebraMap R F (c k) • N.e k

theorem repr_vec (c : Fin 4 → R) (k : Fin 4) : N.e.repr (N.vec c) k = algebraMap R F (c k) := by
  rw [vec, N.e.repr_sum_self]

theorem Q_vec (c : Fin 4 → R) :
    Q (N.vec c) = algebraMap R F (N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2 + π * (N.a 2 * c 2 ^ 2 + N.a 3 * c 3 ^ 2)) := by
  rw [vec, N.Q_eq]
  simp only [map_add, map_mul, map_pow]
  ring

/-- $B(z, w) = \sum_k z_kw_kQ(e_k)$ in coordinates. -/
theorem bil_repr (z w : V) : bil Q z w = ∑ k, N.e.repr z k * N.e.repr w k * Q (N.e k) := by
  conv_lhs => rw [← N.e.sum_repr z, ← N.e.sum_repr w]
  rw [bil_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bil_sum_right, Finset.sum_eq_single k]
  · rw [bil_smul_left, bil_smul_right, bil_self]; ring
  · intro l _ hlk
    rw [bil_smul_left, bil_smul_right, N.orth k l (Ne.symm hlk)]; ring
  · simp

variable {N}

theorem algebraMap_M (hint : ∀ (z : V) (r : R), Q z = algebraMap R F r → ∀ i, ∃ c : R,
      N.e.repr z i = algebraMap R F c)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ OMeara.orth Q) (i j : Fin 4) : algebraMap R F (N.M σ i j) = N.coef σ i j :=
  algebraMap_toR (by obtain ⟨c, hc⟩ := coef_integral hint hσ i j; exact ⟨c, hc.symm⟩)

theorem M_mul (hint : ∀ (z : V) (r : R), Q z = algebraMap R F r → ∀ i, ∃ c : R,
      N.e.repr z i = algebraMap R F c)
    {σ τ : V ≃ₗ[F] V} (hσ : σ ∈ OMeara.orth Q) (hτ : τ ∈ OMeara.orth Q) (i j : Fin 4) :
    N.M (σ * τ) i j = ∑ k, N.M σ i k * N.M τ k j := by
  apply IsFractionRing.injective R F
  rw [algebraMap_M hint ((OMeara.orth Q).mul_mem hσ hτ), coef_mul, map_sum]
  simp only [map_mul, algebraMap_M hint hσ, algebraMap_M hint hτ]

theorem M_pi (hint : ∀ (z : V) (r : R), Q z = algebraMap R F r → ∀ i, ∃ c : R,
      N.e.repr z i = algebraMap R F c)
    (hpi : ∀ (z : V) (r : R), Q z = algebraMap R F (π * r) → ∀ i : Fin 4, (i = 0 ∨ i = 1) →
      ∃ c : R, N.e.repr z i = algebraMap R F (π * c))
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ OMeara.orth Q) {i j : Fin 4} (hi : i = 0 ∨ i = 1) (hj : j = 2 ∨ j = 3) :
    π ∣ N.M σ i j := by
  obtain ⟨c, hc⟩ := coef_pi hpi hσ hi hj
  refine ⟨c, IsFractionRing.injective R F ?_⟩
  rw [algebraMap_M hint hσ, hc]

variable (N)

theorem M_one (i j : Fin 4) : N.M 1 i j = if i = j then 1 else 0 := by
  unfold M
  rw [coef_one]
  split_ifs
  · rw [← map_one (algebraMap R F), toR_algebraMap]
  · rw [← map_zero (algebraMap R F), toR_algebraMap]

theorem red_one : N.red 1 = 1 := by
  ext i j
  simp only [red, M_one, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [emb]

variable {N}

theorem residue_M_pi (hint : ∀ (z : V) (r : R), Q z = algebraMap R F r → ∀ i, ∃ c : R,
      N.e.repr z i = algebraMap R F c)
    (hpi : ∀ (z : V) (r : R), Q z = algebraMap R F (π * r) → ∀ i : Fin 4, (i = 0 ∨ i = 1) →
      ∃ c : R, N.e.repr z i = algebraMap R F (π * c))
    (hπ : Irreducible π) {σ : V ≃ₗ[F] V} (hσ : σ ∈ OMeara.orth Q) {i j : Fin 4} (hi : i = 0 ∨ i = 1)
    (hj : j = 2 ∨ j = 3) : residue R (N.M σ i j) = 0 := by
  obtain ⟨c, hc⟩ := M_pi hint hpi hσ hi hj
  rw [hc, map_mul, (residue_eq_zero_iff π).mpr ((mem_maximalIdeal _).mpr hπ.not_isUnit), zero_mul]

theorem red_mul (hint : ∀ (z : V) (r : R), Q z = algebraMap R F r → ∀ i, ∃ c : R,
      N.e.repr z i = algebraMap R F c)
    (hpi : ∀ (z : V) (r : R), Q z = algebraMap R F (π * r) → ∀ i : Fin 4, (i = 0 ∨ i = 1) →
      ∃ c : R, N.e.repr z i = algebraMap R F (π * c))
    (hπ : Irreducible π) {σ τ : V ≃ₗ[F] V} (hσ : σ ∈ OMeara.orth Q) (hτ : τ ∈ OMeara.orth Q) :
    N.red (σ * τ) = N.red σ * N.red τ := by
  ext i j
  have h2 := residue_M_pi hint hpi hπ hσ (i := emb i) (j := 2) (by fin_cases i <;> simp) (by simp)
  have h3 := residue_M_pi hint hpi hπ hσ (i := emb i) (j := 3) (by fin_cases i <;> simp) (by simp)
  simp only [red, Matrix.mul_apply, Fin.sum_univ_two, M_mul hint hσ hτ, Fin.sum_univ_four, map_add, map_mul,
    h2, h3, zero_mul, add_zero, emb_zero, emb_one]

/-- The hypotheses `hint` and `hpi` and the prime element, bundled for the homomorphism below. -/
structure RedData (N : NormalBasis Q π) : Prop where
  /-- $Q(z) \in \mathfrak o$ implies that the coordinates of $z$ are integral. -/
  hint : ∀ (z : V) (r : R), Q z = algebraMap R F r → ∀ i, ∃ c : R, N.e.repr z i = algebraMap R F c
  /-- $Q(z) \in \mathfrak p$ implies that the coordinates $0, 1$ of $z$ lie in $\mathfrak p$. -/
  hpi : ∀ (z : V) (r : R), Q z = algebraMap R F (π * r) → ∀ i : Fin 4, (i = 0 ∨ i = 1) →
    ∃ c : R, N.e.repr z i = algebraMap R F (π * c)
  /-- $\pi$ is a prime element. -/
  hπ : Irreducible π

theorem RedData.red_mul (D : RedData N) {σ τ : V ≃ₗ[F] V} (hσ : σ ∈ OMeara.orth Q) (hτ : τ ∈ OMeara.orth Q) :
    N.red (σ * τ) = N.red σ * N.red τ :=
  NormalBasis.red_mul D.hint D.hpi D.hπ hσ hτ

theorem RedData.red_mul_inv (D : RedData N) (σ : OMeara.orth Q) :
    N.red (σ : V ≃ₗ[F] V) * N.red ((σ⁻¹ : OMeara.orth Q) : V ≃ₗ[F] V) = 1 := by
  rw [← D.red_mul σ.2 (σ⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, red_one]

theorem RedData.red_inv_mul (D : RedData N) (σ : OMeara.orth Q) :
    N.red ((σ⁻¹ : OMeara.orth Q) : V ≃ₗ[F] V) * N.red (σ : V ≃ₗ[F] V) = 1 := by
  rw [← D.red_mul (σ⁻¹).2 σ.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, red_one]

/-- **The homomorphism $O_4(V) \to O_2(\bar V)$, $\sigma \mapsto \bar\sigma$** (O'Meara 1973, proof of 95:1, step 4,
p. 282: "it is easily seen that $\bar\sigma$ is an isometry of $\bar V$ onto $\bar V$; and that
$\overline{\sigma_1\sigma_2} = \bar\sigma_1\bar\sigma_2$"), as a homomorphism into the linear automorphisms of
$\bar V = \bar F^2$; its values are isometries of $\bar Q$ by `RedData.redHom_mem_orth`. -/
def RedData.redHom (D : RedData N) :
    OMeara.orth Q →* ((Fin 2 → ResidueField R) ≃ₗ[ResidueField R] (Fin 2 → ResidueField R)) where
  toFun σ := LinearEquiv.ofLinearMap (Matrix.toLin' (N.red (σ : V ≃ₗ[F] V)))
    (Matrix.toLin' (N.red ((σ⁻¹ : OMeara.orth Q) : V ≃ₗ[F] V)))
    (by rw [← Matrix.toLin'_mul, D.red_mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, D.red_inv_mul, Matrix.toLin'_one])
  map_one' := by
    refine LinearEquiv.ext fun y => ?_
    simp [red_one]
  map_mul' σ τ := by
    refine LinearEquiv.ext fun y => ?_
    simp [Subgroup.coe_mul, D.red_mul σ.2 τ.2, Matrix.toLin'_mul]

theorem RedData.redHom_apply (D : RedData N) (σ : OMeara.orth Q) (y : Fin 2 → ResidueField R) :
    D.redHom σ y = N.red (σ : V ≃ₗ[F] V) *ᵥ y := by
  simp [RedData.redHom, Matrix.toLin'_apply]

/-- The value list $(a_0, a_1, \pi a_2, \pi a_3)$. -/
def dvals (N : NormalBasis Q π) : Fin 4 → R := ![N.a 0, N.a 1, π * N.a 2, π * N.a 3]

theorem Q_e_eq (N : NormalBasis Q π) (k : Fin 4) : Q (N.e k) = algebraMap R F (dvals N k) := by
  fin_cases k
  exacts [N.Q0, N.Q1, N.Q2, N.Q3]

/-- The columns of the matrix of $\sigma \in O(V)$ are orthogonal for $\langle a_0, a_1, \pi a_2, \pi a_3\rangle$. -/
theorem RedData.M_orth (D : RedData N) {σ : V ≃ₗ[F] V} (hσ : σ ∈ OMeara.orth Q) (i j : Fin 4) :
    ∑ k, N.M σ k i * N.M σ k j * dvals N k = if i = j then dvals N i else 0 := by
  apply IsFractionRing.injective R F
  have h := Sp55.bil_orth Q hσ (N.e i) (N.e j)
  rw [N.bil_repr, N.bil_repr] at h
  rw [map_sum]
  refine (Finset.sum_congr rfl fun k _ => ?_).trans (h.trans ?_)
  · rw [map_mul, map_mul, algebraMap_M D.hint hσ, algebraMap_M D.hint hσ, Q_e_eq]
    rfl
  · simp only [Basis.repr_self, Finsupp.single_apply]
    rw [Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp [Q_e_eq]
      · simp [hij, Ne.symm hij]
    · intro b _ hb; simp [Ne.symm hb]
    · simp

/-- $\bar\sigma$ is orthogonal for $\langle \bar a_0, \bar a_1\rangle$: the three scalar relations. -/
theorem RedData.red_orth (D : RedData N) {σ : V ≃ₗ[F] V} (hσ : σ ∈ OMeara.orth Q) (i j : Fin 2) :
    ∑ k : Fin 2, N.red σ k i * N.red σ k j * residue R (N.a (emb k)) =
      if i = j then residue R (N.a (emb i)) else 0 := by
  have h := congrArg (residue R) (D.M_orth hσ (emb i) (emb j))
  have h2 : residue R (dvals N 2) = 0 := by
    simp only [dvals]
    rw [show (![N.a 0, N.a 1, π * N.a 2, π * N.a 3] : Fin 4 → R) 2 = π * N.a 2 from rfl, map_mul,
      (residue_eq_zero_iff π).mpr ((mem_maximalIdeal _).mpr D.hπ.not_isUnit), zero_mul]
  have h3 : residue R (dvals N 3) = 0 := by
    simp only [dvals]
    rw [show (![N.a 0, N.a 1, π * N.a 2, π * N.a 3] : Fin 4 → R) 3 = π * N.a 3 from rfl, map_mul,
      (residue_eq_zero_iff π).mpr ((mem_maximalIdeal _).mpr D.hπ.not_isUnit), zero_mul]
  rw [map_sum, Fin.sum_univ_four] at h
  simp only [map_mul, h2, h3, mul_zero, add_zero] at h
  rw [Fin.sum_univ_two]
  have e0 : dvals N 0 = N.a 0 := rfl
  have e1 : dvals N 1 = N.a 1 := rfl
  fin_cases i <;> fin_cases j
  · simpa [red, e0, e1] using h
  · simpa [red, e0, e1] using h
  · simpa [red, e0, e1] using h
  · simpa [red, e0, e1] using h

/-- **$\bar\sigma$ is an isometry of $\bar V$** (O'Meara 1973, proof of 95:1, step 4, p. 282). -/
theorem RedData.redHom_mem_orth (D : RedData N) (σ : OMeara.orth Q) : D.redHom σ ∈ OMeara.orth N.Qbar := by
  intro y
  rw [D.redHom_apply]
  have h00 := D.red_orth σ.2 0 0
  have h01 := D.red_orth σ.2 0 1
  have h11 := D.red_orth σ.2 1 1
  rw [if_pos rfl] at h00 h11
  rw [if_neg (by decide)] at h01
  rw [Fin.sum_univ_two] at h00 h01 h11
  simp only [Qbar, weightedSumSquares_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct, smul_eq_mul]
  linear_combination (y 0 * y 0) * h00 + (2 * y 0 * y 1) * h01 + (y 1 * y 1) * h11

variable (N)

/-- $B(e_j, x) = x_jQ(e_j)$. -/
theorem bil_e_left (j : Fin 4) (x : V) : bil Q (N.e j) x = N.e.repr x j * Q (N.e j) := by
  rw [N.bil_repr, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Basis.repr_self, Finsupp.single_apply, Ne.symm hb]
  · simp

/-- The matrix of a symmetry: $\tau_x e_j = e_j - \frac{2x_jQ(e_j)}{Q(x)}x$. -/
theorem coef_symmetry {x : V} (hx : Q x ≠ 0) (i j : Fin 4) :
    N.coef (symmetry Q x hx) i j =
      (if i = j then 1 else 0) - 2 * (N.e.repr x j * Q (N.e j)) / Q x * N.e.repr x i := by
  simp only [coef, symmetry_apply, map_sub, map_smul, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Basis.repr_self, Finsupp.single_apply, N.bil_e_left]
  split_ifs with h1 h2 h2 <;> simp_all

variable {N}

/-- $\bar Q(\bar x) = \overline{a_0c_0^2 + a_1c_1^2}$ for $\bar x = (\bar c_0, \bar c_1)$. -/
theorem Qbar_apply (c : Fin 4 → R) :
    N.Qbar (fun i => residue R (c (emb i))) = residue R (N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2) := by
  simp only [Qbar, weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul, emb_zero, emb_one, map_add, map_mul,
    map_pow]
  ring

/-- **$\bar\tau_x = \tau_{\bar x}$** for $x = c_0e_0 + c_1e_1$ with $Q(x)$ a unit (O'Meara 1973, proof of 95:1,
step 4, p. 283: "it is easily seen from the defining equation of a symmetry that $\bar\sigma = \tau_{\bar x}
\tau_{\bar y}$"). -/
theorem RedData.redHom_symmetry01 [Invertible (2 : ResidueField R)] (D : RedData N) {c : Fin 4 → R}
    (hc : c 2 = 0 ∧ c 3 = 0) (hcu : IsUnit (N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2)) (hx : Q (N.vec c) ≠ 0)
    (hxb : N.Qbar (fun i => residue R (c (emb i))) ≠ 0) :
    D.redHom ⟨symmetry Q (N.vec c) hx, symmetry_mem_orth Q hx⟩ =
      symmetry N.Qbar (fun i => residue R (c (emb i))) hxb := by
  set q := N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2 with hq
  have hQx : Q (N.vec c) = algebraMap R F q := by
    rw [N.Q_vec, hc.1, hc.2]; simp [hq]
  obtain ⟨u, hu⟩ : ∃ u : R, u * q = 1 := ⟨↑hcu.unit⁻¹, by simp⟩
  have hqF : algebraMap R F q ≠ 0 := by rw [← hQx]; exact hx
  -- the integral matrix of the symmetry
  have hM : ∀ a b : Fin 2, N.M (symmetry Q (N.vec c) hx) (emb a) (emb b) =
      (if a = b then 1 else 0) - 2 * (c (emb b) * N.a (emb b)) * u * c (emb a) := by
    intro a b
    apply IsFractionRing.injective R F
    rw [algebraMap_M D.hint (symmetry_mem_orth Q hx), coef_symmetry, N.repr_vec, N.repr_vec, hQx]
    have hab : (emb a = emb b) ↔ a = b := (Fin.castLE_injective _).eq_iff
    have hQe : Q (N.e (emb b)) = algebraMap R F (N.a (emb b)) := by
      fin_cases b
      exacts [N.Q0, N.Q1]
    have huF : algebraMap R F u = (algebraMap R F q)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, hu, map_one])
    rw [hQe]
    simp only [hab, map_sub, map_mul, map_ofNat, huF]
    split_ifs <;> simp only [map_one, map_zero, div_eq_mul_inv] <;> ring
  have hres : residue R u * residue R q = 1 := by rw [← map_mul, hu, map_one]
  have hqb : N.Qbar (fun i => residue R (c (emb i))) = residue R q := Qbar_apply c
  refine LinearEquiv.ext fun y => funext fun i => ?_
  rw [D.redHom_apply, symmetry_apply, Qbar, bil_wss, ← Qbar]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, red, hM, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    hqb]
  have hqb0 : residue R q ≠ 0 := by rw [← hqb]; exact hxb
  have hub : residue R u = (residue R q)⁻¹ := eq_inv_of_mul_eq_one_left hres
  simp only [map_sub, map_mul, map_ofNat, hub, emb_zero, emb_one]
  fin_cases i <;> simp <;> field_simp <;> ring

/-- **$\bar\tau_u = 1$** for $u = c_2e_2 + c_3e_3$ ($\tau_u$ fixes $e_0, e_1$; O'Meara 1973, proof of 95:1, step 4,
p. 283). -/
theorem RedData.redHom_symmetry23 (D : RedData N) {c : Fin 4 → R} (hc : c 0 = 0 ∧ c 1 = 0)
    (hx : Q (N.vec c) ≠ 0) : D.redHom ⟨symmetry Q (N.vec c) hx, symmetry_mem_orth Q hx⟩ = 1 := by
  have hM : ∀ a b : Fin 2, N.M (symmetry Q (N.vec c) hx) (emb a) (emb b) = if a = b then 1 else 0 := by
    intro a b
    apply IsFractionRing.injective R F
    rw [algebraMap_M D.hint (symmetry_mem_orth Q hx), coef_symmetry, N.repr_vec]
    have hcb : c (emb b) = 0 := by fin_cases b <;> simp [hc.1, hc.2]
    have hab : (emb a = emb b) ↔ a = b := (Fin.castLE_injective _).eq_iff
    rw [hcb]
    simp only [hab, map_zero, zero_mul, mul_zero, zero_div, sub_zero]
    split_ifs <;> simp
  refine LinearEquiv.ext fun y => ?_
  rw [D.redHom_apply]
  have : N.red (symmetry Q (N.vec c) hx) = 1 := by
    ext a b
    simp only [red, hM, Matrix.one_apply]
    split_ifs <;> simp
  simp [this]

/-- $\bar Q = \langle \bar a_0, \bar a_1\rangle$ is regular. -/
theorem Qbar_nondegenerate [Invertible (2 : ResidueField R)] :
    (QuadraticMap.associated (N.Qbar)).Nondegenerate := by
  apply cd_nondeg_of_reg
  intro x hx
  have hne : ∀ i : Fin 2, residue R (N.a (emb i)) ≠ 0 := fun i h0 => by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h0
    exact h0 (N.unit _)
  funext i
  have h := hx (Pi.single i 1)
  rw [Qbar, bil_wss, Finset.sum_eq_single i] at h
  · simpa [hne i] using h
  · intro b _ hb; simp [hb]
  · simp

/-- **Step 4 of the proof of 95:1** (O'Meara 1973, p. 283): let $x = c_0e_0 + c_1e_1$ and $y = d_0e_0 + d_1e_1$ have
unit values $Q(x), Q(y)$ with $\overline{Q(x)Q(y)}$ not a square in $\bar F$, and let $u, w \in Fe_2 + Fe_3$ be
anisotropic. Then $\tau_x\tau_y\tau_u\tau_w \notin \Omega(V)$: otherwise $\bar\sigma = \tau_{\bar x}\tau_{\bar y}$
would lie in $\Omega_2(\bar V) \subseteq O'_2(\bar V)$, but $\theta(\bar\sigma) = \bar Q(\bar x)\bar Q(\bar y)$ is not a
square. -/
theorem RedData.symmetry_prod_not_mem_omega [Invertible (2 : ResidueField R)] (D : RedData N)
    {c d c' d' : Fin 4 → R} (hc : c 2 = 0 ∧ c 3 = 0) (hd : d 2 = 0 ∧ d 3 = 0) (hc' : c' 0 = 0 ∧ c' 1 = 0)
    (hd' : d' 0 = 0 ∧ d' 1 = 0) (hcu : IsUnit (N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2))
    (hdu : IsUnit (N.a 0 * d 0 ^ 2 + N.a 1 * d 1 ^ 2))
    (hsq : ¬ IsSquare (residue R ((N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2) * (N.a 0 * d 0 ^ 2 + N.a 1 * d 1 ^ 2))))
    (hx : Q (N.vec c) ≠ 0) (hy : Q (N.vec d) ≠ 0) (hu : Q (N.vec c') ≠ 0) (hw : Q (N.vec d') ≠ 0) :
    symmetry Q (N.vec c) hx * symmetry Q (N.vec d) hy * symmetry Q (N.vec c') hu * symmetry Q (N.vec d') hw ∉
      omega Q := by
  intro hmem
  have hxb : N.Qbar (fun i => residue R (c (emb i))) ≠ 0 := by
    rw [Qbar_apply]; intro h0
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h0; exact h0 hcu
  have hyb : N.Qbar (fun i => residue R (d (emb i))) ≠ 0 := by
    rw [Qbar_apply]; intro h0
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h0; exact h0 hdu
  set g : OMeara.orth Q := ⟨symmetry Q (N.vec c) hx, symmetry_mem_orth Q hx⟩ *
    ⟨symmetry Q (N.vec d) hy, symmetry_mem_orth Q hy⟩ * ⟨symmetry Q (N.vec c') hu, symmetry_mem_orth Q hu⟩ *
    ⟨symmetry Q (N.vec d') hw, symmetry_mem_orth Q hw⟩ with hg
  have hgc : g ∈ commutator (OMeara.orth Q) := by
    rw [Sp55.omega_eq_map] at hmem
    obtain ⟨g', hg', hg'eq⟩ := hmem
    have : g' = g := Subtype.ext hg'eq
    rwa [← this]
  -- the image of the commutator subgroup lies in Ω(V̄)
  let φ : OMeara.orth Q →* OMeara.orth N.Qbar := D.redHom.codRestrict _ D.redHom_mem_orth
  have hφ : φ g ∈ commutator (OMeara.orth N.Qbar) := by
    have h1 : (commutator (OMeara.orth Q)).map φ ≤ commutator (OMeara.orth N.Qbar) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h1 ⟨g, hgc, rfl⟩
  have hΩ : (φ g : (Fin 2 → ResidueField R) ≃ₗ[ResidueField R] (Fin 2 → ResidueField R)) ∈ omega N.Qbar := by
    rw [Sp55.omega_eq_map]; exact ⟨φ g, hφ, rfl⟩
  have hO' := omega_le_orthPrime N.Qbar Qbar_nondegenerate hΩ
  have hφg : (φ g : (Fin 2 → ResidueField R) ≃ₗ[ResidueField R] (Fin 2 → ResidueField R)) =
      symmetry N.Qbar _ hxb * symmetry N.Qbar _ hyb := by
    show D.redHom g = _
    rw [hg, map_mul, map_mul, map_mul, D.redHom_symmetry01 hc hcu hx hxb, D.redHom_symmetry01 hd hdu hy hyb,
      D.redHom_symmetry23 hc' hu, D.redHom_symmetry23 hd' hw, mul_one, mul_one]
  rw [hφg] at hO'
  have hs := hasSpinorNorm_symmetry_mul N.Qbar hxb hyb
  have hsq' := ((mem_orthPrime_iff N.Qbar Qbar_nondegenerate ⟨_, hs⟩).mp hO').2 _ hs
  rw [Qbar_apply, Qbar_apply, ← map_mul] at hsq'
  exact hsq hsq'

end NormalBasis

end S95

end QuadFormsKB.OMeara
