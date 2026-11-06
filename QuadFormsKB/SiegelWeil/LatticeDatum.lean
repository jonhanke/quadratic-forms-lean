/-
# The Eisenstein series of an arbitrary lattice, free or not
**Layer:** local at each finite place $v$ of a number field $F$ (dyadic places included), then global (finite adeles).

**Setting.** $V = F^n$ with $Q = \sum_{i<n}a_ix_i^2$, $n = 2m$ (0-based indices). An $\mathcal O_F$-lattice $L \subset F^n$ is determined by its
completions $L_v \subset F_v^n$, and every family of $\mathcal O_v$-lattices $(L_v)_v$ with $L_v = \mathcal O_v^n$ for almost all $v$ comes from a
unique lattice $L = F^n \cap \prod_vL_v$ (the local–global correspondence of lattices, O'Meara (1973), 81:14). Since $\mathcal O_v$ is a
principal ideal domain, $L_v = h_v\mathcal O_v^n$ for some $h_v \in \mathrm{GL}_n(F_v)$, so **the lattices of $F^n$ are the $L = F^n\cap h\hat{\mathcal O}^n$,
$h \in \mathrm{GL}_n(\mathbb A_f)$**. This includes the lattices that are not free over $\mathcal O_F$: for a fractional ideal $\mathfrak a$ with
local generators $\alpha_v$ ($\mathfrak a_v = \alpha_v\mathcal O_v$), $h = \operatorname{diag}((\alpha_v)_v, 1, \dots, 1)$ gives $L = \mathfrak a \oplus \mathcal O_F^{n-1}$,
of Steinitz class $[\mathfrak a]$, which is not free when $\mathfrak a$ is not principal. A non-diagonal form $Q_0$ on $L$ with a diagonalization
$Q_0\circ P = \langle a\rangle$ ($P \in \mathrm{GL}_n(F)$) is covered too: in the diagonal coordinates the lattice is $P^{-1}L$, i.e. $h$ is replaced by
$P^{-1}h$. The correspondence itself (O'Meara 81:14) is not used in the proofs below: the datum is defined from $h$ directly.

**Results (local).**
* `mem_Sn_of_periodic`: a function on $F_v^n$ supported in $\varpi_v^{-k}\mathcal O_v^n$ and invariant under translation by $\varpi_v^k\mathcal O_v^n$ is a
  Schwartz–Bruhat function (a finite combination of pure tensors of ball indicators).
* `latIndM`, `latIndM_mem_Sn`: the indicator $\mathbf 1_{M^{-1}\mathcal O_v^n}(y) = \mathbf 1_{\mathcal O_v^n}(My)$, $M \in \mathrm{GL}_n(F_v)$, is Schwartz–Bruhat;
  `latIndM_eq_oneV`: it is $\mathbf 1_{\mathcal O_v^n}$ when $M \in \mathrm{GL}_n(\mathcal O_v)$; `latIndM_matV`: for $M = P$ integral it is `latInd`.

**Results (global).**
* `latSA h`: the finite datum $\Phi_v = \mathbf 1_{h_v\mathcal O_v^n}$ of $L = F^n\cap h\hat{\mathcal O}^n$, $h \in \mathrm{GL}_n(\mathbb A_f)$
  (`eventually_latSA_eq`: $\Phi_v = \mathbf 1_{\mathcal O_v^n}$ for almost all $v$).
* **`eisensteinA_latSA_converges`**: $E((g_z, g_f), s, \varphi_\infty\otimes\mathbf 1_{\hat L})$ converges absolutely for $\operatorname{Re}s > 1$, for every
  lattice $L$ (free or not), every $g_f \in \mathrm{SL}_2(\mathbb A_f)$ and $z \in \mathbb H^d$ ($F$ totally real, $Q$ totally positive).

Sources: O'Meara (1973), 81:14 (local–global correspondence of lattices), 81:5 and §82 (Steinitz class); Weil, Acta Math. 113 (1965)
[unverified]; Kudla (2008), §1 [unverified].
-/
import QuadFormsKB.SiegelWeil.EisensteinAdelic

open IsDedekindDomain NumberField MeasureTheory Filter WithZero
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
open scoped MatrixGroups
open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {m : ℕ}

lemma ptensor_ballIndV_eq_ite_k (k : ℤ) (c x : Fin (2 * m) → Fv) :
    ptensor (fun i => ballIndV v (c i) k) x = if ∀ i, Valued.v (x i - c i) ≤ exp (-k) then 1 else 0 := by
  unfold ptensor
  split_ifs with h
  · exact Finset.prod_eq_one fun i _ => by
      show ballIndV v (c i) k (x i) = 1
      unfold ballIndV
      exact Set.indicator_of_mem (by simpa using h i) _
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      show ballIndV v (c i) k (x i) = 0
      unfold ballIndV
      exact Set.indicator_of_notMem (by simpa using hi) _)

lemma ballIndV_mem_SBK_k (c : Fv) (k : ℤ) : ballIndV v c k ∈ SBK Fv := by
  have e : ballIndV v c k = (Metric.closedBall c ‖HN.ϖ v ^ k‖).indicator fun _ => (1 : ℂ) := by
    unfold ballIndV; rw [ballIndV_eq]
  rw [e]
  refine indicator_closedBall_mem_SBK c (norm_pos_iff.mpr (zpow_ne_zero _ ?_))
  exact HN.ϖ_ne_zero v

lemma exp_neg_mul_self (k : ℕ) : exp (-(k : ℤ)) * exp (-(k : ℤ)) = exp (-((2 * k : ℕ) : ℤ)) := by
  rw [← exp_add]; congr 1; push_cast; ring

/-- $y \in \varpi_v^{-k}\tilde z + \varpi_v^k\mathcal O_v$ iff $\varpi_v^ky \in \tilde z + \mathfrak p_v^{2k}$. -/
lemma valued_sub_ctr_le_iff (k : ℕ) (l y : Fv) :
    Valued.v (y - (piV v ^ k)⁻¹ * l) ≤ exp (-(k : ℤ)) ↔
      Valued.v (piV v ^ k * y - l) ≤ exp (-((2 * k : ℕ) : ℤ)) := by
  have hp : piV v ^ k ≠ 0 := pow_ne_zero _ (piV_ne_zero v)
  have e : piV v ^ k * y - l = piV v ^ k * (y - (piV v ^ k)⁻¹ * l) := by field_simp
  rw [e, map_mul, valued_piV_pow, ← exp_neg_mul_self]
  constructor
  · intro h; gcongr
  · intro h
    calc Valued.v (y - (piV v ^ k)⁻¹ * l)
        = exp (k : ℤ) * (exp (-(k : ℤ)) * Valued.v (y - (piV v ^ k)⁻¹ * l)) := by
          rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
      _ ≤ exp (k : ℤ) * (exp (-(k : ℤ)) * exp (-(k : ℤ))) := by gcongr
      _ = exp (-(k : ℤ)) := by rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/-- **Periodic compactly supported functions are Schwartz–Bruhat** (every finite place, dyadic included): if $\Phi$ vanishes off
$\varpi_v^{-k}\mathcal O_v^n$ and $\Phi(y + w) = \Phi(y)$ for $w \in \varpi_v^k\mathcal O_v^n$, then
$\Phi = \sum_z\Phi(c_z)\mathbf 1_{c_z + \varpi_v^k\mathcal O_v^n}$ (finite sum over $z \in (\mathcal O_v/\mathfrak p_v^{2k})^n$, $c_z = \varpi_v^{-k}\tilde z$) lies in
$S(F_v^n)$. -/
theorem mem_Sn_of_periodic (k : ℕ) (Φ : (Fin (2 * m) → Fv) → ℂ)
    (hsupp : ∀ y, Φ y ≠ 0 → ∀ i, Valued.v (piV v ^ k * y i) ≤ 1)
    (hper : ∀ y w : Fin (2 * m) → Fv, (∀ i, Valued.v (w i) ≤ exp (-(k : ℤ))) → Φ (y + w) = Φ y) :
    Φ ∈ (localDataV v).Sn (2 * m) := by
  classical
  have := LocalDensity.DVR.finite_quot_pow (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v) (2 * k)
  let _ : Fintype (RQ v (2 * k)) := Fintype.ofFinite _
  set c : (Fin (2 * m) → RQ v (2 * k)) → Fin (2 * m) → Fv := fun z i => (piV v ^ k)⁻¹ * liftR v (2 * k) z i
  have hwithin : ∀ (z : Fin (2 * m) → RQ v (2 * k)) (y : Fin (2 * m) → Fv), (∀ i, Valued.v (y i - c z i) ≤ exp (-(k : ℤ))) ↔
      (fun i => piV v ^ k * y i) ∈ fiberR v (2 * k) z := by
    intro z y
    constructor
    · intro h i _; exact (valued_sub_ctr_le_iff v k _ _).mp (h i)
    · intro h i; exact (valued_sub_ctr_le_iff v k _ _).mpr (h i (Set.mem_univ _))
  have hΦc : ∀ (z : Fin (2 * m) → RQ v (2 * k)) (y : Fin (2 * m) → Fv), (∀ i, Valued.v (y i - c z i) ≤ exp (-(k : ℤ))) → Φ (c z) = Φ y := by
    intro z y h
    have e : c z = y + (c z - y) := by abel
    rw [e, hper y (c z - y) fun i => by
      rw [Pi.sub_apply, ← neg_sub, Valuation.map_neg]; exact h i]
  have hsum : ∀ y, Φ y = ∑ z : Fin (2 * m) → RQ v (2 * k),
      Φ (c z) * ptensor (fun i => ballIndV v (c z i) k) y := by
    intro y
    simp_rw [ptensor_ballIndV_eq_ite_k]
    by_cases h : ∀ i, Valued.v (piV v ^ k * y i) ≤ 1
    · set z0 := redR v (2 * k) (fun i => piV v ^ k * y i) h
      have hmem : (fun i => piV v ^ k * y i) ∈ fiberR v (2 * k) z0 := (mem_fiberR_iff v (2 * k)).mpr ⟨h, rfl⟩
      have hz0 := (hwithin z0 y).mpr hmem
      rw [Finset.sum_eq_single z0]
      · rw [ite_eq_left hz0, mul_one, hΦc z0 y hz0]
      · intro z _ hz
        rw [ite_eq_right, mul_zero]
        intro hzy
        apply hz
        obtain ⟨_, e⟩ := (mem_fiberR_iff v (2 * k)).mp ((hwithin z y).mp hzy)
        exact e.symm
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · have hy0 : Φ y = 0 := by
        by_contra h0; exact h (hsupp y h0)
      rw [hy0]
      symm
      refine Finset.sum_eq_zero fun z _ => ?_
      split_ifs with hzy
      · rw [hΦc z y hzy, hy0, zero_mul]
      · rw [mul_zero]
  have hfun : Φ = ∑ z : Fin (2 * m) → RQ v (2 * k), Φ (c z) • ptensor (fun i => ballIndV v (c z i) k) := by
    funext y
    rw [hsum y, Finset.sum_apply]
    rfl
  rw [hfun]
  exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _
    (ptensor_mem_Sn fun i => ballIndV_mem_SBK_k v _ _)

/-- Every $x \in F_v$ becomes integral after multiplication by a power of $\varpi_v$. -/
lemma exists_piV_pow_mul_le_one (x : Fv) : ∃ k : ℕ, Valued.v (piV v ^ k * x) ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  · have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    refine ⟨(log (Valued.v x)).toNat, ?_⟩
    rw [map_mul, valued_piV_pow, ← exp_log h0, ← exp_add, ← exp_zero, exp_le_exp]
    have := Int.self_le_toNat (log (Valued.v x))
    rw [log_exp]
    omega

lemma valued_piV_pow_mono {k k' : ℕ} (hk : k ≤ k') {x : Fv} (h : Valued.v (piV v ^ k * x) ≤ 1) :
    Valued.v (piV v ^ k' * x) ≤ 1 := by
  rw [show piV v ^ k' * x = piV v ^ (k' - k) * (piV v ^ k * x) by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hk], map_mul, valued_piV_pow]
  exact mul_le_one' (by rw [← exp_zero, exp_le_exp]; omega) h

/-- A common exponent for finitely many elements. -/
lemma exists_piV_pow_mul_le_one_fintype {ι : Type*} [Fintype ι] (f : ι → Fv) :
    ∃ k : ℕ, ∀ i, Valued.v (piV v ^ k * f i) ≤ 1 := by
  choose k hk using fun i => exists_piV_pow_mul_le_one v (f i)
  refine ⟨∑ i, k i, fun i => valued_piV_pow_mono v ?_ (hk i)⟩
  exact Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- **The lattice indicator** $\mathbf 1_{M^{-1}\mathcal O_v^n}(y) = \mathbf 1_{\mathcal O_v^n}(My)$ for a matrix $M$ over $F_v$. -/
def latIndM (M : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv) : (Fin (2 * m) → Fv) → ℂ :=
  fun y => oneV v (2 * m) (M *ᵥ y)

/-- For an integral matrix $P$ over $\mathcal O_F$ this is the transported lattice indicator `latInd`. -/
lemma latIndM_matV (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) : latIndM v (matV v P) = latInd v P := rfl

lemma valued_mulVec_le {M : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv} {k : ℕ}
    (hM : ∀ i j, Valued.v (piV v ^ k * M i j) ≤ 1) {w : Fin (2 * m) → Fv}
    (hw : ∀ i, Valued.v (w i) ≤ exp (-(k : ℤ))) (i : Fin (2 * m)) : Valued.v ((M *ᵥ w) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  have hp : piV v ^ k ≠ 0 := pow_ne_zero _ (piV_ne_zero v)
  have e : M i j * w j = (piV v ^ k * M i j) * ((piV v ^ k)⁻¹ * w j) := by field_simp
  rw [e, map_mul]
  refine mul_le_one' (hM i j) ?_
  rw [map_mul, map_inv₀, valued_piV_pow]
  calc (exp (-(k : ℤ)))⁻¹ * Valued.v (w j) ≤ (exp (-(k : ℤ)))⁻¹ * exp (-(k : ℤ)) := by gcongr; exact hw j
    _ = 1 := inv_mul_cancel₀ (exp_ne_zero)

lemma valued_mulVec_le_of_int {N : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv} {k : ℕ}
    (hN : ∀ i j, Valued.v (piV v ^ k * N i j) ≤ 1) {x : Fin (2 * m) → Fv}
    (hx : ∀ i, Valued.v (x i) ≤ 1) (i : Fin (2 * m)) : Valued.v (piV v ^ k * (N *ᵥ x) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [← mul_assoc, map_mul]
  exact mul_le_one' (hN i j) (hx j)

/-- **$\mathbf 1_{M^{-1}\mathcal O_v^n}$ is a Schwartz–Bruhat function** for every invertible $M$ over $F_v$ ($NM = 1$), every finite place,
dyadic included: it is supported in $\varpi_v^{-k}\mathcal O_v^n$ and $\varpi_v^k\mathcal O_v^n$-periodic for $k$ large (`mem_Sn_of_periodic`). -/
theorem latIndM_mem_Sn (M N : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv) (hNM : N * M = 1) :
    latIndM v M ∈ (localDataV v).Sn (2 * m) := by
  obtain ⟨k, hk⟩ := exists_piV_pow_mul_le_one_fintype v
    (fun p : (Fin (2 * m) × Fin (2 * m)) ⊕ (Fin (2 * m) × Fin (2 * m)) =>
      Sum.elim (fun q => M q.1 q.2) (fun q => N q.1 q.2) p)
  have hM : ∀ i j, Valued.v (piV v ^ k * M i j) ≤ 1 := fun i j => hk (Sum.inl (i, j))
  have hN : ∀ i j, Valued.v (piV v ^ k * N i j) ≤ 1 := fun i j => hk (Sum.inr (i, j))
  refine mem_Sn_of_periodic v k _ (fun y hy i => ?_) (fun y w hw => ?_)
  · have hMy : ∀ i, Valued.v ((M *ᵥ y) i) ≤ 1 := by
      by_contra h
      exact hy (by unfold latIndM; rw [oneV_eq_ite', ite_eq_right h])
    have := valued_mulVec_le_of_int v hN hMy i
    rwa [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] at this
  · have hMw := valued_mulVec_le v hM hw
    unfold latIndM
    rw [Matrix.mulVec_add, oneV_eq_ite', oneV_eq_ite']
    congr 1
    apply propext
    constructor
    · intro h i
      have e : (M *ᵥ y) i = (M *ᵥ y + M *ᵥ w) i - (M *ᵥ w) i := by simp
      rw [e]
      exact (Valuation.map_sub _ _ _).trans (max_le (h i) (hMw i))
    · intro h i
      exact (Valuation.map_add _ _ _).trans (max_le (h i) (hMw i))

/-- **$\mathbf 1_{M^{-1}\mathcal O_v^n} = \mathbf 1_{\mathcal O_v^n}$ for $M \in \mathrm{GL}_n(\mathcal O_v)$** (entries of $M$ and $N = M^{-1}$ integral). -/
theorem latIndM_eq_oneV (M N : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv) (hNM : N * M = 1)
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hN : ∀ i j, Valued.v (N i j) ≤ 1) :
    latIndM v M = oneV v (2 * m) := by
  funext y
  unfold latIndM
  rw [oneV_eq_ite', oneV_eq_ite']
  have hM' : ∀ i j, Valued.v (piV v ^ 0 * M i j) ≤ 1 := fun i j => by simpa using hM i j
  have hN' : ∀ i j, Valued.v (piV v ^ 0 * N i j) ≤ 1 := fun i j => by simpa using hN i j
  congr 1
  apply propext
  constructor
  · intro h i
    have := valued_mulVec_le_of_int v hN' h i
    rwa [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec, pow_zero, one_mul] at this
  · intro h i
    exact valued_mulVec_le v hM' (fun i => by simpa using h i) i

end Local

/-! ### The finite datum of a lattice $L = F^n\cap h\hat{\mathcal O}^n$ -/

section Global

variable {F : Type} [Field F] [NumberField F] {m : ℕ}

/-- The $v$-component of a matrix over $\mathbb A_f$. -/
abbrev matA (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) (FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) (v.adicCompletion F) :=
  X.map (evalV v)

lemma matA_inv_mul (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin (2 * m)) (FiniteAdeleRing (𝓞 F) F)) :
    matA v h.val * matA v (h⁻¹).val = 1 := by
  rw [matA, matA, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

/-- **The finite datum of the lattice $L = F^n\cap h\hat{\mathcal O}^n$**, $h \in \mathrm{GL}_n(\mathbb A_f)$: $\Phi_v = \mathbf 1_{h_v\mathcal O_v^n}$, i.e.
$\Phi_v(y) = \mathbf 1_{\mathcal O_v^n}(h_v^{-1}y)$, a Schwartz–Bruhat function at every finite place (`latIndM_mem_Sn`). Every lattice of $F^n$, free or not,
is of this form (O'Meara 81:14). -/
@[kb "kudla2008" "§1 (the factorizable datum $\\Phi_f = \\otimes_v\\Phi_v$; here $\\Phi_v = \\mathbf 1_{L_v}$) [unverified]"]
def latSA (h : GL (Fin (2 * m)) (FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)) : (localDataV v).Sn (2 * m) :=
  ⟨latIndM v (matA v (h⁻¹).val),
    latIndM_mem_Sn v _ _ (matA_inv_mul v h)⟩

/-- **$\Phi_v = \mathbf 1_{\mathcal O_v^n}$ for almost all $v$**: the entries of $h$ and $h^{-1}$ are integral at almost all places. -/
theorem eventually_latSA_eq (h : GL (Fin (2 * m)) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v in cofinite, latSA h v = oneS v m := by
  set A := h.val
  set B := (h⁻¹).val
  have hfin := (Set.finite_iUnion fun i : Fin (2 * m) => Set.finite_iUnion fun j : Fin (2 * m) =>
    (FiniteAdeleRing.finite_valued_one_lt (A i j)).union (FiniteAdeleRing.finite_valued_one_lt (B i j)))
  refine hfin.subset fun v hv => ?_
  by_contra hno
  apply hv
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or, not_lt] at hno
  refine Subtype.ext (latIndM_eq_oneV v _ _ (matA_inv_mul v h) (fun i j => (hno i j).2) (fun i j => (hno i j).1))

end Global

section Convergence

open HilbertModular QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- **The Eisenstein series of an arbitrary lattice converges for $\operatorname{Re}s > 1$.** For $F$ totally real,
$Q = \sum_{i<n}b_ix_i^2$ totally positive over $\mathcal O_F$, $n = 2m \ge 2$, the lattice $L = F^n\cap h\hat{\mathcal O}^n$ of any $h \in \mathrm{GL}_n(\mathbb A_f)$
(free or not; for instance $\mathfrak a \oplus \mathcal O_F^{n-1}$ with $\mathfrak a$ non-principal), any $g_f \in \mathrm{SL}_2(\mathbb A_f)$, $z \in \mathbb H^d$ and
$\operatorname{Re}s > 1$, the series $E((g_z, g_f), s, \varphi_\infty\otimes\bigotimes_v\mathbf 1_{L_v})$ converges absolutely over
$B(F)\backslash\mathrm{SL}_2(F)$ and equals its Bruhat expansion. -/
@[kb "weil1965" "Ch. II (convergence of the Eisenstein series) [unverified]; Kudla (2008), §1 [unverified]"]
theorem eisensteinA_latSA_converges (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (h : GL (Fin (2 * m)) (FiniteAdeleRing (𝓞 F) F))
    (gf : SL(2, FiniteAdeleRing (𝓞 F) F)) (z : InfinitePlace F → UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    (Summable fun q : BQuot F => ‖globalSecA (unitsOfInt b hb) (latSA h) gf (archSecS m z s) s q.out‖) ∧
      eisensteinA (unitsOfInt b hb) (latSA h) (eventually_latSA_eq h) gf (isArchSection_archSecS b hb hbpos z s) =
        globalSecA (unitsOfInt b hb) (latSA h) gf (archSecS m z s) s 1 +
          ∑' u : F, globalSecA (unitsOfInt b hb) (latSA h) gf (archSecS m z s) s (wMat * nMat u) :=
  eisensteinA_archSecS_converges b hb hbpos (latSA h) (eventually_latSA_eq h) gf z hs

end Convergence

end QuadFormsKB.SiegelWeil
