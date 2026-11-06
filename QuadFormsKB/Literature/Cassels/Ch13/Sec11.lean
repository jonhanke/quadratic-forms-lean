/-
# Cassels, Chapter 13, §11: Hermite reduction of isotropic forms

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §11, *Hermite reduction: isotropic forms*,
pp. 321–324: there are only finitely many classically integral Hermite-reduced forms of given determinant, isotropic
or not (Theorem 11.1), via Lemmas 11.1–11.3 (Siegel's argument).

Conventions as in `Ch13/Sec2.lean`. $J$ is the $n \times n$ matrix reversing the order of the variables
(`revMat`; Cassels' $j_{ik} = 1$ if $i + k = n + 1$, i.e. $i + k = n - 1$ with 0-based indices). Siegel domains
$\mathcal S(\delta, \eta)$ are `InSiegelDomain δ η` (Ch. 12, p. 259).
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec2
import QuadFormsKB.Literature.Cassels.Ch12.Sec4

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **The reversal matrix $J$** (Cassels, Ch. 13, §11, p. 322): $J = (j_{ik})$ with $j_{ik} = 1$ if $i + k = n - 1$
(0-based; Cassels' $i + k = n + 1$) and $0$ otherwise, so that $\vec{x} \mapsto J\vec{x}$ reverses the order of the
variables. -/
@[kb "cassels1978" "Ch. 13, §11, p. 322 (the matrix J)"]
def revMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i k => if i.val + k.val + 1 = n then 1 else 0

/-- Helper: $(JA)_{ij} = A_{n-1-i,\,j}$. -/
private theorem revMat_mul_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (revMat n * A) i j = A (Fin.rev i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [revMat, Fin.val_rev]; omega
  · intro k _ hk
    have : ¬ (i.val + k.val + 1 = n) := by
      intro h; apply hk; ext; simp [Fin.val_rev]; omega
    simp [revMat, this]
  · simp

/-- Helper: $(AJ)_{ij} = A_{i,\,n-1-j}$. -/
private theorem mul_revMat_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (A * revMat n) i j = A i (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [revMat, Fin.val_rev]; omega
  · intro k _ hk
    have : ¬ (k.val + j.val + 1 = n) := by
      intro h; apply hk; ext; simp [Fin.val_rev]; omega
    simp [revMat, this]
  · simp

/-- **(11.5)** (Cassels, Ch. 13, p. 322): $J^{\mathsf T} = J = J^{-1}$. -/
@[kb "cassels1978" "Ch. 13, §11, (11.5), p. 322"]
theorem revMat_transpose_mul_self (n : ℕ) : (revMat n)ᵀ = revMat n ∧ revMat n * revMat n = 1 := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, revMat, Matrix.of_apply]
    rw [add_comm i.val j.val]
  · ext i j
    rw [revMat_mul_apply]
    simp only [revMat, Matrix.of_apply, Matrix.one_apply, Fin.val_rev]
    have hi := i.2
    have : (n - (i.val + 1) + j.val + 1 = n) ↔ i = j := by
      rw [Fin.ext_iff]; omega
    simp only [this]

/-- **Lemma 11.1** (Cassels, Ch. 13, §11, p. 322): if $G$ is (the matrix of) a Hermite majorant of $F$ then
$$FG^{-1}F = G \tag{11.1, 11.4}$$
(Cassels states it for indefinite $f$; it holds for every regular $f$). -/
@[kb "cassels1978" "Ch. 13, §11, Lemma 11.1, (11.1)–(11.4), p. 322"]
theorem IsHermiteMajorant.mul_inv_mul {F G : Matrix (Fin n) (Fin n) ℝ} (h : IsHermiteMajorant F G) :
    F * G⁻¹ * F = G := by
  obtain ⟨L, ε, hL, hε, hF, hG⟩ := h
  have hLt : IsUnit Lᵀ.det := by rwa [Matrix.det_transpose]
  have hee : (diagonal ε) * (diagonal ε) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; rcases hε i with h | h <;> simp [h]
    · simp [hij]
  have hinv : G⁻¹ = L⁻¹ * (Lᵀ)⁻¹ := by
    rw [hG, Matrix.mul_inv_rev]
  rw [hinv, hF, hG]
  calc Lᵀ * diagonal ε * L * (L⁻¹ * (Lᵀ)⁻¹) * (Lᵀ * diagonal ε * L)
      = Lᵀ * diagonal ε * (L * L⁻¹) * ((Lᵀ)⁻¹ * Lᵀ) * diagonal ε * L := by
        simp only [Matrix.mul_assoc]
    _ = Lᵀ * L := by
        rw [Matrix.mul_nonsing_inv _ hL, Matrix.nonsing_inv_mul _ hLt, Matrix.mul_one, Matrix.mul_one,
          Matrix.mul_assoc Lᵀ, hee, Matrix.mul_one]

/-- Helper: conjugating a diagonal matrix by $J$ reverses the diagonal. -/
private theorem revMat_diagonal_revMat (v : Fin n → ℝ) :
    revMat n * diagonal v * revMat n = diagonal (fun i => v (Fin.rev i)) := by
  ext i j
  rw [Matrix.mul_assoc, revMat_mul_apply, mul_revMat_apply]
  simp only [Matrix.diagonal_apply, Fin.rev_inj]

/-- Helper: an upper unitriangular matrix has determinant $1$. -/
private theorem det_unitri {C : Matrix (Fin n) (Fin n) ℝ} (hlow : ∀ i j, j < i → C i j = 0)
    (hdiag : ∀ i, C i i = 1) : C.det = 1 := by
  rw [det_of_isUpperTriangular (fun i j hij => hlow i j hij)]
  simp [hdiag]

/-- Helper: the inverse of an upper unitriangular matrix with off-diagonal entries bounded by $E$ is upper
unitriangular with entries bounded by $(1 + nE)^n$. -/
private theorem unitri_inv {C : Matrix (Fin n) (Fin n) ℝ} (hlow : ∀ i j, j < i → C i j = 0)
    (hdiag : ∀ i, C i i = 1) {E : ℝ} (hE : 0 ≤ E) (hb : ∀ i j, i < j → |C i j| ≤ E) :
    (∀ i j, j < i → C⁻¹ i j = 0) ∧ (∀ i, C⁻¹ i i = 1) ∧ ∀ i j, |C⁻¹ i j| ≤ (1 + n * E) ^ n := by
  have hU : IsUnit C.det := by rw [det_unitri hlow hdiag]; exact isUnit_one
  have hCX : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hT : C.BlockTriangular id := fun i j hij => hlow i j hij
  have hXT : C⁻¹.BlockTriangular id := by
    have : Invertible C := Matrix.invertibleOfIsUnitDet _ hU
    exact Matrix.blockTriangular_inv_of_blockTriangular hT
  have hXlow : ∀ i j, j < i → C⁻¹ i j = 0 := fun i j hij => hXT hij
  -- row recursion
  have hrec : ∀ i j, C⁻¹ i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j - ∑ k ∈ Finset.Ioi i, C i k * C⁻¹ k j := by
    intro i j
    have h1 := congrFun (congrFun hCX i) j
    rw [Matrix.mul_apply] at h1
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.Ici i)), ← Finset.Ioi_insert,
      Finset.sum_insert Finset.notMem_Ioi_self, hdiag] at h1
    · linarith
    · intro k _ hk
      rw [hlow i k (by simpa using hk), zero_mul]
  refine ⟨hXlow, fun i => ?_, ?_⟩
  · rw [hrec, Finset.sum_eq_zero]
    · simp
    · intro k hk
      rw [hXlow k i (Finset.mem_Ioi.1 hk), mul_zero]
  · have hnE : (0 : ℝ) ≤ n * E := by positivity
    have hq : (1 : ℝ) ≤ 1 + n * E := by linarith
    have key : ∀ r : ℕ, ∀ i : Fin n, n ≤ i.val + r → ∀ j, |C⁻¹ i j| ≤ (1 + n * E) ^ r := by
      intro r
      induction r with
      | zero => intro i hi; have := i.2; omega
      | succ r ih =>
        intro i hi j
        have hsum : |∑ k ∈ Finset.Ioi i, C i k * C⁻¹ k j| ≤
            ∑ k ∈ Finset.Ioi i, E * (1 + n * E) ^ r := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          have hik : i < k := Finset.mem_Ioi.1 hk
          rw [abs_mul]
          exact mul_le_mul (hb i k hik) (ih k (by rw [Fin.lt_def] at hik; omega) j) (abs_nonneg _) hE
        have hcard : ((Finset.Ioi i).card : ℝ) ≤ n := by
          rw [Fin.card_Ioi]; have := i.2; exact_mod_cast (by omega : n - 1 - i.val ≤ n)
        have hsum2 : ∑ k ∈ Finset.Ioi i, E * (1 + n * E) ^ r ≤ n * E * (1 + n * E) ^ r := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have : 0 ≤ E * (1 + n * E) ^ r := by positivity
          nlinarith
        have hpow : (1 : ℝ) ≤ (1 + n * E) ^ r := one_le_pow₀ hq
        have h1 : |(1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ 1 := by
          by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
        rw [hrec]
        calc |(1 : Matrix (Fin n) (Fin n) ℝ) i j - ∑ k ∈ Finset.Ioi i, C i k * C⁻¹ k j|
            ≤ |(1 : Matrix (Fin n) (Fin n) ℝ) i j| + |∑ k ∈ Finset.Ioi i, C i k * C⁻¹ k j| := abs_sub _ _
          _ ≤ 1 + n * E * (1 + n * E) ^ r := by linarith
          _ ≤ (1 + n * E) ^ (r + 1) := by rw [pow_succ]; nlinarith
    intro i j
    exact key n i (by omega) j

/-- **Lemma 11.2** (Cassels, Ch. 13, §11, pp. 322–323): for every $\delta, \eta$ there is $\eta_1$, depending only on
$n, \delta, \eta$, such that if $G \in \mathcal S(\delta, \eta)$ then $JG^{-1}J \in \mathcal S(\delta, \eta_1)$. (Cassels
writes the conclusion with the same $\delta$; the proof: $G = C^{\mathsf T}HC$ gives $JG^{-1}J = C_1^{\mathsf T}H_1C_1$ with
$H_1 = JH^{-1}J$, $C_1 = JC^{-\mathsf T}J$.) -/
@[kb "cassels1978" "Ch. 13, §11, Lemma 11.2, pp. 322–323"]
theorem inSiegelDomain_rev_inv (n : ℕ) (δ η : ℝ) : ∃ η₁ : ℝ, ∀ G : Matrix (Fin n) (Fin n) ℝ,
    InSiegelDomain δ η G → InSiegelDomain δ η₁ (revMat n * G⁻¹ * revMat n) := by
  refine ⟨(1 + n * max η 0) ^ n, fun G hG => ?_⟩
  obtain ⟨h, C, ⟨hlow, hdiag, hGeq⟩, hpos, hstep, hc⟩ := hG
  have hE0 : (0 : ℝ) ≤ max η 0 := le_max_right _ _
  obtain ⟨hXlow, hXdiag, hXb⟩ := unitri_inv hlow hdiag hE0
    (fun i j hij => (hc i j hij).trans (le_max_left _ _))
  have hU : IsUnit C.det := by rw [det_unitri hlow hdiag]; exact isUnit_one
  have hCX : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hXC : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul _ hU
  have hJt := (revMat_transpose_mul_self n).1
  have hJJ := (revMat_transpose_mul_self n).2
  have hJ2 : ∀ B : Matrix (Fin n) (Fin n) ℝ, revMat n * (revMat n * B) = B := fun B => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hDD : diagonal h * diagonal (fun i => (h i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [(hpos i).ne']
    · simp [hij]
  -- the inverse of G
  have hinv : G⁻¹ = C⁻¹ * diagonal (fun i => (h i)⁻¹) * C⁻¹ᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hGeq]
    calc Cᵀ * diagonal h * C * (C⁻¹ * diagonal (fun i => (h i)⁻¹) * C⁻¹ᵀ)
        = Cᵀ * (diagonal h * (C * C⁻¹) * diagonal (fun i => (h i)⁻¹)) * C⁻¹ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hCX, Matrix.mul_one, hDD, Matrix.mul_one, ← Matrix.transpose_mul, hXC,
            Matrix.transpose_one]
  have hform : revMat n * G⁻¹ * revMat n =
      (revMat n * C⁻¹ᵀ * revMat n)ᵀ * diagonal (fun i => (h (Fin.rev i))⁻¹) * (revMat n * C⁻¹ᵀ * revMat n) := by
    rw [hinv, ← revMat_diagonal_revMat (fun i => (h i)⁻¹)]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hJt, Matrix.mul_assoc]
    simp only [hJ2]
  refine ⟨fun i => (h (Fin.rev i))⁻¹, revMat n * C⁻¹ᵀ * revMat n, ⟨?_, ?_, hform⟩, ?_, ?_, ?_⟩
  · intro i j hji
    rw [Matrix.mul_assoc, revMat_mul_apply, mul_revMat_apply, Matrix.transpose_apply]
    exact hXlow _ _ (by rw [Fin.lt_def] at hji ⊢; simp only [Fin.val_rev]; omega)
  · intro i
    rw [Matrix.mul_assoc, revMat_mul_apply, mul_revMat_apply, Matrix.transpose_apply]
    simpa using hXdiag _
  · intro i; exact inv_pos.2 (hpos _)
  · intro i j hij
    have hrev : (Fin.rev i).val = (Fin.rev j).val + 1 := by
      simp only [Fin.val_rev]; have := i.2; have := j.2; omega
    have h1 := hstep (Fin.rev j) (Fin.rev i) hrev
    have ha := hpos (Fin.rev j)
    have hb := hpos (Fin.rev i)
    show (h (Fin.rev i))⁻¹ ≤ δ * (h (Fin.rev j))⁻¹
    calc (h (Fin.rev i))⁻¹ = (h (Fin.rev j) * (h (Fin.rev i))⁻¹) * (h (Fin.rev j))⁻¹ := by
          field_simp
      _ ≤ δ * (h (Fin.rev j))⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 ha.le)
          rw [← div_eq_mul_inv, div_le_iff₀ hb]; exact h1
  · intro i j hij
    rw [Matrix.mul_assoc, revMat_mul_apply, mul_revMat_apply, Matrix.transpose_apply]
    exact hXb _ _

/-- Helper: in a Siegel domain, $h_i \le \max(\delta,1)^n\,h_j$ for $i \le j$. -/
private theorem siegel_chain {δ : ℝ} {h : Fin n → ℝ} (hpos : ∀ i, 0 < h i)
    (hstep : ∀ i j : Fin n, j.val = i.val + 1 → h i ≤ δ * h j) :
    ∀ i j : Fin n, i ≤ j → h i ≤ max δ 1 ^ n * h j := by
  have hD1 : (1 : ℝ) ≤ max δ 1 := le_max_right _ _
  have chain : ∀ k : ℕ, ∀ i j : Fin n, i.val + k = j.val → h i ≤ max δ 1 ^ k * h j := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have : i = j := Fin.ext (by simpa using hij)
      subst this
      simp
    | succ k ih =>
      intro i j hij
      have hlt : i.val + 1 < n := by have := j.2; omega
      have h1 := hstep i ⟨i.val + 1, hlt⟩ rfl
      have h2 := ih ⟨i.val + 1, hlt⟩ j (by simp; omega)
      have h3 : δ * h ⟨i.val + 1, hlt⟩ ≤ max δ 1 * h ⟨i.val + 1, hlt⟩ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos _).le
      calc h i ≤ δ * h ⟨i.val + 1, hlt⟩ := h1
        _ ≤ max δ 1 * h ⟨i.val + 1, hlt⟩ := h3
        _ ≤ max δ 1 * (max δ 1 ^ k * h j) := mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = max δ 1 ^ (k + 1) * h j := by ring
  intro i j hij
  have hk := chain (j.val - i.val) i j (by have : i.val ≤ j.val := hij; omega)
  have hle : max δ 1 ^ (j.val - i.val) ≤ max δ 1 ^ n :=
    pow_le_pow_right₀ hD1 (by have := j.2; omega)
  exact hk.trans (mul_le_mul_of_nonneg_right hle (hpos j).le)

/-- Helper: $(C\vec{x})_u = c_{uv}x$ for $\vec{x} = x\vec{e}_v$. -/
private theorem mulVec_single_aux (c : Matrix (Fin n) (Fin n) ℝ) (v u : Fin n) (x : ℝ) :
    (c *ᵥ Pi.single v x) u = c u v * x := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Helper (rounding, Cassels, Ch. 12, p. 268): for an upper unitriangular $c$, any real $\mu$ and any $i$ there is an
integral $t$ supported on $\{0, \dots, i\}$ with $|\mu_u + (ct)_u| \le 1/2$ for all $u \le i$. -/
private theorem exists_round_aux {c : Matrix (Fin n) (Fin n) ℝ} (hc1 : ∀ i, c i i = 1)
    (hc0 : ∀ i j, j < i → c i j = 0) (μ : Fin n → ℝ) (i : Fin n) :
    ∃ t : Fin n → ℤ, (∀ u, i < u → t u = 0) ∧ ∀ u, u ≤ i → |μ u + (c *ᵥ cast t) u| ≤ 1 / 2 := by
  have key : ∀ r : ℕ, ∃ t : Fin n → ℤ, (∀ u, i < u → t u = 0) ∧
      ∀ u, u ≤ i → i.val < u.val + r → |μ u + (c *ᵥ cast t) u| ≤ 1 / 2 := by
    intro r
    induction r with
    | zero => exact ⟨0, fun _ _ => rfl, fun u hu h => by omega⟩
    | succ r ih =>
      obtain ⟨t, ht0, ht⟩ := ih
      by_cases hr : r ≤ i.val
      · obtain ⟨v, hv⟩ : ∃ v : Fin n, v.val = i.val - r := ⟨⟨i.val - r, by have := i.2; omega⟩, rfl⟩
        have hvi : v ≤ i := by rw [Fin.le_def]; omega
        obtain ⟨s, hs⟩ : ∃ s : ℤ, s = -round (μ v + (c *ᵥ cast t) v) := ⟨_, rfl⟩
        have hcast : cast (t + Pi.single v s) = cast t + Pi.single v (s : ℝ) := by
          funext k
          by_cases hk : k = v <;> simp [cast, Pi.single_apply, hk]
        have hval : ∀ u, (c *ᵥ cast (t + Pi.single v s)) u = (c *ᵥ cast t) u + c u v * s := by
          intro u
          rw [hcast, Matrix.mulVec_add, Pi.add_apply, mulVec_single_aux]
        refine ⟨t + Pi.single v s, ?_, ?_⟩
        · intro u hu
          have hne : u ≠ v := fun h => absurd hu (by rw [h]; exact not_lt.2 hvi)
          simp [ht0 u hu, Pi.single_apply, hne]
        · intro u hu hlt
          rw [hval]
          rcases lt_trichotomy u v with h1 | h1 | h1
          · exfalso
            rw [Fin.lt_def] at h1
            omega
          · subst h1
            rw [hc1, hs]
            have := abs_sub_round (μ u + (c *ᵥ cast t) u)
            have e : μ u + ((c *ᵥ cast t) u + 1 * ((-round (μ u + (c *ᵥ cast t) u) : ℤ) : ℝ)) =
                μ u + (c *ᵥ cast t) u - round (μ u + (c *ᵥ cast t) u) := by push_cast; ring
            rw [e]; exact this
          · rw [hc0 u v h1, zero_mul, add_zero]
            apply ht u hu
            rw [Fin.lt_def] at h1
            omega
      · exact ⟨t, ht0, fun u hu h => ht u hu (by have := not_le.1 hr; omega)⟩
  obtain ⟨t, ht0, ht⟩ := key n
  exact ⟨t, ht0, fun u hu => ht u hu (by have := i.2; omega)⟩

/-- Helper: the determinant of the real matrix of an integral matrix. -/
private theorem det_castM (T : Matrix (Fin n) (Fin n) ℤ) : (castM T).det = ((T.det : ℤ) : ℝ) := by
  have := (Int.castRingHom ℝ).map_det T
  simpa [castM, RingHom.mapMatrix_apply] using this.symm

/-- Helper: $T^{\mathsf T}GT$ is positive definite for $G$ positive definite and $T$ of nonzero determinant. -/
private theorem posDef_act {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {T : Matrix (Fin n) (Fin n) ℤ}
    (hT : T.det ≠ 0) : (act T G).PosDef := by
  obtain ⟨hs, hpos⟩ := (posDef_iff G).1 hG
  rw [posDef_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · show (act T G)ᵀ = act T G
    unfold act
    have : Gᵀ = G := hs
    simp [Matrix.transpose_mul, this, Matrix.mul_assoc]
  · rw [val_act]
    apply hpos
    intro h0
    apply hx
    have hU : IsUnit (castM T).det := by
      rw [det_castM]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast hT)
    have := congrArg (fun z => (castM T)⁻¹ *ᵥ z) h0
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU] using this

/-- **Lemma 11.3** (Cassels, Ch. 13, §11, p. 323): let $G \in \mathcal S(\delta, \eta)$ and let $T$ be a non-singular
integral matrix. If $\vec{m}_0, \dots, \vec{m}_{n-1}$ are linearly independent integral vectors giving the successive
minima of the form with matrix $T^{\mathsf T}GT$, then the coordinates of the vectors $T\vec{m}_j$ are bounded by a
constant depending only on $n, \delta, \eta$ and $\det T$ (a generalization of Ch. 12, Lemma 4.2, Corollary,
`lemma_4_2_cor`, which is the case $T = I$). -/
@[kb "cassels1978" "Ch. 13, §11, Lemma 11.3, p. 323"]
theorem lemma_11_3 (n : ℕ) (δ η : ℝ) (D : ℤ) : ∃ C : ℝ, ∀ (G : Matrix (Fin n) (Fin n) ℝ)
    (T : Matrix (Fin n) (Fin n) ℤ), InSiegelDomain δ η G → T.det = D → D ≠ 0 →
    ∀ m : Fin n → Fin n → ℤ, LinearIndependent ℝ (fun j => cast (m j)) →
      (∀ j, val (act T G) (cast (m j)) = succMin (act T G) j) → ∀ i j : Fin n, |((T *ᵥ m j) i : ℝ)| ≤ C := by
  obtain ⟨C1, hC1pos, hC1⟩ := lemma_4_1 n δ η
  have hD1 : (1 : ℝ) ≤ max δ 1 := le_max_right _ _
  have hDn : (1 : ℝ) ≤ max δ 1 ^ n := one_le_pow₀ hD1
  have hE0 : (0 : ℝ) ≤ max η 0 := le_max_right _ _
  set N : ℝ := (D.natAbs : ℝ) with hN
  set A0 : ℝ := C1 * max δ 1 ^ n * N ^ 2 + n * max δ 1 ^ n * N ^ 2 + 1 with hA0
  refine ⟨n * ((1 + n * max η 0) ^ n * A0), ?_⟩
  intro G T hG hT hD m hLI hm i0 J
  obtain ⟨h, c, hd, hpos, hstep, hc⟩ := id hG
  have hchain := siegel_chain hpos hstep
  have hP := hG.posDef
  have hTne : T.det ≠ 0 := by rw [hT]; exact hD
  have hHP := posDef_act hP hTne
  have hNpos : 0 < N := by
    rw [hN]; exact_mod_cast Int.natAbs_pos.2 hD
  -- the integral matrix A with T A = N
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s * D = (D.natAbs : ℤ) := by
    rcases lt_or_gt_of_ne hD with h | h
    · exact ⟨-1, by omega⟩
    · exact ⟨1, by omega⟩
  set A : Matrix (Fin n) (Fin n) ℤ := s • T.adjugate with hAdef
  have hTA : T * A = (D.natAbs : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
    rw [hAdef, Matrix.mul_smul, Matrix.mul_adjugate, hT, smul_smul, hs]
  have hTAv : ∀ a : Fin n → ℤ, T *ᵥ (A *ᵥ a) = (D.natAbs : ℤ) • a := by
    intro a
    rw [Matrix.mulVec_mulVec, hTA, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hTAr : ∀ a : Fin n → ℤ, cast (T *ᵥ (A *ᵥ a)) = N • cast a := by
    intro a
    rw [hTAv]; funext k; simp [cast, hN]
  have hvalA : ∀ a : Fin n → ℤ, val (act T G) (cast (A *ᵥ a)) = N ^ 2 * val G (cast a) := by
    intro a
    rw [val_act_cast, hTAr, val_smul]
  -- the vector b = T m_J and its coordinates
  set b : Fin n → ℝ := cast (T *ᵥ m J) with hb
  set μ : Fin n → ℝ := c *ᵥ b with hμ
  have hMJ : succMin (act T G) J = ∑ u, h u * μ u ^ 2 := by
    rw [← hm J, val_act_cast, ← hb, val_eq_of_isSqDecomp hd, hμ]
  have hterm : ∀ i, h i * μ i ^ 2 ≤ succMin (act T G) J := by
    intro i
    rw [hMJ]
    exact Finset.single_le_sum (f := fun u => h u * μ u ^ 2)
      (fun u _ => mul_nonneg (hpos u).le (sq_nonneg _)) (Finset.mem_univ i)
  have hbound : ∀ i, |μ i| ≤ A0 := by
    intro i
    have hhi := hpos i
    suffices hB : μ i ^ 2 ≤ C1 * max δ 1 ^ n * N ^ 2 + n * max δ 1 ^ n * N ^ 2 by
      have : |μ i| ≤ μ i ^ 2 + 1 := by nlinarith [sq_abs (μ i), sq_nonneg (|μ i| - 1)]
      rw [hA0]; linarith
    have hN2 : 0 ≤ N ^ 2 := by positivity
    by_cases hcase : ∃ u, u ≤ i ∧ succMin (act T G) J ≤ N ^ 2 * G u u
    · obtain ⟨u, hui, hu⟩ := hcase
      have h41 := hC1 G hG h c hd u
      have hle : succMin (act T G) J ≤ N ^ 2 * (C1 * (max δ 1 ^ n * h i)) :=
        calc succMin (act T G) J ≤ N ^ 2 * G u u := hu
          _ ≤ N ^ 2 * (C1 * h u) := mul_le_mul_of_nonneg_left h41.2.1 hN2
          _ ≤ N ^ 2 * (C1 * (max δ 1 ^ n * h i)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hchain u i hui) hC1pos.le) hN2
      have h1 : h i * μ i ^ 2 ≤ h i * (C1 * max δ 1 ^ n * N ^ 2) := by
        calc h i * μ i ^ 2 ≤ _ := (hterm i).trans hle
          _ = _ := by ring
      have := le_of_mul_le_mul_left h1 hhi
      have : 0 ≤ n * max δ 1 ^ n * N ^ 2 := by positivity
      linarith
    · push_neg at hcase
      obtain ⟨t, ht0, htr⟩ := exists_round_aux hd.2.1 hd.1 (fun u => μ u / N) i
      obtain ⟨a, ha⟩ : ∃ a : Fin n → ℝ, a = c *ᵥ cast t := ⟨_, rfl⟩
      rw [← ha] at htr
      have ha0 : ∀ u, i < u → a u = 0 := by
        intro u hu
        rw [ha, Matrix.mulVec, dotProduct]
        refine Finset.sum_eq_zero fun v _ => ?_
        by_cases hv : v ≤ i
        · rw [hd.1 u v (lt_of_le_of_lt hv hu), zero_mul]
        · rw [show cast t v = 0 by simp [cast, ht0 v (not_le.1 hv)], mul_zero]
      -- the integral vector m_J + A t
      have hcastadd : cast (m J + A *ᵥ t) = cast (m J) + cast (A *ᵥ t) := by
        funext k; simp [cast]
      have hTc : cast (T *ᵥ (m J + A *ᵥ t)) = b + N • cast t := by
        have : T *ᵥ (m J + A *ᵥ t) = T *ᵥ m J + (D.natAbs : ℤ) • t := by
          rw [Matrix.mulVec_add, hTAv]
        rw [this]
        funext k; simp [cast, hb, hN]
      have hmstar : succMin (act T G) J ≤ val (act T G) (cast (m J + A *ᵥ t)) := by
        by_contra hlt
        push_neg at hlt
        have hmem := mem_span_of_val_lt_succMin hHP hLI hm (j := J) (c := m J + A *ᵥ t) hlt
        have hsingle : ∀ u, u ≤ i → cast (A *ᵥ (Pi.single u 1 : Fin n → ℤ)) ∈
            Submodule.span ℝ (Set.image (fun i => cast (m i)) {i | i < J}) := by
          intro u hu
          refine mem_span_of_val_lt_succMin hHP hLI hm (j := J) (c := A *ᵥ (Pi.single u 1 : Fin n → ℤ)) ?_
          rw [hvalA, cast_single, val_single]; exact hcase u hu
        have hAt : cast (A *ᵥ t) = ∑ u, (cast t u) • cast (A *ᵥ (Pi.single u 1 : Fin n → ℤ)) := by
          funext k
          simp [Matrix.mulVec, dotProduct, cast, Pi.single_apply, Finset.sum_apply, mul_comm]
        have htmem : cast (A *ᵥ t) ∈ Submodule.span ℝ (Set.image (fun i => cast (m i)) {i | i < J}) := by
          rw [hAt]
          refine Submodule.sum_mem _ fun u _ => ?_
          by_cases hu : u ≤ i
          · exact Submodule.smul_mem _ _ (hsingle u hu)
          · simp [cast, ht0 u (not_le.1 hu)]
        have hJ : cast (m J) ∈ Submodule.span ℝ (Set.image (fun i => cast (m i)) {i | i < J}) := by
          have : cast (m J) = cast (m J + A *ᵥ t) - cast (A *ᵥ t) := by rw [hcastadd]; abel
          rw [this]
          exact Submodule.sub_mem _ hmem htmem
        exact hLI.notMem_span_image (s := {i | i < J}) (x := J) (by simp) hJ
      have hval : val (act T G) (cast (m J + A *ᵥ t)) = ∑ u, h u * (μ u + N * a u) ^ 2 := by
        rw [val_act_cast, hTc, val_eq_of_isSqDecomp hd, Matrix.mulVec_add, Matrix.mulVec_smul, ← hμ, ← ha]
        simp [smul_eq_mul]
      rw [hval, hMJ] at hmstar
      have hg : ∑ u, (h u * (μ u + N * a u) ^ 2 - h u * μ u ^ 2) =
          ∑ u ∈ Finset.Iic i, (h u * (μ u + N * a u) ^ 2 - h u * μ u ^ 2) := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun u _ hu => ?_
        have : a u = 0 := ha0 u (by simpa using hu)
        simp [this]
      have hg0 : 0 ≤ ∑ u ∈ Finset.Iic i, (h u * (μ u + N * a u) ^ 2 - h u * μ u ^ 2) := by
        rw [← hg, Finset.sum_sub_distrib]
        linarith
      rw [Finset.sum_sub_distrib] at hg0
      have h2 : h i * μ i ^ 2 ≤ ∑ u ∈ Finset.Iic i, h u * μ u ^ 2 :=
        Finset.single_le_sum (f := fun u => h u * μ u ^ 2)
          (fun u _ => mul_nonneg (hpos u).le (sq_nonneg _)) (Finset.mem_Iic.2 le_rfl)
      have h3 : ∑ u ∈ Finset.Iic i, h u * (μ u + N * a u) ^ 2 ≤
          ∑ u ∈ Finset.Iic i, max δ 1 ^ n * h i * N ^ 2 / 4 := by
        refine Finset.sum_le_sum fun u hu => ?_
        have hui := Finset.mem_Iic.1 hu
        have hq : (μ u + N * a u) ^ 2 ≤ N ^ 2 / 4 := by
          have h1 := abs_le.1 (htr u hui)
          have e : μ u + N * a u = N * (μ u / N + a u) := by field_simp
          rw [e, mul_pow]
          have : (μ u / N + a u) ^ 2 ≤ 1 / 4 := by nlinarith [h1.1, h1.2]
          nlinarith
        calc h u * (μ u + N * a u) ^ 2 ≤ h u * (N ^ 2 / 4) :=
              mul_le_mul_of_nonneg_left hq (hpos u).le
          _ = h u * N ^ 2 / 4 := by ring
          _ ≤ max δ 1 ^ n * h i * N ^ 2 / 4 := by
              have := hchain u i hui
              have : h u * N ^ 2 ≤ max δ 1 ^ n * h i * N ^ 2 :=
                mul_le_mul_of_nonneg_right this hN2
              linarith
      have h4 : ∑ u ∈ Finset.Iic i, max δ 1 ^ n * h i * N ^ 2 / 4 ≤ n * max δ 1 ^ n * h i * N ^ 2 / 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.Iic i).card : ℝ) ≤ n := by
          rw [Fin.card_Iic]; exact_mod_cast i.2
        have : 0 ≤ max δ 1 ^ n * h i * N ^ 2 := by positivity
        nlinarith
      have h5 : h i * μ i ^ 2 ≤ h i * (n * max δ 1 ^ n * N ^ 2) := by
        have : 0 ≤ n * max δ 1 ^ n * h i * N ^ 2 := by positivity
        nlinarith
      have := le_of_mul_le_mul_left h5 hhi
      have : 0 ≤ C1 * max δ 1 ^ n * N ^ 2 := by positivity
      linarith
  -- back-substitution: b = C⁻¹ μ
  obtain ⟨-, -, hXb⟩ := unitri_inv hd.1 hd.2.1 hE0 (fun i j hij => (hc i j hij).trans (le_max_left _ _))
  have hU : IsUnit c.det := by rw [det_unitri hd.1 hd.2.1]; exact isUnit_one
  have hbX : b = c⁻¹ *ᵥ μ := by
    rw [hμ, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
  have hA0pos : 0 ≤ A0 := by rw [hA0]; positivity
  have : |((T *ᵥ m J) i0 : ℝ)| = |b i0| := rfl
  rw [this, hbX, Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |c⁻¹ i0 k * μ k| ≤ ∑ k : Fin n, (1 + n * max η 0) ^ n * A0 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hXb i0 k) (hbound k) (abs_nonneg _) (by positivity)
    _ = _ := by simp

/-- Helper: the integral matrix $JF_{\mathbb Z}$ (rows reversed). -/
private def revRows (Fz : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => Fz (Fin.rev i) j

/-- Helper: $\overline{JF_{\mathbb Z}} = J\overline{F_{\mathbb Z}}$. -/
private theorem castM_revRows (Fz : Matrix (Fin n) (Fin n) ℤ) : castM (revRows Fz) = revMat n * castM Fz := by
  ext i j
  rw [revMat_mul_apply]
  simp [castM, revRows]

/-- Helper: a classically integral form has an integral matrix $F_{\mathbb Z}$ with $\overline{F_{\mathbb Z}} = F$. -/
private theorem exists_castM_realMat {Q : IntQF n} (hci : IsClassicallyIntegral Q) :
    ∃ Fz : Matrix (Fin n) (Fin n) ℤ, castM Fz = realMat Q ∧ ∀ i j, Q.hessian i j = 2 * Fz i j := by
  have h2 : ∀ i j : Fin n, (2 : ℤ) ∣ Q.hessian i j := by
    intro i j
    rw [isClassicallyIntegral_iff] at hci
    simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [Q.upper h, add_zero]; exact even_iff_two_dvd.mp (hci i j h)
    · subst h; exact ⟨Q.coeff i i, by ring⟩
    · rw [Q.upper h, zero_add]; exact even_iff_two_dvd.mp (hci j i h)
  choose k hk using h2
  refine ⟨Matrix.of k, ?_, hk⟩
  ext i j
  have : (Q.hessian i j : ℝ) = 2 * (k i j : ℝ) := by exact_mod_cast hk i j
  simp [castM, realMat, this]

/-- Helper: a form is determined by its real matrix. -/
private theorem eq_of_realMat_eq' {Q Q' : IntQF n} (h : realMat Q = realMat Q') : Q = Q' := by
  apply QuadForm.eq_of_eval_eq
  intro x
  have h1 : ((Q.eval x : ℤ) : ℝ) = val (realMat Q) (cast x) := by
    rw [← QuadForm.evalIn_real_eq_val]
    simp [QuadForm.evalIn, cast]
  have h2 : ((Q'.eval x : ℤ) : ℝ) = val (realMat Q') (cast x) := by
    rw [← QuadForm.evalIn_real_eq_val]
    simp [QuadForm.evalIn, cast]
  rw [h] at h1
  exact_mod_cast h1.trans h2.symm

/-- Helper (as in Ch. 12, Thm. 1.4): if $TQ = P$ with $Q$ having linearly independent columns and $P$, $Q$
bounded by $K \ge 1$ then $T$ is bounded by $n\,K\,n!\,K^n$. -/
private theorem bound_of_mul (T Qz Pz : Matrix (Fin n) (Fin n) ℤ) (K : ℝ) (hK1 : 1 ≤ K)
    (hTQ : T * Qz = Pz) (hLI : LinearIndependent ℝ (castM Qz).col)
    (hPb : ∀ a b, |(Pz a b : ℝ)| ≤ K) (hQb : ∀ a b, |(Qz a b : ℝ)| ≤ K) (i j : Fin n) :
    |(T i j : ℝ)| ≤ n * (K * ((n.factorial : ℝ) * K ^ n)) := by
  have hTQr : castM T * castM Qz = castM Pz := by
    rw [← castM_mul, hTQ]
  have hdetQ : (castM Qz).det ≠ 0 := by
    have h2 := (Matrix.linearIndependent_col_iff_isUnit.1 hLI)
    exact (isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 h2))
  have hcd : (castM Qz).det = ((Qz.det : ℤ) : ℝ) := by
    have := (Int.castRingHom ℝ).map_det Qz
    simpa [castM, RingHom.mapMatrix_apply] using this.symm
  have hdetQz : Qz.det ≠ 0 := by
    intro h0
    apply hdetQ
    rw [hcd, h0]; simp
  have hone : (1 : ℝ) ≤ |(castM Qz).det| := by
    rw [hcd]
    have := Int.one_le_abs hdetQz
    exact_mod_cast this
  have hid : (castM Qz).det • castM T = castM Pz * (castM Qz).adjugate := by
    rw [← hTQr, Matrix.mul_assoc, Matrix.mul_adjugate]
    simp
  have hentry : (castM Qz).det * (T i j : ℝ) = (castM Pz * (castM Qz).adjugate) i j := by
    have := congrFun (congrFun hid i) j
    simpa [castM] using this
  have hPb' : ∀ a b, |castM Pz a b| ≤ K := hPb
  have hQb' : ∀ a b, |castM Qz a b| ≤ K := hQb
  have hadj : ∀ a b, |(castM Qz).adjugate a b| ≤ (n.factorial : ℝ) * K ^ n := by
    intro a b
    rw [Matrix.adjugate_apply]
    have := Matrix.det_le (A := (castM Qz).updateRow b (Pi.single a 1))
      (abv := AbsoluteValue.abs) (x := K) (fun p q => by
        show |(castM Qz).updateRow b (Pi.single a 1) p q| ≤ K
        rw [Matrix.updateRow_apply]
        split_ifs
        · by_cases h : q = a <;> simp [Pi.single_apply, h] <;> linarith
        · exact hQb' p q)
    simpa [Fintype.card_fin, nsmul_eq_mul] using this
  have hprod : |(castM Pz * (castM Qz).adjugate) i j| ≤ n * (K * ((n.factorial : ℝ) * K ^ n)) := by
    rw [Matrix.mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |castM Pz i k * (castM Qz).adjugate k j|
        ≤ ∑ k : Fin n, K * ((n.factorial : ℝ) * K ^ n) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hPb' i k) (hadj k j) (abs_nonneg _) (by linarith)
      _ = _ := by simp
  have hfin : |(T i j : ℝ)| ≤ |(castM Qz).det| * |(T i j : ℝ)| :=
    le_mul_of_one_le_left (abs_nonneg _) hone
  rw [← abs_mul, hentry] at hfin
  exact hfin.trans hprod

/-- **Theorem 11.1** (Cassels, Ch. 13, §11, pp. 322–324): there are only finitely many classically integral
Hermite-reduced forms of given determinant $d \ne 0$, isotropic or not (this removes "anisotropic" from Theorem 2.1,
`finite_isMajorantReduced`). Classically integral: `IsClassicallyIntegral`; $d(f) = \det F$ with $F$ = `realMat Q`. -/
@[kb "cassels1978" "Ch. 13, §11, Thm. 11.1, pp. 322–324"]
theorem finite_isMajorantReduced_classical (n : ℕ) (d : ℝ) (hd : d ≠ 0) :
    {Q : IntQF n | IsClassicallyIntegral Q ∧ (realMat Q).det = d ∧ IsMajorantReduced (realMat Q)}.Finite := by
  classical
  obtain ⟨δ, η, hR⟩ := exists_siegelDomain_of_isMinkowskiReduced n
  obtain ⟨C0, hC0⟩ := lemma_4_2_cor n δ η
  obtain ⟨η₁, hη₁⟩ := inSiegelDomain_rev_inv n δ η
  have hJt := (revMat_transpose_mul_self n).1
  have hJJ := (revMat_transpose_mul_self n).2
  have hJ2 : ∀ B : Matrix (Fin n) (Fin n) ℝ, revMat n * (revMat n * B) = B := fun B => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hdetJ : (revMat n).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hJJ
    rw [Matrix.det_mul, h0] at this
    simp at this
  -- the determinant of the integral matrix attached to a form in the set
  have hdetTz : ∀ Fz : Matrix (Fin n) (Fin n) ℤ, (castM Fz).det = d →
      (((revRows Fz).det : ℤ) : ℝ) = (revMat n).det * d := by
    intro Fz hFz
    rw [← det_castM, castM_revRows, Matrix.det_mul, hFz]
  by_cases hex : ∃ D : ℤ, (D : ℝ) = (revMat n).det * d
  swap
  · convert Set.finite_empty
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hci hdet _
    obtain ⟨Fz, hFz, -⟩ := exists_castM_realMat hci
    exact hex ⟨_, hdetTz Fz (by rw [hFz]; exact hdet)⟩
  obtain ⟨D, hD⟩ := hex
  have hD0 : D ≠ 0 := by
    intro h0
    rw [h0] at hD
    simp at hD
    rcases hD with h | h
    · exact hdetJ h
    · exact hd h
  obtain ⟨C3, hC3⟩ := lemma_11_3 n δ η₁ D
  set K : ℝ := max (max C0 C3) 1 with hK
  have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
  set B : ℝ := n * (K * ((n.factorial : ℝ) * K ^ n)) with hB
  -- the key bound
  have key : ∀ Q ∈ {Q : IntQF n | IsClassicallyIntegral Q ∧ (realMat Q).det = d ∧
      IsMajorantReduced (realMat Q)}, ∀ i j, |(Q.hessian i j : ℝ)| ≤ 2 * B := by
    rintro Q ⟨hci, hdet, G, hGH, hGred⟩ i j
    obtain ⟨Fz, hFz, hhess⟩ := exists_castM_realMat hci
    have hFs : (realMat Q).IsSymm := hGH.isSymm_det_ne_zero.1
    have hGpd := hGH.posDef
    have hSig : InSiegelDomain δ η G := hR G hGred
    obtain ⟨m, hLI, hm⟩ := exists_succMin_vectors hGpd
    have hm0 := hC0 G hSig m hLI hm
    have hSig1 := hη₁ G hSig
    set G' := revMat n * G⁻¹ * revMat n with hG'
    set Tz := revRows Fz with hTz
    have hTzr : castM Tz = revMat n * realMat Q := by rw [hTz, castM_revRows, hFz]
    have hGeq : act Tz G' = G := by
      have h11 := hGH.mul_inv_mul
      unfold act
      rw [hTzr, Matrix.transpose_mul, hFs.eq, hJt, hG']
      conv_rhs => rw [← h11]
      simp only [Matrix.mul_assoc]
      simp only [hJ2]
    have hdetT : Tz.det = D := by
      have h1 := hdetTz Fz (by rw [hFz]; exact hdet)
      have : ((Tz.det : ℤ) : ℝ) = (D : ℝ) := by rw [hD, ← h1]
      exact_mod_cast this
    have hm' : ∀ j, val (act Tz G') (cast (m j)) = succMin (act Tz G') j := by
      rw [hGeq]; exact hm
    have hb := hC3 G' Tz hSig1 hdetT hD0 m hLI hm'
    set Qz : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun a b => m b a with hQz
    set Pz : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun a b => (Tz *ᵥ m b) a with hPz
    have hTQ : Tz * Qz = Pz := by
      ext a b
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hQz, hPz]
    have hTb : ∀ a b, |(Tz a b : ℝ)| ≤ B :=
      fun a b => bound_of_mul Tz Qz Pz K hK1 hTQ hLI
        (fun a b => (hb a b).trans ((le_max_right _ _).trans (le_max_left _ _)))
        (fun a b => (hm0 a b).trans ((le_max_left _ _).trans (le_max_left _ _))) a b
    have h1 := hTb (Fin.rev i) j
    have h2 : Tz (Fin.rev i) j = Fz i j := by simp [hTz, revRows]
    rw [h2] at h1
    have h3 : (Q.hessian i j : ℝ) = 2 * (Fz i j : ℝ) := by exact_mod_cast hhess i j
    rw [h3, abs_mul]
    norm_num
    linarith
  -- finiteness
  set N : ℕ := ⌈2 * B⌉₊ with hN
  have hinj : Set.InjOn (fun Q : IntQF n => Q.hessian)
      {Q : IntQF n | IsClassicallyIntegral Q ∧ (realMat Q).det = d ∧ IsMajorantReduced (realMat Q)} := by
    intro Q _ Q' _ h
    apply eq_of_realMat_eq'
    show (1 / 2 : ℝ) • Q.hessian.map (algebraMap ℤ ℝ) = (1 / 2 : ℝ) • Q'.hessian.map (algebraMap ℤ ℝ)
    have h' : Q.hessian = Q'.hessian := h
    rw [h']
  refine Set.Finite.of_finite_image ?_ hinj
  have hfin : (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Set.Icc (-(N : ℤ)) N).Finite :=
    Set.Finite.pi (fun _ => Set.Finite.pi (fun _ => Set.finite_Icc _ _))
  refine hfin.subset ?_
  rintro _ ⟨Q, hQ, rfl⟩ i _ j _
  have h1 := key Q hQ i j
  have h3 : |((Q.hessian i j : ℤ) : ℝ)| ≤ N := by
    have := Nat.le_ceil (2 * B)
    rw [← hN] at this
    linarith
  have h4 : |Q.hessian i j| ≤ N := by exact_mod_cast h3
  exact abs_le.1 h4

end QuadFormsKB.Reduction
