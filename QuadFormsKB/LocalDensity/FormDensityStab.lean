/-
# Densities of forms by forms over a DVR: stabilization and existence of the limit

**Layer:** DVR, every residue characteristic (dyadic primes included).

**Proves** Siegel's stabilization (Siegel 1935, Hilfssatz 13; Kitaoka 1993, §5.6 [unverified]) in the repo's
quadratic-form convention: for $Q$ in $n$ variables, $T$ in $r$ variables with $\det H_T \ne 0$,
$d = \mathrm{ord}_\pi \det H_T$ and $k \ge 2d + 1$,
$$A_{\pi^{k+1}}(Q, T)\, q^{r(r+1)/2} = q^{nr}\, A_{\pi^k}(Q, T) \qquad (\texttt{repCountForm\_succ}),$$
so for $r \le n$ the normalized counts $A_{\pi^k}(Q, T)/q^{k(nr - r(r+1)/2)}$ are constant for $k \ge 2d + 1$ and the
limit $\beta_\pi(Q, T)$ exists (`localDensityForm_eventually_eq`, `localDensityForm_eq`). No hypothesis on $Q$
(not even nondegeneracy) and no restriction $r < n$: the case $n = r$, $T = Q$ is the self-density
(`FormDensitySelf.lean`). When $H_T$ is invertible mod $\pi$ ($d = 0$) the counts are constant from $k = 1$:
$\beta_\pi(Q, T) = A_\pi(Q, T)/q^{nr - r(r+1)/2}$, a count over the residue field.

*Proof.* `card_sol_succ` (`FormDensityHensel.lean`) for the quadratic map
$X \mapsto Q \circ X$ on $M_{n\times r}(R) = R^{n \times r}$ with values in the upper-triangular coefficients
$R^{\{i \le j\}}$; its differential at $X$ is $W \mapsto (Z_{ii},\ Z_{ij} + Z_{ji})_{i < j}$ with $Z = X^{\mathsf T} H_Q W$
(`formD`). At a solution mod $\pi^k$, $G = X^{\mathsf T} H_Q X \equiv H_T$, so $\det G = \pi^d u'$ with $u'$ a unit
($k > d$), and $W = X\,\mathrm{adj}(G)\,u'^{-1} Z$ gives $X^{\mathsf T} H_Q W = \pi^d Z$ for any upper-triangular $Z$:
the image contains $\pi^d R^{\{i\le j\}}$ (`formD_surj`).

*Comparison with Lemma 3.2 / `DVRDepth`.* For $r = 1$, $T = \langle m\rangle$: $H_T = (2m)$, $d = \mathrm{ord}_\pi(2m)$,
so this recovers the stabilization of $r_{\pi^k}(m)$ from $k \ge 2\,\mathrm{ord}_\pi(2m) + 1$ for **every** $Q$
(`repCountForm_unary`), a uniform bound; `DVRDepth.lean` has sharper, $Q$-dependent bounds.
**Depends on** `FormDensityHensel.lean`.
-/
import QuadFormsKB.LocalDensity.FormDensityHensel

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n r : ℕ}

/-! ### The quadratic map `X ↦ Q ∘ X` in coordinates -/

/-- The index set of the upper-triangular coefficients of a form in $r$ variables: $\{(i, j) : i \le j\}$. -/
abbrev UpperIdx (r : ℕ) := {p : Fin r × Fin r // p.1 ≤ p.2}

/-- $\#\{(i, j) : 0 \le i \le j < r\} = r(r+1)/2$. -/
theorem card_upperIdx (r : ℕ) : Fintype.card (UpperIdx r) = r * (r + 1) / 2 := by
  classical
  let e : UpperIdx r ≃ Sym2 (Fin r) :=
    { toFun := fun p => s(p.1.1, p.1.2)
      invFun := Sym2.lift ⟨fun a b => ⟨(min a b, max a b), min_le_max⟩, fun a b => by
        apply Subtype.ext; simp [min_comm, max_comm]⟩
      left_inv := fun p => by
        apply Subtype.ext
        simp [min_eq_left p.2, max_eq_right p.2]
      right_inv := fun s => by
        induction s using Sym2.ind with
        | h a b =>
          simp only [Sym2.lift_mk]
          rcases le_total a b with h | h
          · simp [min_eq_left h, max_eq_right h]
          · simp [min_eq_right h, max_eq_left h, Sym2.eq_swap] }
  rw [Fintype.card_congr e, Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel,
    mul_comm]

/-- The matrix with entries $x_{(l, i)}$. -/
def toMat {A : Type*} (x : Fin n × Fin r → A) : Matrix (Fin n) (Fin r) A := Matrix.of fun l i => x (l, i)

/-- The bilinear form $B_Q(\vec u, \vec v) = \vec u^{\mathsf T} H_Q \vec v$. -/
def bil (Q : QuadForm R n) (u v : Fin n → R) : R := u ⬝ᵥ (Q.hessian *ᵥ v)

theorem bil_comm (Q : QuadForm R n) (u v : Fin n → R) : bil Q u v = bil Q v u := by
  unfold bil
  rw [← Matrix.dotProduct_transpose_mulVec, hessian_transpose]

/-- The $i$-th column of a matrix. -/
def col {A : Type*} (X : Matrix (Fin n) (Fin r) A) (i : Fin r) : Fin n → A := fun l => X l i

/-- The coefficients of $Q \circ X$ on and above the diagonal, as a vector indexed by `UpperIdx r`. -/
def formF (Q : QuadForm R n) (x : Fin n × Fin r → R) : UpperIdx r → R :=
  fun p => (Q.compMat (toMat x)).coeff p.1.1 p.1.2

theorem formF_apply (Q : QuadForm R n) (x : Fin n × Fin r → R) (p : UpperIdx r) :
    formF Q x p = if p.1.1 = p.1.2 then Q.eval (col (toMat x) p.1.1)
      else bil Q (col (toMat x) p.1.1) (col (toMat x) p.1.2) := by
  simp only [formF, compMat_coeff, if_pos p.2]
  rfl

theorem col_toMat_add (x w : Fin n × Fin r → R) (i : Fin r) :
    col (toMat (x + w)) i = col (toMat x) i + col (toMat w) i := rfl

theorem col_toMat_smul (c : R) (w : Fin n × Fin r → R) (i : Fin r) :
    col (toMat (c • w)) i = c • col (toMat w) i := rfl

theorem col_toMat_add_smul (x w : Fin n × Fin r → R) (c : R) (i : Fin r) :
    col (toMat (x + c • w)) i = col (toMat x) i + c • col (toMat w) i := rfl

/-- **The differential of $X \mapsto Q \circ X$** at $X$: $W \mapsto (B_Q(X_i, W_i))_{i}$ on the diagonal and
$B_Q(X_i, W_j) + B_Q(W_i, X_j)$ above it. -/
def formD (Q : QuadForm R n) (x : Fin n × Fin r → R) : (Fin n × Fin r → R) →ₗ[R] (UpperIdx r → R) where
  toFun w := fun p => if p.1.1 = p.1.2 then bil Q (col (toMat x) p.1.1) (col (toMat w) p.1.1)
    else bil Q (col (toMat x) p.1.1) (col (toMat w) p.1.2) + bil Q (col (toMat w) p.1.1) (col (toMat x) p.1.2)
  map_add' w w' := by
    funext p
    simp only [Pi.add_apply, col_toMat_add, bil, mulVec_add, dotProduct_add, add_dotProduct]
    split_ifs <;> ring
  map_smul' c w := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, col_toMat_smul, bil, mulVec_smul,
      dotProduct_smul, smul_dotProduct]
    split_ifs <;> ring

/-- **Taylor expansion** of $X \mapsto Q \circ X$: $Q\circ(X + cW) = Q \circ X + c\,D_X W + c^2\, Q \circ W$. -/
theorem formF_add_smul (Q : QuadForm R n) (x w : Fin n × Fin r → R) (c : R) :
    formF Q (x + c • w) = formF Q x + c • formD Q x w + c ^ 2 • formF Q w := by
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, formF_apply, col_toMat_add_smul]
  show _ = _ + c * (if p.1.1 = p.1.2 then _ else _) + _
  split_ifs with h
  · rw [eval_add_smul', dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, hessian_transpose]
    rfl
  · simp only [bil, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    ring

/-! ### The image of the differential -/

/-- $(X^{\mathsf T} C W)_{ab} = X_a^{\mathsf T} C W_b$. -/
theorem transpose_mul_mul_apply₂ {A : Type*} [CommRing A] (C : Matrix (Fin n) (Fin n) A)
    (X W : Matrix (Fin n) (Fin r) A) (a b : Fin r) :
    (Xᵀ * C * W) a b = (fun l => X l a) ⬝ᵥ (C *ᵥ fun l => W l b) := by
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- **The image of the differential contains $\pi^d R^{\{i \le j\}}$** at every solution mod $\pi^k$, when
$\pi^d \,\|\, \det H_T$ and $k > d$. -/
theorem formD_surj (Q : QuadForm R n) (T : QuadForm R r) (π : R) (hπ : Irreducible π) (d k : ℕ)
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det) (hdk : d < k)
    (x : Fin n × Fin r → R) (hx : ∀ p, π ^ k ∣ formF Q x p - T.coeff p.1.1 p.1.2) (c : UpperIdx r → R) :
    ∃ w, formD Q x w = π ^ d • c := by
  classical
  set X := toMat x with hX
  set G : Matrix (Fin r) (Fin r) R := Xᵀ * Q.hessian * X with hG
  have hGh : G = (Q.compMat X).hessian := (hessian_compMat Q X).symm
  -- `G ≡ H_T` entrywise
  have hcoeff : ∀ a b, π ^ k ∣ (Q.compMat X).coeff a b - T.coeff a b := by
    intro a b
    by_cases hab : a ≤ b
    · exact hx ⟨(a, b), hab⟩
    · rw [(Q.compMat X).upper (show id b < id a from not_le.mp hab),
        T.upper (show id b < id a from not_le.mp hab), sub_zero]
      exact dvd_zero _
  have hGT : ∀ a b, π ^ k ∣ G a b - T.hessian a b := by
    intro a b
    rw [hGh]
    simp only [hessian, Matrix.add_apply, Matrix.transpose_apply]
    rw [show (Q.compMat X).coeff a b + (Q.compMat X).coeff b a - (T.coeff a b + T.coeff b a) =
      ((Q.compMat X).coeff a b - T.coeff a b) + ((Q.compMat X).coeff b a - T.coeff b a) by ring]
    exact dvd_add (hcoeff a b) (hcoeff b a)
  have hdet : π ^ k ∣ G.det - T.hessian.det := by
    have hmap : (Ideal.Quotient.mk (Ideal.span {π ^ k})).mapMatrix G =
        (Ideal.Quotient.mk (Ideal.span {π ^ k})).mapMatrix T.hessian := by
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact hGT a b
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, hmap]
  obtain ⟨u, hu, huu⟩ := dvr_exact hπ hd hd'
  obtain ⟨s, hs⟩ := hdet
  have hGdet : G.det = π ^ d * (u + π ^ (k - d) * s) := by
    rw [mul_add, ← mul_assoc, ← pow_add, show d + (k - d) = k by omega, ← hs, ← hu]; ring
  have hu' : IsUnit (u + π ^ (k - d) * s) := by
    apply dvr_isUnit_of_not_dvd hπ
    intro h
    apply dvr_not_dvd_of_isUnit hπ huu
    have : π ∣ π ^ (k - d) * s := dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) s
    simpa using dvd_sub h this
  set Z : Matrix (Fin r) (Fin r) R := Matrix.of fun i j => if h : i ≤ j then c ⟨(i, j), h⟩ else 0 with hZ
  set W : Matrix (Fin n) (Fin r) R := X * (G.adjugate * ((↑hu'.unit⁻¹ : R) • Z)) with hW
  have hXW : Xᵀ * Q.hessian * W = π ^ d • Z := by
    rw [hW, ← Matrix.mul_assoc, ← hG, ← Matrix.mul_assoc, Matrix.mul_adjugate, hGdet, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, mul_assoc, IsUnit.mul_val_inv, mul_one]
  refine ⟨fun li => W li.1 li.2, ?_⟩
  have hWt : toMat (fun li : Fin n × Fin r => W li.1 li.2) = W := rfl
  have hent : ∀ a b, bil Q (col X a) (col W b) = π ^ d * Z a b := by
    intro a b
    have := congrFun (congrFun hXW a) b
    rw [transpose_mul_mul_apply₂] at this
    unfold bil col
    rw [this, Matrix.smul_apply, smul_eq_mul]
  funext p
  simp only [formD, LinearMap.coe_mk, AddHom.coe_mk, hWt, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [← hX, hent, hZ, Matrix.of_apply, dif_pos (h ▸ le_rfl : p.1.1 ≤ p.1.1)]
    congr 2
    apply Subtype.ext
    ext <;> simp [h]
  · rw [← hX, hent, bil_comm, hent, hZ, Matrix.of_apply, Matrix.of_apply, dif_pos p.2,
      dif_neg (fun h' => h (le_antisymm p.2 h')), mul_zero, add_zero]

/-! ### Counts in coordinates -/

/-- **$A_{\pi^N}(Q, T)$ in coordinates:** the number of $\vec x \in (R/\pi^N)^{n \times r}$ with
$\pi^N \mid (Q \circ X)_{ij} - T_{ij}$ for all $i \le j$ (lifts to $R$). -/
theorem repCountForm_eq_card_sol (Q : QuadForm R n) (T : QuadForm R r) (π : R) (N : ℕ) :
    repCountForm Q T π N = Nat.card {x : Fin n × Fin r → R ⧸ Ideal.span {π ^ N} //
      ∀ p, π ^ N ∣ formF Q (liftI π N x) p - T.coeff p.1.1 p.1.2} := by
  unfold repCountForm
  let e : Matrix (Fin n) (Fin r) (R ⧸ Ideal.span {π ^ N}) ≃ (Fin n × Fin r → R ⧸ Ideal.span {π ^ N}) :=
    (Equiv.curry _ _ _).symm
  refine Nat.card_congr (Equiv.subtypeEquiv e fun X => ?_)
  have hX : X = (toMat (liftI π N (e X))).map (Ideal.Quotient.mk _) := by
    ext l i
    show X l i = Ideal.Quotient.mk _ (liftI π N (e X) (l, i))
    exact (congrFun (redI_liftI π N (e X)) (l, i)).symm
  conv_lhs => rw [hX, map_compMat]
  constructor
  · intro h p
    have := congrArg (fun S : QuadForm _ r => S.coeff p.1.1 p.1.2) h
    simp only [QuadForm.map, Matrix.map_apply] at this
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
    exact this
  · intro h
    apply ext_upper
    intro i j hij
    simp only [QuadForm.map, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h ⟨(i, j), hij⟩

/-! ### Stabilization -/

section Stab

variable [Finite (IsLocalRing.ResidueField R)]

/-- **Stabilization of $A_{\pi^k}(Q, T)$** (Siegel 1935, Hilfssatz 13; Kitaoka 1993, §5.6 [unverified]): if
$\pi^d \,\|\, \det H_T$ and $k \ge 2d + 1$, then $A_{\pi^{k+1}}(Q, T)\, q^{r(r+1)/2} = q^{nr} A_{\pi^k}(Q, T)$. Any
$Q$, any $r$, every residue characteristic. -/
@[kb "siegel1935" "Hilfssatz 13 [unverified]"]
theorem repCountForm_succ (Q : QuadForm R n) (T : QuadForm R r) (π : R) (hπ : Irreducible π) (d k : ℕ)
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det) (hk : 2 * d + 1 ≤ k) :
    repCountForm Q T π (k + 1) * q R ^ (r * (r + 1) / 2) = q R ^ (n * r) * repCountForm Q T π k := by
  rw [repCountForm_eq_card_sol, repCountForm_eq_card_sol, ← card_upperIdx r,
    show n * r = Fintype.card (Fin n × Fin r) by simp]
  exact card_sol_succ π hπ (formF Q) (formD Q) (formF_add_smul Q) (fun p => T.coeff p.1.1 p.1.2) d k hk
    fun x hx c => formD_surj Q T π hπ d k hd hd' (by omega) x hx c

/-- $r(r+1)/2 \le nr$ when $r \le n$. -/
theorem upper_le_mul (hrn : r ≤ n) : r * (r + 1) / 2 ≤ n * r := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp
  · apply Nat.div_le_of_le_mul
    nlinarith

/-- **Stabilization, normalized** ($r \le n$): $A_{\pi^{k+1}}(Q, T) = q^{nr - r(r+1)/2} A_{\pi^k}(Q, T)$ for
$k \ge 2d + 1$, $\pi^d \,\|\, \det H_T$. -/
theorem repCountForm_succ' (Q : QuadForm R n) (T : QuadForm R r) (π : R) (hπ : Irreducible π) (d k : ℕ)
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det) (hk : 2 * d + 1 ≤ k)
    (hrn : r ≤ n) :
    repCountForm Q T π (k + 1) = q R ^ (n * r - r * (r + 1) / 2) * repCountForm Q T π k := by
  have h := repCountForm_succ Q T π hπ d k hd hd' hk
  have hq : 0 < q R ^ (r * (r + 1) / 2) := pow_pos (q_pos (R := R)) _
  rw [← Nat.sub_add_cancel (upper_le_mul hrn), pow_add, mul_comm (q R ^ _) (q R ^ (r * (r + 1) / 2)),
    mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h]; ring)

/-- **The normalized counts are constant from $k = 2d + 1$ on** ($r \le n$, $\pi^d \,\|\, \det H_T$). -/
theorem repCountForm_normalized_eq (Q : QuadForm R n) (T : QuadForm R r) (π : R) (hπ : Irreducible π)
    (d : ℕ) (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det) (hrn : r ≤ n) (k : ℕ)
    (hk : 2 * d + 1 ≤ k) :
    (repCountForm Q T π k : ℝ) / (q R : ℝ) ^ (k * (n * r - r * (r + 1) / 2)) =
      (repCountForm Q T π (2 * d + 1) : ℝ) / (q R : ℝ) ^ ((2 * d + 1) * (n * r - r * (r + 1) / 2)) := by
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih, repCountForm_succ' Q T π hπ d k hd hd' hk hrn]
    push_cast
    rw [show (k + 1) * (n * r - r * (r + 1) / 2) =
      (n * r - r * (r + 1) / 2) + k * (n * r - r * (r + 1) / 2) by ring, pow_add]
    have : (q R : ℝ) ^ (n * r - r * (r + 1) / 2) ≠ 0 := pow_ne_zero _ hq0
    field_simp

/-- **The local density of $T$ by $Q$ exists and is attained** ($r \le n$, $\pi^d \,\|\, \det H_T$): for every
$k \ge 2d + 1$, $\beta_\pi(Q, T) = A_{\pi^k}(Q, T)/q^{k(nr - r(r+1)/2)}$ (Siegel 1935; Kitaoka 1993, §5.6
[unverified]). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_eq (Q : QuadForm R n) (T : QuadForm R r) (π : R) (hπ : Irreducible π) (d : ℕ)
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det) (hrn : r ≤ n) (k : ℕ)
    (hk : 2 * d + 1 ≤ k) :
    localDensityForm Q T π = (repCountForm Q T π k : ℝ) / (q R : ℝ) ^ (k * (n * r - r * (r + 1) / 2)) := by
  have hT : Filter.Tendsto (fun k : ℕ =>
      (repCountForm Q T π k : ℝ) / (q R : ℝ) ^ (k * (n * r - r * (r + 1) / 2))) Filter.atTop
      (nhds ((repCountForm Q T π (2 * d + 1) : ℝ) /
        (q R : ℝ) ^ ((2 * d + 1) * (n * r - r * (r + 1) / 2)))) := by
    apply tendsto_const_nhds.congr'
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨2 * d + 1, fun k hk => (repCountForm_normalized_eq Q T π hπ d hd hd' hrn k hk).symm⟩
  unfold localDensityForm
  rw [hT.limUnder_eq, repCountForm_normalized_eq Q T π hπ d hd hd' hrn k hk]

/-- **Existence of $\beta_\pi(Q, T)$ for nondegenerate $T$** ($r \le n$; Siegel 1935; Kitaoka 1993, §5.6
[unverified]): the normalized counts are eventually equal to `localDensityForm Q T π`. Every residue
characteristic. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_eventually_eq (Q : QuadForm R n) (T : QuadForm R r) (hT : T.Nondegenerate)
    (π : R) (hπ : Irreducible π) (hrn : r ≤ n) :
    ∀ᶠ k in Filter.atTop,
      (repCountForm Q T π k : ℝ) / (q R : ℝ) ^ (k * (n * r - r * (r + 1) / 2)) = localDensityForm Q T π := by
  obtain ⟨d, hd, hd'⟩ := exists_pow_dvd_not_dvd π hπ hT
  rw [Filter.eventually_atTop]
  exact ⟨2 * d + 1, fun k hk => (localDensityForm_eq Q T π hπ d hd hd' hrn k hk).symm⟩

/-- **$H_T$ invertible mod $\pi$:** $\beta_\pi(Q, T) = A_\pi(Q, T)/q^{nr - r(r+1)/2}$, a count of $X$ over the residue
field $R/\pi$ ($r \le n$). At a non-dyadic prime this is "$T$ unimodular"; at a dyadic prime it means $T$ even
unimodular (e.g. a hyperbolic plane). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_eq_of_isUnit (Q : QuadForm R n) (T : QuadForm R r) (π : R) (hπ : Irreducible π)
    (hT : IsUnit T.hessian.det) (hrn : r ≤ n) :
    localDensityForm Q T π = (repCountForm Q T π 1 : ℝ) / (q R : ℝ) ^ (n * r - r * (r + 1) / 2) := by
  rw [localDensityForm_eq Q T π hπ 0 (by simp) (by simpa using dvr_not_dvd_of_isUnit hπ hT) hrn 1 le_rfl,
    one_mul]

end Stab

end QuadFormsKB.LocalDensity.DVR
