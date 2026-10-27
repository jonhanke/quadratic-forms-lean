/-
# Cassels, Chapter 12, §7: the geometry of the general case

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, §7, pp. 277–279.

The images $T\mathcal R = \{Tf : f \in \mathcal R\}$ of the set $\mathcal R$ of reduced forms under the substitutions
$T \in \mathrm{GL}_n(\mathbb{Z})$ ($(Tf)(\vec{x}) = f(T\vec{x})$, matrix $T^{\mathsf T}FT$, `act`; here `img T`) cover the cone
$\mathcal P^\circ$ of strictly positive definite forms (Theorem 7.1), overlap only on their boundaries (Theorem 7.4),
only finitely many meet a given one (Theorem 7.5) or a given compact set (Theorem 7.6), and those meeting $\mathcal R$
generate $\mathrm{GL}_n(\mathbb{Z})$ (Theorem 7.7).

**Order of composition.** Cassels writes $T_1 = T_2S$ in Theorem 7.5; with $(Tf)(\vec{x}) = f(T\vec{x})$ one has
$T(Sf) = (ST)f$ (`act_mul`), so the same statement reads $T_1 = ST_2$ here. Since $\Sigma$ is closed under inverses
the two formulations describe the same finite set.

**Not formalized:** the Corollary to Theorem 7.7 (generation by the *neighbours*, whose intersection with $\mathcal R$
has codimension $1$, and the sign changes), whose proof needs a general-position argument for a segment avoiding a
finite union of sets of codimension $\ge 2$.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec5

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **The set $T\mathcal R$** (Cassels, Ch. 12, §1, p. 257, and §7): the forms $f(T\vec{x})$, i.e. the matrices
$T^{\mathsf T}GT$, with $G$ Minkowski-reduced. -/
@[kb "cassels1978" "Ch. 12, §1, p. 257, and §7, p. 277 (the sets T𝓡)"]
def img (T : GL (Fin n) ℤ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  act T.val '' {G | IsMinkowskiReduced G}

/-- **Interior relative to the symmetric matrices** (Cassels' "interior point" in $\mathbb{R}^{n(n+1)/2}$, Thm. 7.4,
p. 277): $F$ is symmetric and some open set $U \ni F$ of $M_n(\mathbb{R})$ has all its symmetric members in $S$. -/
def symInterior (S : Set (Matrix (Fin n) (Fin n) ℝ)) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {F | F.IsSymm ∧ ∃ U, IsOpen U ∧ F ∈ U ∧ U ∩ {G | G.IsSymm} ⊆ S}

/-- Helper: $T^{-1}$ undoes the substitution $T$. -/
theorem act_inv_act7 (T : GL (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) :
    act T⁻¹.val (act T.val F) = F := by
  have h : T.val * T⁻¹.val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← act_mul, h, act_one]

/-- Helper: $T$ undoes the substitution $T^{-1}$. -/
theorem act_act_inv7 (T : GL (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) :
    act T.val (act T⁻¹.val F) = F := by
  have h : T⁻¹.val * T.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← act_mul, h, act_one]

/-- Helper: a sign-diagonal matrix squares to the identity. -/
theorem IsSignDiagonal.val_mul_self7 {T : GL (Fin n) ℤ} (h : IsSignDiagonal T) : T.val * T.val = 1 := by
  obtain ⟨d, hd, hT⟩ := h
  rw [hT, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases hd i with h | h <;> simp [h]

/-- Helper: the inverse of a sign-diagonal matrix is itself. -/
theorem IsSignDiagonal.inv_val7 {T : GL (Fin n) ℤ} (h : IsSignDiagonal T) : T⁻¹.val = T.val := by
  have h1 := h.val_mul_self7
  calc T⁻¹.val = T⁻¹.val * (T.val * T.val) := by rw [h1, Matrix.mul_one]
    _ = (T⁻¹.val * T.val) * T.val := by rw [Matrix.mul_assoc]
    _ = T.val := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-- Helper: the inverse of a sign-diagonal matrix is sign-diagonal. -/
theorem IsSignDiagonal.inv7 {T : GL (Fin n) ℤ} (h : IsSignDiagonal T) : IsSignDiagonal T⁻¹ := by
  obtain ⟨d, hd, hT⟩ := h
  exact ⟨d, hd, by rw [IsSignDiagonal.inv_val7 ⟨d, hd, hT⟩, hT]⟩

/-- Helper: sign changes of the coordinates preserve the tail gcd being $1$. -/
theorem tailGcd_signs7 {j : Fin n} {d : Fin n → ℤ} (hd : ∀ i, d i = 1 ∨ d i = -1) {e : Fin n → ℤ}
    (he : tailGcd j e = 1) : tailGcd j (diagonal d *ᵥ e) = 1 := by
  have hnn : 0 ≤ tailGcd j (diagonal d *ᵥ e) := Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  have hdvd : tailGcd j (diagonal d *ᵥ e) ∣ tailGcd j e := by
    apply Finset.dvd_gcd
    intro k hk
    have h1 : tailGcd j (diagonal d *ᵥ e) ∣ (diagonal d *ᵥ e) k := Finset.gcd_dvd hk
    have h2 : e k = d k * (diagonal d *ᵥ e) k := by
      rw [Matrix.mulVec_diagonal]
      rcases hd k with h | h <;> rw [h] <;> ring
    rw [h2]
    exact dvd_mul_of_dvd_right h1 _
  rw [he] at hdvd
  exact Int.eq_one_of_dvd_one hnn hdvd

/-- Helper: sign-diagonal substitutions preserve reduced forms (so $D\mathcal R = \mathcal R$ for sign-diagonal $D$,
by applying this also to $D^{-1}$). -/
theorem IsSignDiagonal.act_reduced7 {D : GL (Fin n) ℤ} (hD : IsSignDiagonal D) {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : IsMinkowskiReduced G) : IsMinkowskiReduced (act D.val G) := by
  obtain ⟨d, hd, hDd⟩ := hD
  refine ⟨PosDef.act hG.1 D, fun j e he => ?_⟩
  rw [extendsBasis_iff_gcd] at he
  have hext : ExtendsBasis j (D.val *ᵥ e) := by
    rw [extendsBasis_iff_gcd, hDd]; exact tailGcd_signs7 hd he
  have hj : D.val *ᵥ (Pi.single j 1 : Fin n → ℤ) = d j • (Pi.single j 1 : Fin n → ℤ) := by
    rw [hDd]; funext k
    by_cases h : k = j <;> simp [Matrix.mulVec_diagonal, Pi.single_apply, h]
  rw [act_diag, val_act, castM_mulVec_cast, hj]
  have hc : cast (d j • (Pi.single j 1 : Fin n → ℤ)) = (d j : ℝ) • (Pi.single j 1 : Fin n → ℝ) := by
    funext k
    by_cases h : k = j <;> simp [cast, Pi.single_apply, h]
  have := hG.2 j _ hext
  rw [hc, val_smul, val_single]
  have hsq : ((d j : ℝ)) ^ 2 = 1 := by rcases hd j with h | h <;> rw [h] <;> norm_num
  rw [hsq, one_mul]
  exact this

/-- Helper: `act` by a fixed integral matrix is continuous. -/
theorem continuous_act7 (U : Matrix (Fin n) (Fin n) ℤ) : Continuous (act U) := by
  unfold act
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/-- Helper: `act` preserves symmetry. -/
theorem isSymm_act7 (U : Matrix (Fin n) (Fin n) ℤ) {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) :
    (act U F).IsSymm := by
  have hs : Fᵀ = F := hF
  show (act U F)ᵀ = act U F
  unfold act
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hs, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Helper: a unimodular substitution preserves and reflects symmetry. -/
theorem isSymm_act_iff7 (T : GL (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) :
    (act T.val F).IsSymm ↔ F.IsSymm :=
  ⟨fun h => by have := isSymm_act7 T⁻¹.val h; rwa [act_inv_act7] at this, isSymm_act7 _⟩

/-- Helper: a unimodular substitution preserves and reflects strict positive definiteness. -/
theorem posDef_act_iff7 (T : GL (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) :
    (act T.val F).PosDef ↔ F.PosDef :=
  ⟨fun h => by have := PosDef.act h T⁻¹; rwa [act_inv_act7] at this, fun h => PosDef.act h T⟩

/-- Helper: the symmetric matrices form a closed set. -/
theorem isClosed_isSymm7 : IsClosed {F : Matrix (Fin n) (Fin n) ℝ | F.IsSymm} := by
  have : {F : Matrix (Fin n) (Fin n) ℝ | F.IsSymm} = {F | Fᵀ = F} := rfl
  rw [this]
  exact isClosed_eq (continuous_id.matrix_transpose) continuous_id

/-- Helper: $F \in T\mathcal R$ iff $T^{-1}F$ is reduced. -/
theorem mem_img_iff_red7 (T : GL (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) :
    F ∈ img T ↔ IsMinkowskiReduced (act T⁻¹.val F) := by
  constructor
  · rintro ⟨G, hG, rfl⟩
    rw [act_inv_act7]; exact hG
  · intro h
    exact ⟨_, h, act_act_inv7 T F⟩

/-- Helper: the closed set $\{F : T^{-1}F \in \overline{\mathcal R^\circ}\}$, of which $T\mathcal R$ is the part in
$\mathcal P^\circ$ (`mem_img_iff7`). -/
def clR7 (T : GL (Fin n) ℤ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  (act T⁻¹.val) ⁻¹' closure {F | IsStrictlyReduced F}

/-- Helper: `clR7 T` is closed. -/
theorem isClosed_clR7 (T : GL (Fin n) ℤ) : IsClosed (clR7 T) :=
  isClosed_closure.preimage (continuous_act7 _)

/-- Helper: $T\mathcal R$ is the intersection of `clR7 T` with $\mathcal P^\circ$ (Lemma 5.3 (ii)). -/
theorem mem_img_iff7 (T : GL (Fin n) ℤ) (F : Matrix (Fin n) (Fin n) ℝ) :
    F ∈ img T ↔ F ∈ clR7 T ∧ F.PosDef := by
  have e := lemma_5_3_closure (n := n)
  rw [mem_img_iff_red7]
  constructor
  · intro h
    have h' : act T⁻¹.val F ∈ {F | IsMinkowskiReduced F} := h
    rw [e] at h'
    exact ⟨h'.1, (posDef_act_iff7 T⁻¹ F).1 h.1⟩
  · rintro ⟨h1, h2⟩
    have h' : act T⁻¹.val F ∈ closure {F | IsStrictlyReduced F} ∩ {F | F.PosDef} :=
      ⟨h1, PosDef.act h2 T⁻¹⟩
    rw [← e] at h'
    exact h'

/-- Helper: if $T_1 = ST_2$ with $S$ sign-diagonal then $T_1\mathcal R = T_2\mathcal R$. -/
theorem img_eq_of_signDiag7 {S T₁ T₂ : GL (Fin n) ℤ} (hS : IsSignDiagonal S) (h : T₁ = S * T₂) :
    img T₁ = img T₂ := by
  ext F
  constructor
  · rintro ⟨H, hH, rfl⟩
    refine ⟨act S.val H, hS.act_reduced7 hH, ?_⟩
    rw [h, Units.val_mul, act_mul]
  · rintro ⟨H, hH, rfl⟩
    refine ⟨act S⁻¹.val H, hS.inv7.act_reduced7 hH, ?_⟩
    rw [h, Units.val_mul, act_mul, act_act_inv7]

/-- **Theorem 7.1** (Cassels, Ch. 12, §7, p. 277): $\mathcal P^\circ = \bigcup_T T\mathcal R$, the union over all integral
unimodular $T$. -/
@[kb "cassels1978" "Ch. 12, §7, Thm. 7.1, p. 277"]
theorem thm_7_1 : {F : Matrix (Fin n) (Fin n) ℝ | F.PosDef} = ⋃ T : GL (Fin n) ℤ, img T := by
  ext F
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hF
    obtain ⟨T, hT⟩ := exists_isMinkowskiReduced hF
    exact ⟨T⁻¹, act T.val F, hT, act_inv_act7 T F⟩
  · rintro ⟨T, G, hG, rfl⟩
    exact PosDef.act hG.1 T

/-- **Theorem 7.2** (Cassels, Ch. 12, §7, p. 277): if $T\mathcal R = \mathcal R$ then $T$ is diagonal with entries $\pm1$
((7.1): $T(x_0, \dots, x_{n-1}) = (\pm x_0, \dots, \pm x_{n-1})$). -/
@[kb "cassels1978" "Ch. 12, §7, Thm. 7.2, p. 277"]
theorem thm_7_2 {T : GL (Fin n) ℤ} (hT : img T = {G | IsMinkowskiReduced G}) : IsSignDiagonal T := by
  obtain ⟨F₀, hF₀⟩ := exists_isStrictlyReduced n
  have hmem : F₀ ∈ img T := by rw [hT]; exact hF₀.1
  obtain ⟨G, hG, rfl⟩ := hmem
  have h := hF₀.2 T⁻¹ (by rw [act_inv_act7]; exact hG)
  simpa using h.inv7

/-- Helper: the linear functional $G \mapsto g(\vec{x}) - g_{jj}$ on matrices. -/
def ineqL7 (j : Fin n) (x : Fin n → ℝ) : Module.Dual ℝ (Matrix (Fin n) (Fin n) ℝ) where
  toFun G := val G x - G j j
  map_add' G H := by simp [val, Matrix.add_mulVec, dotProduct_add]; ring
  map_smul' c G := by simp [val, Matrix.smul_mulVec, dotProduct_smul]; ring

/-- Helper: the linear map $F \mapsto T^{\mathsf T}FT$ on matrices. -/
def actL7 (U : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := act U
  map_add' F G := by simp [act, Matrix.mul_add, Matrix.add_mul]
  map_smul' c F := by simp [act, Matrix.mul_smul, Matrix.smul_mul]

/-- Helper: the linear functional $G \mapsto g_{00}$ on matrices. -/
def entryL7 (i j : Fin n) : Module.Dual ℝ (Matrix (Fin n) (Fin n) ℝ) where
  toFun G := G i j
  map_add' G H := by simp
  map_smul' c G := by simp

/-- Helper: finitely many linear conditions indexed by a finite set can be indexed by `Fin k`. -/
theorem exists_dual_family7 {α M : Type*} [AddCommGroup M] [Module ℝ M] (P : Set α) (hP : P.Finite)
    (ℓ : α → Module.Dual ℝ M) :
    ∃ (k : ℕ) (L : Fin k → Module.Dual ℝ M), ∀ F : M, (∀ m, 0 ≤ L m F) ↔ ∀ a ∈ P, 0 ≤ ℓ a F := by
  haveI := hP.to_subtype
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin P
  refine ⟨k, fun m => ℓ (e.symm m).1, fun F => ⟨fun h a ha => ?_, fun h m => h _ (e.symm m).2⟩⟩
  simpa using h (e ⟨a, ha⟩)

/-- Helper: the finite set of conditions $(j, \vec{e}^{\,*})$, $\vec{e}^{\,*} \in W_j$, of Theorem 5.2. -/
theorem finite_WPairs7 (n : ℕ) : {p : Fin n × (Fin n → ℤ) | p.2 ∈ W p.1}.Finite := by
  have : {p : Fin n × (Fin n → ℤ) | p.2 ∈ W p.1} ⊆ ⋃ j : Fin n, (Prod.mk j) '' W j := by
    rintro ⟨j, e⟩ h
    exact Set.mem_iUnion.2 ⟨j, e, h, rfl⟩
  exact (Set.finite_iUnion fun j => (W_finite j).image _).subset this

/-- Helper: reduced forms among symmetric matrices, by Theorem 5.2 Corollary (finite condition set). -/
theorem red_iff_posDef7 {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} :
    IsMinkowskiReduced G ↔ G.PosDef ∧ ∀ p ∈ {p : Fin (n + 1) × (Fin (n + 1) → ℤ) | p.2 ∈ W p.1},
      0 ≤ ineqL7 p.1 (cast p.2) G := by
  constructor
  · intro h
    have hs := ((posDef_iff G).1 h.1).1
    refine ⟨h.1, fun p hp => ?_⟩
    have := ((thm_5_2_cor hs).1 h).2 p.1 p.2 hp
    show 0 ≤ val G (cast p.2) - G p.1 p.1
    linarith
  · rintro ⟨h1, h2⟩
    have hs := ((posDef_iff G).1 h1).1
    have h00 : 0 < G 0 0 := by
      have := ((posDef_iff G).1 h1).2 (Pi.single 0 1) (by
        intro h0; have := congrFun h0 0; simp at this)
      rwa [val_single] at this
    refine (thm_5_2_cor hs).2 ⟨h00, fun j e he => ?_⟩
    have := h2 (j, e) he
    change 0 ≤ val G (cast e) - G j j at this
    linarith

/-- Helper: reduced forms among symmetric matrices, with the strict condition $g_{00} > 0$. -/
theorem red_iff_symm7 {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} :
    IsMinkowskiReduced G ↔ G.IsSymm ∧ 0 < entryL7 0 0 G ∧ ∀ p ∈ {p : Fin (n + 1) × (Fin (n + 1) → ℤ) | p.2 ∈ W p.1},
      0 ≤ ineqL7 p.1 (cast p.2) G := by
  constructor
  · intro h
    have hs := ((posDef_iff G).1 h.1).1
    have h00 : 0 < G 0 0 := by
      have := ((posDef_iff G).1 h.1).2 (Pi.single 0 1) (by
        intro h0; have := congrFun h0 0; simp at this)
      rwa [val_single] at this
    exact ⟨hs, h00, (red_iff_posDef7.1 h).2⟩
  · rintro ⟨hs, h00, h2⟩
    refine (thm_5_2_cor hs).2 ⟨h00, fun j e he => ?_⟩
    have := h2 (j, e) he
    change 0 ≤ val G (cast e) - G j j at this
    linarith

/-- **Theorem 7.3** (Cassels, Ch. 12, §7, p. 277): for every integral unimodular $T$ the set $T\mathcal R$ is cut out of
$\mathcal P^\circ$ by finitely many homogeneous linear conditions $L^{(m)}(f) \ge 0$ in the coefficients $f_{ij}$
((7.2)–(7.3)); alternatively, among all symmetric $F$, by these and one further strict condition $L^{(0)}(f) > 0$
((7.4)). Stated for $n \ge 1$ variables; the linear forms are on $M_n(\mathbb{R})$ and only their values on symmetric
matrices matter. -/
@[kb "cassels1978" "Ch. 12, §7, Thm. 7.3, (7.2)–(7.4), p. 277"]
theorem thm_7_3 (T : GL (Fin (n + 1)) ℤ) :
    ∃ (k : ℕ) (L : Fin k → Module.Dual ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
      (L₀ : Module.Dual ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)),
      img T = {F | F.PosDef ∧ ∀ m, 0 ≤ L m F} ∧ img T = {F | F.IsSymm ∧ 0 < L₀ F ∧ ∀ m, 0 ≤ L m F} := by
  obtain ⟨k, L, hL⟩ := exists_dual_family7 _ (finite_WPairs7 (n + 1))
    (fun p => (ineqL7 p.1 (cast p.2)).comp (actL7 T⁻¹.val))
  refine ⟨k, L, (entryL7 0 0).comp (actL7 T⁻¹.val), ?_, ?_⟩
  · ext F
    rw [mem_img_iff_red7, red_iff_posDef7, Set.mem_setOf_eq, hL F, posDef_act_iff7]
    rfl
  · ext F
    rw [mem_img_iff_red7, red_iff_symm7, Set.mem_setOf_eq, hL F, isSymm_act_iff7]
    rfl

/-- Helper: $(G - tP)(\vec{x}) = G(\vec{x}) - tP(\vec{x})$. -/
theorem val_sub_smul7 (G P : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    val (G - t • P) x = val G x - t * val P x := by
  simp [val, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]

/-- Helper: a weight vector $w$ with $\sum_i w_i x_i^2 > w_j$, for an integral $\vec{e}\ne\pm e_j$. -/
theorem exists_weight7 {j : Fin n} {e : Fin n → ℤ} (h1 : e ≠ Pi.single j 1) (h2 : e ≠ -Pi.single j 1) :
    ∃ w : Fin n → ℝ, w j < ∑ i, w i * (cast e i) ^ 2 := by
  by_cases h : ∃ k, k ≠ j ∧ e k ≠ 0
  · obtain ⟨k, hkj, hk⟩ := h
    refine ⟨Pi.single k 1, ?_⟩
    have hk' : (0 : ℝ) < (e k : ℝ) ^ 2 := by
      have : (e k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    simp [Pi.single_apply, hkj.symm, cast]
    exact hk'
  · push_neg at h
    set c : ℤ := e j with hc
    have hc2 : c ^ 2 ≠ 1 := by
      intro hc2
      have : c = 1 ∨ c = -1 := by
        have : (c - 1) * (c + 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · left; omega
        · right; omega
      rcases this with h' | h'
      · apply h1; funext k
        by_cases hk : k = j
        · subst hk; simp [h', hc] at *; omega
        · simp [Pi.single_apply, hk, h k hk]
      · apply h2; funext k
        by_cases hk : k = j
        · subst hk; simp [Pi.single_apply]; omega
        · simp [Pi.single_apply, hk, h k hk]
    have hc2' : ((c : ℝ) ^ 2 - 1) ≠ 0 := by
      intro h0
      apply hc2
      have : ((c ^ 2 : ℤ) : ℝ) = 1 := by push_cast; linarith
      exact_mod_cast this
    refine ⟨((c : ℝ) ^ 2 - 1) • Pi.single j 1, ?_⟩
    simp [Pi.single_apply, cast, hc]
    nlinarith [sq_pos_of_ne_zero hc2']

/-- Helper: a form in the symmetric interior of $\mathcal R$ is strictly reduced (the perturbation argument of
Theorem 7.4: Cassels, p. 277, "if $f$ is interior then ... (5.4)"). -/
theorem isStrictlyReduced_of_interior7 {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G ∈ symInterior {G | IsMinkowskiReduced G}) : IsStrictlyReduced G := by
  obtain ⟨hs, U, hU, hGU, hUR⟩ := hG
  have hGR : IsMinkowskiReduced G := hUR ⟨hGU, hs⟩
  rw [isStrictlyReduced_iff]
  refine ⟨hGR.1, fun j e he hne1 hne2 => ?_⟩
  refine lt_of_le_of_ne (hGR.2 j e he) ?_
  intro heq
  obtain ⟨w, hw⟩ := exists_weight7 hne1 hne2
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), G - t • diagonal w ∈ U := by
    have : Filter.Tendsto (fun t : ℝ => G - t • diagonal w) (nhds 0) (nhds G) := by
      have hc : Continuous (fun t : ℝ => G - t • diagonal w) :=
        continuous_const.sub (continuous_id.smul continuous_const)
      simpa using hc.tendsto 0
    exact (this.mono_left nhdsWithin_le_nhds).eventually (hU.mem_nhds hGU)
  obtain ⟨t, htU, ht⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht0 : (0 : ℝ) < t := ht
  have hsym : (G - t • diagonal w).IsSymm :=
    hs.sub ((Matrix.isSymm_diagonal w).smul t)
  have hR := hUR ⟨htU, hsym⟩
  have h := hR.2 j e he
  rw [val_sub_smul7, val_diagonal] at h
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul] at h
  nlinarith

/-- **Theorem 7.4** (Cassels, Ch. 12, §7, p. 277): if $T_1\mathcal R$ and $T_2\mathcal R$ have a form in common which is an
interior point of one of them, then $T_1\mathcal R = T_2\mathcal R$. -/
@[kb "cassels1978" "Ch. 12, §7, Thm. 7.4, p. 277"]
theorem thm_7_4 {T₁ T₂ : GL (Fin n) ℤ} {F : Matrix (Fin n) (Fin n) ℝ} (h₁ : F ∈ symInterior (img T₁))
    (h₂ : F ∈ img T₂) : img T₁ = img T₂ := by
  obtain ⟨hs, U, hU, hFU, hUS⟩ := h₁
  have hGint : act T₁⁻¹.val F ∈ symInterior {G | IsMinkowskiReduced G} := by
    refine ⟨isSymm_act7 _ hs, (act T₁.val) ⁻¹' U, hU.preimage (continuous_act7 _), ?_, ?_⟩
    · show act T₁.val (act T₁⁻¹.val F) ∈ U
      rw [act_act_inv7]; exact hFU
    · rintro H ⟨hHU, hHs⟩
      have h3 : act T₁.val H ∈ img T₁ := hUS ⟨hHU, isSymm_act7 _ hHs⟩
      rw [mem_img_iff_red7, act_inv_act7] at h3
      exact h3
  have hstr := isStrictlyReduced_of_interior7 hGint
  rw [mem_img_iff_red7] at h₂
  have hD := hstr.2 (T₁ * T₂⁻¹) (by
    rw [Units.val_mul, act_mul]
    show IsMinkowskiReduced (act T₂⁻¹.val (act T₁.val (act T₁⁻¹.val F)))
    rw [act_act_inv7]; exact h₂)
  exact img_eq_of_signDiag7 hD (by simp [mul_assoc])

/-- **The finite set $\Sigma$** (Cassels, Ch. 12, proof of Thm. 7.5, p. 278, and Thm. 7.7, p. 278): the integral unimodular
$S$ such that $\mathcal R \cap S\mathcal R$ is nonempty. Finite by Theorem 1.2 (`sigma_finite`). -/
@[kb "cassels1978" "Ch. 12, §7, Thm. 7.5 proof and Thm. 7.7, p. 278 (the set Σ)"]
def sigma (n : ℕ) : Set (GL (Fin n) ℤ) := {S | ({G | IsMinkowskiReduced G} ∩ img S).Nonempty}

@[kb "cassels1978" "Ch. 12, §7, proof of Thm. 7.5, p. 278 (Σ is finite)"]
theorem sigma_finite (n : ℕ) : (sigma n).Finite := by
  refine (finite_gl_reduced_pair n).subset ?_
  rintro S ⟨G, hG, G', hG', rfl⟩
  exact ⟨G', hG', hG⟩

/-- **Theorem 7.5** (Cassels, Ch. 12, §7, pp. 277–278): $T_1\mathcal R \cap T_2\mathcal R$ is nonempty iff $T_1 = ST_2$ for some
$S$ in the finite set $\Sigma$ (`sigma`, `sigma_finite`). *Update* (clarification): Cassels writes $T_1 = T_2S$, which matches the left action
$f \mapsto f(T^{-1}\vec{x})$, not his $(Tf)(\vec{x}) = f(T\vec{x})$; see the module docstring. -/
@[kb "cassels1978" "Ch. 12, §7, Thm. 7.5, pp. 277–278"]
theorem thm_7_5 (T₁ T₂ : GL (Fin n) ℤ) : (img T₁ ∩ img T₂).Nonempty ↔ ∃ S ∈ sigma n, T₁ = S * T₂ := by
  constructor
  · rintro ⟨F, ⟨G₁, hG₁, h₁⟩, ⟨G₂, hG₂, h₂⟩⟩
    refine ⟨T₁ * T₂⁻¹, ⟨G₂, hG₂, G₁, hG₁, ?_⟩, by simp [mul_assoc]⟩
    rw [Units.val_mul, act_mul, h₁, ← h₂, act_inv_act7]
  · rintro ⟨S, ⟨G, hG, G', hG', hS⟩, rfl⟩
    refine ⟨act T₂.val G, ⟨G', hG', ?_⟩, ⟨G, hG, rfl⟩⟩
    rw [Units.val_mul, act_mul, hS]

/-- **Theorem 7.5, Corollary** (Cassels, Ch. 12, p. 278): every form belongs to at most $t$ of the sets $T\mathcal R$,
where $t$ is the number of elements of $\Sigma$. -/
@[kb "cassels1978" "Ch. 12, §7, Thm. 7.5, Corollary, p. 278"]
theorem thm_7_5_cor (F : Matrix (Fin n) (Fin n) ℝ) :
    {S : Set (Matrix (Fin n) (Fin n) ℝ) | ∃ T, S = img T ∧ F ∈ S}.Finite ∧
      {S : Set (Matrix (Fin n) (Fin n) ℝ) | ∃ T, S = img T ∧ F ∈ S}.ncard ≤ (sigma n).ncard := by
  by_cases hex : ∃ T₀, F ∈ img T₀
  · obtain ⟨T₀, hT₀⟩ := hex
    have hsub : {S : Set (Matrix (Fin n) (Fin n) ℝ) | ∃ T, S = img T ∧ F ∈ S} ⊆
        (fun S : GL (Fin n) ℤ => img (S * T₀)) '' sigma n := by
      rintro _ ⟨T, rfl, hF⟩
      obtain ⟨S, hS, hTS⟩ := (thm_7_5 T T₀).1 ⟨F, hF, hT₀⟩
      exact ⟨S, hS, by rw [hTS]⟩
    have hfin : ((fun S : GL (Fin n) ℤ => img (S * T₀)) '' sigma n).Finite :=
      (sigma_finite n).image _
    exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_image_le (sigma_finite n))⟩
  · have : {S : Set (Matrix (Fin n) (Fin n) ℝ) | ∃ T, S = img T ∧ F ∈ S} = ∅ := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨T, rfl, hF⟩
      exact hex ⟨T, hF⟩
    rw [this]
    simp

/-- Helper: the euclidean unit sphere is compact. -/
theorem isCompact_sphere7 : IsCompact {x : Fin n → ℝ | ∑ i, x i ^ 2 = 1} := by
  have hSc : IsClosed {x : Fin n → ℝ | ∑ i, x i ^ 2 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hSb : Bornology.IsBounded {x : Fin n → ℝ | ∑ i, x i ^ 2 = 1} := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : x i ^ 2 ≤ 1 := by
      have : x i ^ 2 ≤ ∑ i, x i ^ 2 :=
        Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
      have hx' : ∑ i, x i ^ 2 = 1 := hx
      linarith
    rw [Real.norm_eq_abs]
    exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  exact Metric.isCompact_of_isClosed_isBounded hSc hSb

/-- Helper: a lower bound on the unit sphere gives a lower bound everywhere. -/
theorem val_ge_of_sphere7 {F : Matrix (Fin n) (Fin n) ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (h : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → κ ≤ val F x) (x : Fin n → ℝ) :
    κ * ∑ i, x i ^ 2 ≤ val F x := by
  by_cases hz : ∑ i, x i ^ 2 = 0
  · have : x = 0 := by
      ext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1 hz i
        (Finset.mem_univ i)
      simpa using this
    subst this
    simp [val]
  · have hpos : 0 < ∑ i, x i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hz)
    set r := Real.sqrt (∑ i, x i ^ 2) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hpos
    have hr2 : r ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hpos.le
    have hy : ∑ i, (r⁻¹ • x) i ^ 2 = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      rw [← hr2]
      field_simp
    have h1 := h _ hy
    rw [val_smul] at h1
    have : κ * r ^ 2 ≤ val F x := by
      have := mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
      calc κ * r ^ 2 ≤ r ^ 2 * ((r⁻¹) ^ 2 * val F x) := by nlinarith
        _ = val F x := by field_simp
    rw [← hr2]; exact this

/-- Helper (uniform Lemma 5.2): on a compact set of strictly positive definite forms, $f(\vec{x}) \ge \kappa|\vec{x}|^2$
with one $\kappa > 0$. -/
theorem exists_unif_val_ge7 {K : Set (Matrix (Fin n) (Fin n) ℝ)} (hK : IsCompact K)
    (hKP : ∀ F ∈ K, F.PosDef) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F ∈ K, ∀ x : Fin n → ℝ, κ * ∑ i, x i ^ 2 ≤ val F x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun F _ x => by simp [val]⟩
  have hS : IsCompact {x : Fin n → ℝ | ∑ i, x i ^ 2 = 1} := isCompact_sphere7
  have hSne : ({x : Fin n → ℝ | ∑ i, x i ^ 2 = 1}).Nonempty := by
    refine ⟨Pi.single ⟨0, hn⟩ 1, ?_⟩
    simp [Pi.single_apply]
  have hcont : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) => val p.1 p.2) := by
    unfold val Matrix.mulVec dotProduct
    fun_prop
  obtain ⟨p, hp, hmin⟩ := (hK.prod hS).exists_isMinOn (hne.prod hSne) hcont.continuousOn
  have hp1 : p.1 ∈ K := hp.1
  have hp2 : ∑ i, p.2 i ^ 2 = 1 := hp.2
  have hp0 : p.2 ≠ 0 := by
    intro h0
    rw [h0] at hp2
    simp at hp2
  have hpos : 0 < val p.1 p.2 := ((posDef_iff _).1 (hKP _ hp1)).2 _ hp0
  refine ⟨val p.1 p.2, hpos, fun F hF x => val_ge_of_sphere7 hpos.le (fun y hy => ?_) x⟩
  exact hmin (show (F, y) ∈ K ×ˢ {x : Fin n → ℝ | ∑ i, x i ^ 2 = 1} from ⟨hF, hy⟩)

/-- Helper: $f(\vec{x})$ for $F = \kappa I$. -/
theorem val_smul_one7 (κ : ℝ) (x : Fin n → ℝ) : val (κ • (1 : Matrix (Fin n) (Fin n) ℝ)) x = κ * ∑ i, x i ^ 2 := by
  simp only [val, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, sq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **Theorem 7.6 (local finiteness)** (Cassels, Ch. 12, §7, p. 278): a compact subset $\mathcal C$ of $\mathcal P^\circ$
meets $T\mathcal R$ for only finitely many integral unimodular $T$. (Cassels' proof covers $\mathcal C$ by finitely many
interiors of Siegel domains; here the columns of $T^{-1}$ are bounded directly, by Theorem 3.1 (ii) and a uniform
Lemma 5.2 on $\mathcal C$.) -/
@[kb "cassels1978" "Ch. 12, §7, Thm. 7.6, p. 278"]
theorem thm_7_6 {K : Set (Matrix (Fin n) (Fin n) ℝ)} (hK : IsCompact K) (hKP : ∀ F ∈ K, F.PosDef) :
    {T : GL (Fin n) ℤ | (img T ∩ K).Nonempty}.Finite := by
  obtain ⟨κ, hκ, hκK⟩ := exists_unif_val_ge7 hK hKP
  have hcont : Continuous fun F : Matrix (Fin n) (Fin n) ℝ => ∑ k, F k k :=
    continuous_finset_sum _ fun k _ => (continuous_id.matrix_elem k k)
  obtain ⟨a, ha⟩ := hK.bddAbove_image hcont.continuousOn
  set B : ℝ := (9 / 4 : ℝ) ^ n * a with hB
  have hκ1 : (κ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
    rw [posDef_iff]
    refine ⟨(Matrix.isSymm_one).smul κ, fun x hx => ?_⟩
    rw [val_smul_one7]
    have hpos : 0 < ∑ i, x i ^ 2 := by
      by_contra h
      apply hx
      have h0 : ∑ i, x i ^ 2 = 0 :=
        le_antisymm (not_lt.1 h) (Finset.sum_nonneg fun i _ => sq_nonneg _)
      ext i
      simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1 h0 i (Finset.mem_univ i)
    positivity
  have hfin1 := finite_val_le hκ1 B
  have hU : {U : GL (Fin n) ℤ | ∃ F ∈ K, IsMinkowskiReduced (act U.val F)}.Finite := by
    let Φ : GL (Fin n) ℤ → (Fin n → Fin n → ℤ) := fun U j => U.val *ᵥ Pi.single j 1
    have hinj : Function.Injective Φ := by
      intro T T' h
      apply Units.ext
      ext a j
      have := congrFun (congrFun h j) a
      simpa [Φ, mulVec_single_apply] using this
    refine Set.Finite.of_finite_image (f := Φ) ?_ hinj.injOn
    refine (Set.Finite.pi (t := fun _ : Fin n => {m : Fin n → ℤ | val (κ • (1 : Matrix (Fin n) (Fin n) ℝ)) (cast m) ≤ B})
      (fun _ => hfin1)).subset ?_
    rintro _ ⟨U, ⟨F, hFK, hFU⟩, rfl⟩ j _
    show val (κ • (1 : Matrix (Fin n) (Fin n) ℝ)) (cast (U.val *ᵥ Pi.single j 1)) ≤ B
    rw [val_smul_one7]
    refine (hκK F hFK _).trans ?_
    refine (columns_bound (hKP F hFK) U hFU j).trans ?_
    exact mul_le_mul_of_nonneg_left (ha ⟨F, hFK, rfl⟩) (by positivity)
  refine (hU.image (fun U => U⁻¹)).subset ?_
  rintro T ⟨F, ⟨G, hG, rfl⟩, hFK⟩
  refine ⟨T⁻¹, ⟨act T.val G, hFK, ?_⟩, inv_inv T⟩
  rw [act_inv_act7]; exact hG

/-- **Theorem 7.6, Corollary** (Cassels, Ch. 12, p. 278): every $F_0 \in \mathcal P^\circ$ has a neighbourhood whose
symmetric members all lie in the union of the sets $T\mathcal R$ that contain $F_0$. -/
@[kb "cassels1978" "Ch. 12, §7, Thm. 7.6, Corollary, p. 278"]
theorem thm_7_6_cor {F₀ : Matrix (Fin n) (Fin n) ℝ} (hF₀ : F₀.PosDef) :
    ∃ U, IsOpen U ∧ F₀ ∈ U ∧ ∀ F ∈ U, F.IsSymm → ∃ T : GL (Fin n) ℤ, F₀ ∈ img T ∧ F ∈ img T := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  obtain ⟨U₀, hU₀, hP⟩ := thm_5_1_open (n := n)
  have hF₀U : F₀ ∈ U₀ := by
    have : F₀ ∈ U₀ ∩ {F | F.IsSymm} := by rw [← hP]; exact hF₀
    exact this.1
  have hPos : ∀ F, F ∈ U₀ → F.IsSymm → F.PosDef := by
    intro F h1 h2
    have : F ∈ U₀ ∩ {F | F.IsSymm} := ⟨h1, h2⟩
    rw [← hP] at this
    exact this
  obtain ⟨C, hC, hCint, hCU⟩ := exists_compact_subset hU₀ hF₀U
  have hKc : IsCompact (C ∩ {F | F.IsSymm}) := hC.inter_right isClosed_isSymm7
  have hKP : ∀ F ∈ C ∩ {F | F.IsSymm}, F.PosDef := fun F hF => hPos F (hCU hF.1) hF.2
  have hfin := thm_7_6 hKc hKP
  have hbad : {T : GL (Fin n) ℤ | (img T ∩ (C ∩ {F | F.IsSymm})).Nonempty ∧ F₀ ∉ img T}.Finite :=
    hfin.subset fun T hT => hT.1
  refine ⟨interior C ∩ ⋂ T ∈ {T : GL (Fin n) ℤ | (img T ∩ (C ∩ {F | F.IsSymm})).Nonempty ∧ F₀ ∉ img T},
    (clR7 T)ᶜ, isOpen_interior.inter (hbad.isOpen_biInter fun T _ => (isClosed_clR7 T).isOpen_compl),
    ⟨hCint, ?_⟩, ?_⟩
  · simp only [Set.mem_iInter]
    intro T hT hmem
    exact hT.2 ((mem_img_iff7 T F₀).2 ⟨hmem, hF₀⟩)
  · rintro F ⟨hFC, hFB⟩ hFs
    have hFK : F ∈ C ∩ {F | F.IsSymm} := ⟨interior_subset hFC, hFs⟩
    have hFpos : F.PosDef := hKP F hFK
    have hmem : F ∈ ⋃ T : GL (Fin n) ℤ, img T := by rw [← thm_7_1]; exact hFpos
    obtain ⟨T, hT⟩ := Set.mem_iUnion.1 hmem
    refine ⟨T, ?_, hT⟩
    by_contra hF₀T
    simp only [Set.mem_iInter] at hFB
    exact hFB T ⟨⟨F, hT, hFK⟩, hF₀T⟩ ((mem_img_iff7 T F).1 hT).1

/-- **Theorem 7.7** (Cassels, Ch. 12, §7, pp. 278–279): the set $\Sigma$ of integral unimodular $S$ with
$\mathcal R \cap S\mathcal R \ne \emptyset$ is finite (`sigma_finite`) and generates $\mathrm{GL}_n(\mathbb{Z})$: every integral
unimodular $T$ is a product of elements of $\Sigma$. *Proof* (Cassels'): the segment from a strictly reduced $f_1$ to
$Tf_1$ meets finitely many convex sets $T_k\mathcal R$ (Theorem 7.6), which link $\mathcal R$ to $T\mathcal R$ in a chain of
successive intersecting sets. -/
@[kb "cassels1978" "Ch. 12, §7, Thm. 7.7, pp. 278–279"]
theorem thm_7_7 (n : ℕ) : Subgroup.closure (sigma n) = ⊤ := by
  set H := Subgroup.closure (sigma n) with hH
  rw [eq_top_iff]
  intro T _
  obtain ⟨F₁, hF₁⟩ := exists_isStrictlyReduced n
  set F₂ := act T.val F₁ with hF₂def
  have hF₂ : F₂.PosDef := PosDef.act hF₁.1.1 T
  set γ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => (1 - t) • F₁ + t • F₂ with hγ
  have hγc : Continuous γ := by
    refine Continuous.add (Continuous.smul (continuous_const.sub continuous_id) continuous_const)
      (Continuous.smul continuous_id continuous_const)
  have hγP : ∀ t ∈ Set.Icc (0 : ℝ) 1, (γ t).PosDef := fun t ht =>
    thm_5_1_convex hF₁.1.1 hF₂ (sub_nonneg.2 ht.2) ht.1 (by ring)
  have hK : IsCompact (γ '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image hγc
  have hKP : ∀ F ∈ γ '' Set.Icc (0 : ℝ) 1, F.PosDef := by
    rintro _ ⟨t, ht, rfl⟩; exact hγP t ht
  have hfin := thm_7_6 hK hKP
  -- the sets E T' = {t ∈ [0,1] : γ t ∈ T'R}
  set E : GL (Fin n) ℤ → Set ℝ := fun T' => Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' clR7 T' with hE
  have hEmem : ∀ T' : GL (Fin n) ℤ, ∀ t ∈ Set.Icc (0 : ℝ) 1, (t ∈ E T' ↔ γ t ∈ img T') := by
    intro T' t ht
    rw [mem_img_iff7]
    constructor
    · rintro ⟨_, h⟩; exact ⟨h, hγP t ht⟩
    · rintro ⟨h, _⟩; exact ⟨ht, h⟩
  have hEclosed : ∀ T', IsClosed (E T') := fun T' =>
    isClosed_Icc.inter ((isClosed_clR7 T').preimage hγc)
  set A : Set ℝ := ⋃ T' ∈ {T' : GL (Fin n) ℤ | (img T' ∩ γ '' Set.Icc (0 : ℝ) 1).Nonempty ∧ T' ∈ H}, E T'
    with hA
  set B : Set ℝ := ⋃ T' ∈ {T' : GL (Fin n) ℤ | (img T' ∩ γ '' Set.Icc (0 : ℝ) 1).Nonempty ∧ T' ∉ H}, E T'
    with hB
  have hAc : IsClosed A :=
    (hfin.subset fun T' hT' => hT'.1).isClosed_biUnion fun T' _ => hEclosed T'
  have hBc : IsClosed B :=
    (hfin.subset fun T' hT' => hT'.1).isClosed_biUnion fun T' _ => hEclosed T'
  have hcover : Set.Icc (0 : ℝ) 1 ⊆ A ∪ B := by
    intro t ht
    have hmem : γ t ∈ ⋃ T' : GL (Fin n) ℤ, img T' := by rw [← thm_7_1]; exact hγP t ht
    obtain ⟨T', hT'⟩ := Set.mem_iUnion.1 hmem
    have hne : (img T' ∩ γ '' Set.Icc (0 : ℝ) 1).Nonempty := ⟨γ t, hT', t, ht, rfl⟩
    by_cases hTH : T' ∈ H
    · left
      exact Set.mem_biUnion (x := T') ⟨hne, hTH⟩ ((hEmem T' t ht).2 hT')
    · right
      exact Set.mem_biUnion (x := T') ⟨hne, hTH⟩ ((hEmem T' t ht).2 hT')
  have hdis : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ A → t ∈ B → False := by
    intro t ht hAt hBt
    obtain ⟨T', ⟨_, hT'H⟩, hT'E⟩ := Set.mem_iUnion₂.1 hAt
    obtain ⟨T'', ⟨_, hT''H⟩, hT''E⟩ := Set.mem_iUnion₂.1 hBt
    obtain ⟨S, hS, hST⟩ := (thm_7_5 T' T'').1
      ⟨γ t, (hEmem T' t ht).1 hT'E, (hEmem T'' t ht).1 hT''E⟩
    apply hT''H
    have : T'' = S⁻¹ * T' := by rw [hST]; simp
    rw [this]
    exact H.mul_mem (H.inv_mem (Subgroup.subset_closure hS)) hT'H
  have hconn := isPreconnected_iff_subset_of_disjoint_closed.1
    (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)) A B hAc hBc hcover (by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨ht, hAt, hBt⟩
      exact hdis t ht hAt hBt)
  have h0 : (0 : ℝ) ∈ A := by
    have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hγ0 : γ 0 = F₁ := by simp [hγ]
    have himg : γ 0 ∈ img 1 := ⟨F₁, hF₁.1, by rw [hγ0]; exact act_one _⟩
    exact Set.mem_biUnion (x := (1 : GL (Fin n) ℤ))
      ⟨⟨γ 0, himg, 0, h0Icc, rfl⟩, H.one_mem⟩ ((hEmem 1 0 h0Icc).2 himg)
  have hAall : Set.Icc (0 : ℝ) 1 ⊆ A := by
    rcases hconn with h | h
    · exact h
    · exact absurd (h ⟨le_rfl, zero_le_one⟩) (fun hB0 => hdis 0 ⟨le_rfl, zero_le_one⟩ h0 hB0)
  have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨T', ⟨_, hT'H⟩, hT'E⟩ := Set.mem_iUnion₂.1 (hAall h1Icc)
  have hγ1 : γ 1 = F₂ := by simp [hγ]
  have himg : F₂ ∈ img T' := by rw [← hγ1]; exact (hEmem T' 1 h1Icc).1 hT'E
  rw [mem_img_iff_red7] at himg
  have hD : IsSignDiagonal (T * T'⁻¹) := hF₁.2 (T * T'⁻¹) (by
    rw [Units.val_mul, act_mul]; exact himg)
  have hDsigma : T * T'⁻¹ ∈ sigma n :=
    ⟨act (T * T'⁻¹).val F₁, hD.act_reduced7 hF₁.1, F₁, hF₁.1, rfl⟩
  have : T = (T * T'⁻¹) * T' := by simp
  rw [this]
  exact H.mul_mem (Subgroup.subset_closure hDsigma) hT'H

end QuadFormsKB.Reduction
