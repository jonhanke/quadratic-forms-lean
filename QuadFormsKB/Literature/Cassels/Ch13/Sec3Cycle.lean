/-
# Cassels, Chapter 13, §3: the cycle of classically reduced forms (Lemma 3.6 Corollary, Lemma 3.7)

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §3, pp. 296–298: the two-sided sequence
$f_m$ of classically reduced forms properly or improperly equivalent to a given one ((3.48)–(3.50)), the
Corollary to Lemma 3.6 (every classically reduced form equivalent to $f$ is in the sequence — corrected here, see
below), Lemma 3.7 (periodicity, generators of $O^+(f)$, improper equivalence of $f$ with $-f$) and its Corollary
(the Pell equation with $-1$).

**The sequence.** Cassels constructs $f_m$ from lattice points $\vec{\xi}_m$ and only sketches the construction. Here
it is defined directly on the forms. A classically reduced form (`IsClassicallyReduced`, (3.34)–(3.35)) is
$f = a(x + \theta y)(x - \phi y)$ with $\theta > 1 > \phi > 0$; for $f$ with matrix $F$, $a = F_{00}$,
$u = F_{01}/F_{00}$, $k = F_{11}/F_{00}$, the roots are $\theta = u + \sqrt{u^2 - k}$, $\phi = \sqrt{u^2 - k} - u$
(`redTheta`, `redPhi`). Cassels' relation $\vec{\xi}_{m+1} = w_m\vec{\xi}_m + \vec{\xi}_{m-1}$ ((3.50); the display is
garbled in the machine-read text and is reconstructed from the sign conditions (3.44)–(3.48)) says
$$f_{m+1}(x, y) = f_m(y, x + w_m y), \qquad w_m = \lfloor 1/\phi_m \rfloor \ge 1,$$
and backwards $f_{m-1}(x, y) = f_m(-v x + y, x)$ with $v = \lfloor \theta_m \rfloor = w_{m-1}$. In terms of continued
fractions, $1/\phi_m = [w_m; w_{m+1}, \dots]$ and $\theta_m = [w_{m-1}; w_{m-2}, \dots]$.

Conventions as in `Ch13/Sec3Classical.lean`: a real binary form is its symmetric matrix $F$, $f(\vec{x}) = $
`val F x`, and `act T F` $= T^{\mathsf T}FT$ is the form $f(T\vec{x})$.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec3Classical
import QuadFormsKB.Literature.Cassels.Ch13.Sec3
import QuadFormsKB.Literature.Cassels.Ch13.Sec2

open Matrix

namespace QuadFormsKB.Reduction

/-- **The root $\theta$ of a classically reduced form** (Cassels, Ch. 13, (3.34), p. 295): for
$f = a(x + \theta y)(x - \phi y)$ with matrix $F$, $\theta = u + \sqrt{u^2 - k}$ where $u = F_{01}/F_{00}$,
$k = F_{11}/F_{00}$. -/
noncomputable def redTheta (F : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  F 0 1 / F 0 0 + √((F 0 1 / F 0 0) ^ 2 - F 1 1 / F 0 0)

/-- **The root $\phi$ of a classically reduced form** (Cassels, Ch. 13, (3.34), p. 295): $\phi = \sqrt{u^2 - k} - u$,
notation as for `redTheta`. -/
noncomputable def redPhi (F : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  √((F 0 1 / F 0 0) ^ 2 - F 1 1 / F 0 0) - F 0 1 / F 0 0

/-- The matrix $\begin{pmatrix} 0 & 1 \\ 1 & w \end{pmatrix}$ of the step $(x, y) \mapsto (y, x + wy)$
(determinant $-1$). -/
def cycleMat (w : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, w]

/-- The integer $w = \lfloor 1/\phi \rfloor$ of a classically reduced form (Cassels' $w_m$ for $f = f_m$). -/
noncomputable def cycleW (F : Matrix (Fin 2) (Fin 2) ℝ) : ℤ := ⌊(redPhi F)⁻¹⌋

/-- The next form of the cycle: $f_{m+1}(x, y) = f_m(y, x + w_m y)$. -/
noncomputable def cycleNext (F : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  act (cycleMat (cycleW F)) F

/-- The previous form of the cycle: $f_{m-1}(x, y) = f_m(-v x + y, x)$ with $v = \lfloor \theta_m \rfloor$
(the inverse of the step `cycleNext`). -/
noncomputable def cyclePrev (F : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  act !![-⌊redTheta F⌋, 1; 1, 0] F

/-- **The sequence $f_m$ of classically reduced forms** (Cassels, Ch. 13, §3, (3.48)–(3.49), p. 297), $m \in \mathbb{Z}$,
starting from $f_0 = f$. -/
@[kb "cassels1978" "Ch. 13, §3, (3.48)–(3.49), p. 297 (the sequence f_m)"]
noncomputable def cycleForm (F : Matrix (Fin 2) (Fin 2) ℝ) : ℤ → Matrix (Fin 2) (Fin 2) ℝ
  | Int.ofNat n => cycleNext^[n] F
  | Int.negSucc n => cyclePrev^[n + 1] F

/-- **The sequence $w_m$** (Cassels, Ch. 13, §3, (3.50), p. 297): $w_m = \lfloor 1/\phi_m \rfloor$ for the form $f_m$. -/
@[kb "cassels1978" "Ch. 13, §3, (3.50), p. 297 (the sequence w_m)"]
noncomputable def cycleSeqW (F : Matrix (Fin 2) (Fin 2) ℝ) (m : ℤ) : ℤ := cycleW (cycleForm F m)

/-- The matrix $B_n = \begin{pmatrix} 0 & 1 \\ 1 & w_0 \end{pmatrix} \cdots \begin{pmatrix} 0 & 1 \\ 1 & w_{n-1}
\end{pmatrix}$ with $f_n(\vec{x}) = f(B_n\vec{x})$; its columns are Cassels' basis $\vec{a}_n, \vec{a}_{n+1}$ when
$f = f_0$ is taken in the basis $\vec{a}_0, \vec{a}_1$. -/
noncomputable def cycleBasis (F : Matrix (Fin 2) (Fin 2) ℝ) : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => 1
  | n + 1 => cycleBasis F n * cycleMat (cycleSeqW F n)

/-! ### Helpers: factorization data of reduced forms -/

/-- Helper: `F` is a symmetric form `F₀₀ (x₀ + θ x₁)(x₀ − φ x₁)` with `θ > 1 > φ > 0` and `F₀₀ ≠ 0`. -/
structure Rd (F : Matrix (Fin 2) (Fin 2) ℝ) (θ φ : ℝ) : Prop where
  symm : F.IsSymm
  a_ne : F 0 0 ≠ 0
  one_lt : 1 < θ
  phi_pos : 0 < φ
  phi_lt : φ < 1
  val_eq : ∀ x : Fin 2 → ℝ, val F x = F 0 0 * (x 0 + θ * x 1) * (x 0 - φ * x 1)

/-- Helper: anisotropy over `ℚ`. -/
def Aniso (F : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ x : Fin 2 → ℚ, x ≠ 0 → val F (fun i => (x i : ℝ)) ≠ 0

theorem rd_of_red {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (h : IsClassicallyReduced F) :
    ∃ θ φ, Rd F θ φ := by
  obtain ⟨A, θ, φ, hA, hθ, hφ0, hφ1, h⟩ := h
  have hA' : F 0 0 = A := by
    have := h ![1, 0]
    rw [val_fin2 hF] at this
    simpa using this
  exact ⟨θ, φ, hF, by rw [hA']; exact hA, hθ, hφ0, hφ1, fun x => by rw [h x, hA']⟩

theorem Rd.isClassicallyReduced {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) :
    IsClassicallyReduced F :=
  ⟨F 0 0, θ, φ, h.a_ne, h.one_lt, h.phi_pos, h.phi_lt, h.val_eq⟩

theorem Rd.entries {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) :
    F 0 1 = F 0 0 * (θ - φ) / 2 ∧ F 1 1 = -(F 0 0 * θ * φ) := by
  have h1 := h.val_eq ![0, 1]
  have h2 := h.val_eq ![1, 1]
  rw [val_fin2 h.symm] at h1 h2
  simp at h1 h2
  constructor <;> nlinarith

theorem Rd.red {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) :
    redTheta F = θ ∧ redPhi F = φ := by
  obtain ⟨e1, e2⟩ := h.entries
  have ha := h.a_ne
  have e1' : F 0 1 / F 0 0 = (θ - φ) / 2 := by rw [e1]; field_simp
  have e2' : F 1 1 / F 0 0 = -(θ * φ) := by rw [e2]; field_simp
  have hq : (F 0 1 / F 0 0) ^ 2 - F 1 1 / F 0 0 = ((θ + φ) / 2) ^ 2 := by
    rw [e1', e2']; ring
  have hs : √((F 0 1 / F 0 0) ^ 2 - F 1 1 / F 0 0) = (θ + φ) / 2 := by
    rw [hq]; exact Real.sqrt_sq (by linarith [h.phi_pos, h.one_lt])
  unfold redTheta redPhi
  rw [hs, e1']
  constructor <;> ring

theorem rd_of_val {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : G.IsSymm) {a θ φ : ℝ} (ha : a ≠ 0) (h1 : 1 < θ)
    (h2 : 0 < φ) (h3 : φ < 1) (hv : ∀ x : Fin 2 → ℝ, val G x = a * (x 0 + θ * x 1) * (x 0 - φ * x 1)) :
    Rd G θ φ := by
  have hA : G 0 0 = a := by
    have := hv ![1, 0]
    rw [val_fin2 hG] at this
    simpa using this
  exact ⟨hG, by rw [hA]; exact ha, h1, h2, h3, fun x => by rw [hv x, hA]⟩

/-- Helper: two factorizations of the same form share their roots (up to the swap). -/
theorem fac_unique {a θ φ θ' φ' : ℝ} (ha : a ≠ 0)
    (h : ∀ x : Fin 2 → ℝ, a * (x 0 + θ * x 1) * (x 0 - φ * x 1) = a * (x 0 + θ' * x 1) * (x 0 - φ' * x 1)) :
    (θ = θ' ∧ φ = φ') ∨ (θ = -φ' ∧ φ = -θ') := by
  have h2 := h ![0, 1]
  have h3 := h ![1, 1]
  simp at h2 h3
  have hp : a * (θ * φ) = a * (θ' * φ') := by linear_combination h2
  have hd : a * (θ - φ) = a * (θ' - φ') := by linear_combination h3 + hp
  have hp' : θ * φ = θ' * φ' := mul_left_cancel₀ ha hp
  have hd' : θ - φ = θ' - φ' := mul_left_cancel₀ ha hd
  have : (θ - θ') * (θ + φ') = 0 := by
    have : φ = θ - (θ' - φ') := by linarith
    rw [this] at hp'
    linear_combination hp'
  rcases mul_eq_zero.1 this with h | h
  · left; constructor <;> linarith
  · right; constructor <;> linarith

theorem isSymm_act {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (T : Matrix (Fin 2) (Fin 2) ℤ) :
    (act T F).IsSymm := by
  unfold Matrix.IsSymm act
  simp [Matrix.transpose_mul, Matrix.mul_assoc, hF.eq]

theorem castM_cycleMat_mulVec (w : ℤ) (x : Fin 2 → ℝ) :
    castM (cycleMat w) *ᵥ x = ![x 1, x 0 + w * x 1] := by
  ext i; fin_cases i <;> simp [castM, cycleMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem castM_prevMat_mulVec (v : ℤ) (x : Fin 2 → ℝ) :
    castM !![-v, 1; 1, 0] *ᵥ x = ![-v * x 0 + x 1, x 0] := by
  ext i; fin_cases i <;> simp [castM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Rd.val_next {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (w : ℤ) (x : Fin 2 → ℝ) :
    val (act (cycleMat w) F) x =
      (-(F 0 0 * θ * φ)) * (x 0 + (w + 1 / θ) * x 1) * (x 0 - (1 / φ - w) * x 1) := by
  have hθ : θ ≠ 0 := by linarith [h.one_lt]
  have hφ : φ ≠ 0 := h.phi_pos.ne'
  rw [val_act, castM_cycleMat_mulVec, h.val_eq]
  simp
  field_simp
  ring

theorem Rd.val_prev {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (v : ℤ) (x : Fin 2 → ℝ)
    (h1 : θ - v ≠ 0) (h2 : (v : ℝ) + φ ≠ 0) :
    val (act !![-v, 1; 1, 0] F) x =
      (-(F 0 0 * (θ - v) * (v + φ))) * (x 0 + (1 / (θ - v)) * x 1) * (x 0 - (1 / (v + φ)) * x 1) := by
  rw [val_act, castM_prevMat_mulVec, h.val_eq]
  simp
  field_simp
  ring

theorem val_e0 {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) : val F ![1, 0] = F 0 0 := by
  rw [val_fin2 hF]; simp

theorem Rd.theta_ne {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) (n : ℤ) :
    (n : ℝ) ≠ θ := by
  intro hn
  apply hA ![-n, 1] (by intro h0; have := congrFun h0 1; simp at this)
  rw [h.val_eq]
  simp [← hn]

theorem Rd.phi_ne {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) (n : ℤ) :
    (n : ℝ) ≠ 1 / φ := by
  intro hn
  have hφ := h.phi_pos.ne'
  have hφn : φ * n = 1 := by rw [hn]; field_simp
  apply hA ![1, n] (by intro h0; have := congrFun h0 0; simp at this)
  rw [h.val_eq]
  simp
  right
  linarith

theorem aniso_act {F : Matrix (Fin 2) (Fin 2) ℝ} (hA : Aniso F) {T : Matrix (Fin 2) (Fin 2) ℤ}
    (hT : T.det ≠ 0) : Aniso (act T F) := by
  intro x hx
  have hdet : (T.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    have : (T.map (Int.cast : ℤ → ℚ)).det = (T.det : ℚ) := by
      simpa [RingHom.mapMatrix_apply] using ((Int.castRingHom ℚ).map_det T).symm
    rw [this]; exact_mod_cast hT
  have hy : (T.map (Int.cast : ℤ → ℚ)) *ᵥ x ≠ 0 := fun h0 => hx (Matrix.eq_zero_of_mulVec_eq_zero hdet h0)
  have heq : castM T *ᵥ (fun i => (x i : ℝ)) = fun i => ((((T.map (Int.cast : ℤ → ℚ)) *ᵥ x) i : ℚ) : ℝ) := by
    ext i
    simp [Matrix.mulVec, dotProduct, castM]
  rw [val_act, heq]
  exact hA _ hy

theorem Rd.next_iff {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ)
    (hirr : ∀ n : ℤ, (n : ℝ) ≠ 1 / φ) (w : ℤ) :
    IsClassicallyReduced (act (cycleMat w) F) ↔ w = ⌊1 / φ⌋ := by
  have hφ1 : 1 < 1 / φ := by rw [lt_div_iff₀ h.phi_pos]; linarith [h.phi_lt]
  have hθ0 : 0 < 1 / θ := by have := h.one_lt; positivity
  have hsym := isSymm_act h.symm (cycleMat w)
  have hne : -(F 0 0 * θ * φ) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero h.a_ne (by linarith [h.one_lt])) h.phi_pos.ne')
  constructor
  · intro hr
    obtain ⟨θ'', φ'', hR⟩ := rd_of_red hsym hr
    have hG00 : act (cycleMat w) F 0 0 = -(F 0 0 * θ * φ) := by
      have h1 := h.val_next w ![1, 0]
      rw [val_e0 hsym] at h1
      simpa using h1
    rcases fac_unique (a := -(F 0 0 * θ * φ)) hne (θ' := θ'') (φ' := φ'') (fun x => by
        rw [← h.val_next, hR.val_eq, hG00]) with ⟨_, h2⟩ | ⟨h1, h2⟩
    · symm
      rw [Int.floor_eq_iff]
      constructor <;> linarith [hR.phi_pos, hR.phi_lt]
    · exfalso
      linarith [hR.phi_pos, hR.one_lt]
  · intro hw
    subst hw
    have hw1 : 1 ≤ ⌊1 / φ⌋ := Int.le_floor.2 (by exact_mod_cast hφ1.le)
    have hw1' : (1 : ℝ) ≤ (⌊1 / φ⌋ : ℤ) := by exact_mod_cast hw1
    have hle := Int.floor_le (1 / φ)
    have hlt := Int.lt_floor_add_one (1 / φ)
    have hlt' : (⌊1 / φ⌋ : ℝ) < 1 / φ := lt_of_le_of_ne hle (hirr _)
    exact (rd_of_val hsym hne (by linarith) (by linarith) (by linarith) (fun x => h.val_next _ x)).isClassicallyReduced

/-- Helper: the data attached to a good form: factorization data and anisotropy. -/
def Good (F : Matrix (Fin 2) (Fin 2) ℝ) : Prop := (∃ θ φ, Rd F θ φ) ∧ Aniso F

theorem Rd.cycleW_eq {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) :
    cycleW F = ⌊1 / φ⌋ := by
  unfold cycleW; rw [h.red.2, one_div]

theorem Rd.next {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) :
    Rd (cycleNext F) (cycleW F + 1 / θ) (1 / φ - cycleW F) := by
  have hφ1 : 1 < 1 / φ := by rw [lt_div_iff₀ h.phi_pos]; linarith [h.phi_lt]
  have hθ0 : 0 < 1 / θ := by have := h.one_lt; positivity
  have hne : -(F 0 0 * θ * φ) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero h.a_ne (by linarith [h.one_lt])) h.phi_pos.ne')
  have hW := h.cycleW_eq
  have hw1 : 1 ≤ ⌊1 / φ⌋ := Int.le_floor.2 (by exact_mod_cast hφ1.le)
  have hw1' : (1 : ℝ) ≤ (⌊1 / φ⌋ : ℤ) := by exact_mod_cast hw1
  have hle := Int.floor_le (1 / φ)
  have hlt := Int.lt_floor_add_one (1 / φ)
  have hlt' : (⌊1 / φ⌋ : ℝ) < 1 / φ := lt_of_le_of_ne hle (h.phi_ne hA _)
  unfold cycleNext
  rw [hW]
  exact rd_of_val (isSymm_act h.symm _) hne (by linarith) (by linarith) (by linarith)
    (fun x => h.val_next _ x)

theorem Rd.cycleW_ge {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) : 1 ≤ cycleW F := by
  rw [h.cycleW_eq]
  have hφ1 : 1 < 1 / φ := by rw [lt_div_iff₀ h.phi_pos]; linarith [h.phi_lt]
  exact Int.le_floor.2 (by exact_mod_cast hφ1.le)

theorem Rd.prev {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) :
    Rd (cyclePrev F) (1 / (θ - ⌊θ⌋)) (1 / (⌊θ⌋ + φ)) ∧ cycleW (cyclePrev F) = ⌊θ⌋ := by
  have hv1 : 1 ≤ ⌊θ⌋ := Int.le_floor.2 (by exact_mod_cast h.one_lt.le)
  have hv1' : (1 : ℝ) ≤ (⌊θ⌋ : ℤ) := by exact_mod_cast hv1
  have hle := Int.floor_le θ
  have hlt := Int.lt_floor_add_one θ
  have hlt' : (⌊θ⌋ : ℝ) < θ := lt_of_le_of_ne hle (h.theta_ne hA _)
  have hp1 : 0 < θ - ⌊θ⌋ := by linarith
  have hp2 : 0 < (⌊θ⌋ : ℝ) + φ := by linarith [h.phi_pos]
  have hne : -(F 0 0 * (θ - ⌊θ⌋) * (⌊θ⌋ + φ)) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero h.a_ne hp1.ne') hp2.ne')
  have hR : Rd (cyclePrev F) (1 / (θ - ⌊θ⌋)) (1 / (⌊θ⌋ + φ)) := by
    unfold cyclePrev
    rw [h.red.1]
    refine rd_of_val (isSymm_act h.symm _) hne ?_ (one_div_pos.2 hp2) ?_
      (fun x => h.val_prev _ x hp1.ne' hp2.ne')
    · rw [lt_div_iff₀ hp1]; linarith
    · rw [div_lt_one hp2]; linarith [h.phi_pos]
  refine ⟨hR, ?_⟩
  rw [hR.cycleW_eq, one_div_one_div]
  rw [Int.floor_eq_iff]
  constructor <;> linarith [h.phi_pos, h.phi_lt]

theorem Rd.next_prev {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) :
    cycleNext (cyclePrev F) = F := by
  obtain ⟨_, hW⟩ := h.prev hA
  unfold cycleNext
  rw [hW]
  unfold cyclePrev
  rw [h.red.1, ← act_mul]
  have : (!![-⌊θ⌋, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) * cycleMat ⌊θ⌋ = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [cycleMat]
  rw [this, act_one]

theorem Rd.prev_next {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) :
    cyclePrev (cycleNext F) = F := by
  have hN := h.next hA
  unfold cyclePrev
  rw [hN.red.1]
  have hf : ⌊(cycleW F : ℝ) + 1 / θ⌋ = cycleW F := by
    rw [Int.floor_eq_iff]
    have hθ0 : 0 < 1 / θ := by have := h.one_lt; positivity
    have : 1 / θ < 1 := by rw [div_lt_one (by linarith [h.one_lt])]; exact h.one_lt
    constructor <;> linarith
  rw [hf]
  unfold cycleNext
  rw [← act_mul]
  have : cycleMat (cycleW F) * (!![-cycleW F, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [cycleMat]
  rw [this, act_one]

theorem good_next {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) : Good (cycleNext F) := by
  obtain ⟨⟨θ, φ, h⟩, hA⟩ := hG
  refine ⟨⟨_, _, h.next hA⟩, ?_⟩
  unfold cycleNext
  refine aniso_act hA ?_
  simp [cycleMat, Matrix.det_fin_two_of]

theorem good_prev {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) : Good (cyclePrev F) := by
  obtain ⟨⟨θ, φ, h⟩, hA⟩ := hG
  refine ⟨⟨_, _, (h.prev hA).1⟩, ?_⟩
  unfold cyclePrev
  refine aniso_act hA ?_
  simp [Matrix.det_fin_two_of]

theorem Good.next_prev {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) : cycleNext (cyclePrev F) = F := by
  obtain ⟨⟨θ, φ, h⟩, hA⟩ := hG
  exact h.next_prev hA

theorem Good.prev_next {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) : cyclePrev (cycleNext F) = F := by
  obtain ⟨⟨θ, φ, h⟩, hA⟩ := hG
  exact h.prev_next hA

theorem good_next_iter {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) (n : ℕ) : Good (cycleNext^[n] F) := by
  induction n with
  | zero => exact hG
  | succ n ih => rw [Function.iterate_succ_apply']; exact good_next ih

theorem good_prev_iter {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) (n : ℕ) : Good (cyclePrev^[n] F) := by
  induction n with
  | zero => exact hG
  | succ n ih => rw [Function.iterate_succ_apply']; exact good_prev ih

theorem cycleForm_zero (F : Matrix (Fin 2) (Fin 2) ℝ) : cycleForm F 0 = F := rfl

theorem good_cycleForm {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) (m : ℤ) : Good (cycleForm F m) := by
  cases m with
  | ofNat n => exact good_next_iter hG n
  | negSucc n => exact good_prev_iter hG (n + 1)

theorem cycleForm_succ {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) (m : ℤ) :
    cycleForm F (m + 1) = cycleNext (cycleForm F m) := by
  cases m with
  | ofNat n =>
    have : (Int.ofNat n : ℤ) + 1 = Int.ofNat (n + 1) := rfl
    rw [this]
    simp [cycleForm, Function.iterate_succ_apply']
  | negSucc n =>
    cases n with
    | zero =>
      have : Int.negSucc 0 + 1 = 0 := rfl
      rw [this, cycleForm_zero]
      simp only [cycleForm, zero_add, Function.iterate_one]
      exact hG.next_prev.symm
    | succ k =>
      have : Int.negSucc (k + 1) + 1 = Int.negSucc k := rfl
      rw [this]
      simp only [cycleForm]
      rw [Function.iterate_succ_apply' (f := cyclePrev) (n := k + 1)]
      exact (good_prev_iter hG (k + 1)).next_prev.symm

theorem cycleSeqW_eq (F : Matrix (Fin 2) (Fin 2) ℝ) (m : ℤ) :
    cycleSeqW F m = cycleW (cycleForm F m) := rfl

theorem det_cycleMat (w : ℤ) : (cycleMat w).det = -1 := by
  simp [cycleMat, Matrix.det_fin_two_of]

theorem cycleBasis_spec {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) (n : ℕ) :
    cycleForm F n = act (cycleBasis F n) F ∧ (cycleBasis F n).det = (-1) ^ n := by
  induction n with
  | zero => simp [cycleBasis, act_one, cycleForm_zero]
  | succ n ih =>
    have e : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, cycleForm_succ hG]
    refine ⟨?_, ?_⟩
    · rw [ih.1]
      simp only [cycleBasis, cycleNext, cycleSeqW_eq, ← act_mul]
      rw [ih.1]
    · simp only [cycleBasis, Matrix.det_mul, ih.2, det_cycleMat, pow_succ]

/-- **(3.48)–(3.50)** (Cassels, Ch. 13, §3, p. 297): let $f$ be a classically reduced real binary form without
nonzero rational zeros. Every $f_m$ is classically reduced; $w_m \ge 1$; $f_{m+1}(x, y) = f_m(y, x + w_m y)$, and
$w_m$ is the only integer $w$ for which $f_m(y, x + wy)$ is classically reduced. Also $f_n(\vec{x}) = f(B_n\vec{x})$
with $\det B_n = (-1)^n$, so $f_n$ is properly equivalent to $f$ for even $n$ and improperly for odd $n$. (Cassels
derives the sequence from lattice points; the displays are garbled in the machine-read text and are reconstructed.) -/
@[kb "cassels1978" "Ch. 13, §3, (3.48)–(3.50), p. 297"]
theorem cycleForm_spec {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (hred : IsClassicallyReduced F)
    (haniso : ∀ x : Fin 2 → ℚ, x ≠ 0 → val F (fun i => (x i : ℝ)) ≠ 0) :
    cycleForm F 0 = F ∧
    (∀ m : ℤ, IsClassicallyReduced (cycleForm F m) ∧ 1 ≤ cycleSeqW F m ∧
      cycleForm F (m + 1) = act (cycleMat (cycleSeqW F m)) (cycleForm F m) ∧
      ∀ w : ℤ, IsClassicallyReduced (act (cycleMat w) (cycleForm F m)) ↔ w = cycleSeqW F m) ∧
    ∀ n : ℕ, cycleForm F n = act (cycleBasis F n) F ∧ (cycleBasis F n).det = (-1) ^ n := by
  have hG : Good F := ⟨rd_of_red hF hred, haniso⟩
  refine ⟨cycleForm_zero F, fun m => ?_, fun n => cycleBasis_spec hG n⟩
  obtain ⟨⟨θ, φ, h⟩, hA⟩ := good_cycleForm hG m
  refine ⟨h.isClassicallyReduced, h.cycleW_ge, cycleForm_succ hG m, fun w => ?_⟩
  rw [cycleSeqW_eq, h.cycleW_eq]
  exact h.next_iff (h.phi_ne hA) w

/-! ### Helpers: reduced pairs of lattice vectors -/

/-- Helper: the linear form `(a, b) ↦ a - α b` on `ℤ²`. -/
noncomputable def lf (α : ℝ) (a b : ℤ) : ℝ := (a : ℝ) - α * b

/-- Helper: first column of a matrix under `lf α`. -/
noncomputable def lc0 (α : ℝ) (T : Matrix (Fin 2) (Fin 2) ℤ) : ℝ := lf α (T 0 0) (T 1 0)

/-- Helper: second column of a matrix under `lf α`. -/
noncomputable def lc1 (α : ℝ) (T : Matrix (Fin 2) (Fin 2) ℤ) : ℝ := lf α (T 0 1) (T 1 1)

/-- Helper: `lf α` has no nonzero integral zeros. -/
def NZ (α : ℝ) : Prop := ∀ a b : ℤ, lf α a b = 0 → a = 0 ∧ b = 0

/-- Helper: the columns of `T` form a reduced pair for `(lf α, lf β)` with ratios `c`, `d`. -/
def RP (α β : ℝ) (T : Matrix (Fin 2) (Fin 2) ℤ) (c d : ℝ) : Prop :=
  (T.det = 1 ∨ T.det = -1) ∧ 1 < c ∧ 0 < d ∧ d < 1 ∧
    lc1 α T = c * lc0 α T ∧ lc1 β T = -d * lc0 β T

theorem box_core {c d : ℝ} (hc : 1 < c) (hd0 : 0 < d) (hd1 : d < 1) (x y : ℤ) (hxy : x ≠ 0 ∨ y ≠ 0)
    (h1 : |(x : ℝ) + c * y| < c) (h2 : |(x : ℝ) - d * y| < 1) : False := by
  rw [abs_lt] at h1 h2
  have hx : x = 0 ∨ 1 ≤ x ∨ x ≤ -1 := by omega
  have hy : y = 0 ∨ 1 ≤ y ∨ y ≤ -1 := by omega
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · omega
  · have : (1 : ℝ) ≤ y := by exact_mod_cast hy
    have hx0 : (x : ℝ) = 0 := by exact_mod_cast hx
    nlinarith
  · have : (y : ℝ) ≤ -1 := by exact_mod_cast hy
    have hx0 : (x : ℝ) = 0 := by exact_mod_cast hx
    nlinarith
  · have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have hy0 : (y : ℝ) = 0 := by exact_mod_cast hy
    nlinarith
  · have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have : (1 : ℝ) ≤ y := by exact_mod_cast hy
    nlinarith
  · have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have : (y : ℝ) ≤ -1 := by exact_mod_cast hy
    nlinarith
  · have : (x : ℝ) ≤ -1 := by exact_mod_cast hx
    have hy0 : (y : ℝ) = 0 := by exact_mod_cast hy
    nlinarith
  · have : (x : ℝ) ≤ -1 := by exact_mod_cast hx
    have : (1 : ℝ) ≤ y := by exact_mod_cast hy
    nlinarith
  · have : (x : ℝ) ≤ -1 := by exact_mod_cast hx
    have : (y : ℝ) ≤ -1 := by exact_mod_cast hy
    nlinarith

theorem col0_ne {T : Matrix (Fin 2) (Fin 2) ℤ} (h : T.det = 1 ∨ T.det = -1) : T 0 0 ≠ 0 ∨ T 1 0 ≠ 0 := by
  by_contra hc
  push Not at hc
  rw [Matrix.det_fin_two, hc.1, hc.2] at h
  omega

theorem RP.lc0_ne {α β : ℝ} {T : Matrix (Fin 2) (Fin 2) ℤ} {c d : ℝ} (hα : NZ α) (h : RP α β T c d) :
    lc0 α T ≠ 0 := by
  intro h0
  obtain ⟨a, b⟩ := hα _ _ h0
  rcases col0_ne h.1 with h1 | h1 <;> contradiction

theorem RP.lc0_ne' {α β : ℝ} {T : Matrix (Fin 2) (Fin 2) ℤ} {c d : ℝ} (hβ : NZ β) (h : RP α β T c d) :
    lc0 β T ≠ 0 := by
  intro h0
  obtain ⟨a, b⟩ := hβ _ _ h0
  rcases col0_ne h.1 with h1 | h1 <;> contradiction

/-- Helper: integral coordinates of a lattice point in the basis given by the columns of `T`. -/
theorem coords {T : Matrix (Fin 2) (Fin 2) ℤ} (h : T.det = 1 ∨ T.det = -1) (a b : ℤ) :
    ∃ x y : ℤ, a = x * T 0 0 + y * T 0 1 ∧ b = x * T 1 0 + y * T 1 1 := by
  rw [Matrix.det_fin_two] at h
  rcases h with h | h
  · exact ⟨a * T 1 1 - b * T 0 1, T 0 0 * b - T 1 0 * a, by linear_combination (-a) * h,
      by linear_combination (-b) * h⟩
  · exact ⟨-(a * T 1 1 - b * T 0 1), -(T 0 0 * b - T 1 0 * a), by linear_combination a * h,
      by linear_combination b * h⟩

theorem lf_coords (γ : ℝ) {T : Matrix (Fin 2) (Fin 2) ℤ} {a b x y : ℤ}
    (h1 : a = x * T 0 0 + y * T 0 1) (h2 : b = x * T 1 0 + y * T 1 1) :
    lf γ a b = x * lc0 γ T + y * lc1 γ T := by
  simp only [lf, lc0, lc1, h1, h2]; push_cast; ring

theorem RP.box {α β : ℝ} {T : Matrix (Fin 2) (Fin 2) ℤ} {c d : ℝ} (hα : NZ α) (hβ : NZ β)
    (h : RP α β T c d) (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ¬ (|lf α a b| < |lc1 α T| ∧ |lf β a b| < |lc0 β T|) := by
  rintro ⟨h1, h2⟩
  obtain ⟨x, y, e1, e2⟩ := coords h.1 a b
  have hA := h.lc0_ne hα
  have hB := h.lc0_ne' hβ
  obtain ⟨_, hc, hd0, hd1, hU, hV⟩ := h
  rw [lf_coords α e1 e2, hU] at h1
  rw [lf_coords β e1 e2, hV] at h2
  have e3 : (x : ℝ) * lc0 α T + y * (c * lc0 α T) = lc0 α T * (x + c * y) := by ring
  have e4 : (x : ℝ) * lc0 β T + y * (-d * lc0 β T) = lc0 β T * (x - d * y) := by ring
  rw [e3, abs_mul, abs_mul, abs_of_pos (by linarith : 0 < c)] at h1
  rw [e4, abs_mul] at h2
  have hAp : 0 ≤ |lc0 α T| := abs_nonneg _
  have h1' : |(x : ℝ) + c * y| < c := by
    have : abs (lc0 α T) * abs ((x : ℝ) + c * y) < abs (lc0 α T) * c := by linarith [h1, mul_comm c (abs (lc0 α T))]
    exact lt_of_mul_lt_mul_left this hAp
  have h2' : |(x : ℝ) - d * y| < 1 := by
    have : abs (lc0 β T) * abs ((x : ℝ) - d * y) < abs (lc0 β T) * 1 := by linarith
    exact lt_of_mul_lt_mul_left this (abs_nonneg _)
  refine box_core hc hd0 hd1 x y ?_ h1' h2'
  by_contra hxy
  push Not at hxy
  obtain ⟨hx, hy⟩ := hxy
  rw [hx, hy] at e1 e2
  simp at e1 e2
  rcases hab with h | h <;> contradiction

theorem RP.unique {α β : ℝ} {T S : Matrix (Fin 2) (Fin 2) ℤ} {c d c' d' : ℝ} (hα : NZ α) (hβ : NZ β)
    (hP : RP α β T c d) (hQ : RP α β S c' d')
    (h1 : |lc0 α T| ≤ |lc0 α S|) (h2 : |lc0 α S| < |lc1 α T|) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ S = ε • T := by
  have hA := hP.lc0_ne hα
  have hB := hP.lc0_ne' hβ
  have hA' := hQ.lc0_ne hα
  have hB' := hQ.lc0_ne' hβ
  have hS0 := col0_ne hQ.1
  have hT0 := col0_ne hP.1
  have hP' := hP
  have hQ' := hQ
  obtain ⟨hdT, hc, hd0, hd1, hU, hV⟩ := hP'
  obtain ⟨hdS, hc', hd0', hd1', hU', hV'⟩ := hQ'
  have s1 : |lc0 β T| ≤ |lc0 β S| := by
    by_contra hn; push Not at hn
    exact hP.box hα hβ (S 0 0) (S 1 0) hS0 ⟨h2, hn⟩
  have hlt : |lc0 α T| < |lc1 α S| := by
    have : |lc1 α S| = c' * |lc0 α S| := by
      rw [hU', abs_mul, abs_of_pos (by linarith)]
    have hpos : 0 < |lc0 α S| := abs_pos.2 hA'
    nlinarith
  have s2 : |lc0 β S| ≤ |lc0 β T| := by
    by_contra hn; push Not at hn
    exact hQ.box hα hβ (T 0 0) (T 1 0) hT0 ⟨hlt, hn⟩
  have habs : |lc0 β S| = |lc0 β T| := le_antisymm s2 s1
  obtain ⟨ε, hε, e0, e1⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ S 0 0 = ε * T 0 0 ∧ S 1 0 = ε * T 1 0 := by
    rcases abs_eq_abs.1 habs with h | h
    · have := hβ (S 0 0 - T 0 0) (S 1 0 - T 1 0) (by
        simp only [lc0, lf] at h ⊢; push_cast; linarith)
      refine ⟨1, Or.inl rfl, ?_, ?_⟩ <;> simp <;> omega
    · have := hβ (S 0 0 + T 0 0) (S 1 0 + T 1 0) (by
        simp only [lc0, lf] at h ⊢; push_cast; linarith)
      refine ⟨-1, Or.inr rfl, ?_, ?_⟩ <;> simp <;> omega
  obtain ⟨x, y, ex, ey⟩ := coords hdT (S 0 1) (S 1 1)
  have hl0 : ∀ γ, lc0 γ S = ε * lc0 γ T := by
    intro γ; simp only [lc0, lf, e0, e1]; push_cast; ring
  have hl1 : ∀ γ, lc1 γ S = x * lc0 γ T + y * lc1 γ T := fun γ => lf_coords γ ex ey
  have R1 : (x : ℝ) + y * c = c' * ε := by
    have := hU'
    rw [hl1, hl0, hU] at this
    apply mul_right_cancel₀ hA
    linear_combination this
  have R2 : (x : ℝ) - y * d = -d' * ε := by
    have := hV'
    rw [hl1, hl0, hV] at this
    apply mul_right_cancel₀ hB
    linear_combination this
  have hdet : S.det = ε * y * T.det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, e0, e1, ex, ey]; ring
  have hy : y = 1 ∨ y = -1 := by
    rcases hε with rfl | rfl <;> rcases hdT with h | h <;> rcases hdS with h' | h' <;>
      rw [hdet, h] at h' <;> omega
  have hxy : x = 0 ∧ y = ε := by
    rcases hε with rfl | rfl <;> rcases hy with rfl | rfl
    · refine ⟨?_, rfl⟩
      have a1 : (x : ℝ) < 1 := by push_cast at R1 R2; linarith
      have a2 : (-1 : ℝ) < x := by push_cast at R1 R2; linarith
      have a1' : x < 1 := by exact_mod_cast a1
      have a2' : -1 < x := by exact_mod_cast a2
      omega
    · exfalso; push_cast at R1 R2; linarith
    · exfalso; push_cast at R1 R2; linarith
    · refine ⟨?_, rfl⟩
      have a1 : (x : ℝ) < 1 := by push_cast at R1 R2; linarith
      have a2 : (-1 : ℝ) < x := by push_cast at R1 R2; linarith
      have a1' : x < 1 := by exact_mod_cast a1
      have a2' : -1 < x := by exact_mod_cast a2
      omega
  obtain ⟨hx0, hyε⟩ := hxy
  refine ⟨ε, hε, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e0, e1, ex, ey, hx0, hyε]

theorem Rd.nz {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) :
    NZ (-θ) ∧ NZ φ := by
  constructor
  · intro a b hab
    by_contra hne
    apply hA ![(a : ℚ), (b : ℚ)] (by
      intro h0
      apply hne
      refine ⟨?_, ?_⟩
      · have := congrFun h0 0; simpa using this
      · have := congrFun h0 1; simpa using this)
    rw [h.val_eq]
    have : (a : ℝ) + θ * b = 0 := by simp only [lf] at hab; linarith
    simp [this]
  · intro a b hab
    by_contra hne
    apply hA ![(a : ℚ), (b : ℚ)] (by
      intro h0
      apply hne
      refine ⟨?_, ?_⟩
      · have := congrFun h0 0; simpa using this
      · have := congrFun h0 1; simpa using this)
    rw [h.val_eq]
    have : (a : ℝ) - φ * b = 0 := by simp only [lf] at hab; linarith
    simp [this]

theorem lc0_mul_cycleMat (γ : ℝ) (B : Matrix (Fin 2) (Fin 2) ℤ) (w : ℤ) :
    lc0 γ (B * cycleMat w) = lc1 γ B := by
  simp [lc0, lc1, cycleMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem lc1_mul_cycleMat (γ : ℝ) (B : Matrix (Fin 2) (Fin 2) ℤ) (w : ℤ) :
    lc1 γ (B * cycleMat w) = lc0 γ B + w * lc1 γ B := by
  simp only [lc0, lc1, lf, cycleMat, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  ring

theorem rp_seq {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) (n : ℕ) :
    ∃ c d, Rd (cycleForm F n) c d ∧ RP (-θ) φ (cycleBasis F n) c d := by
  induction n with
  | zero =>
    refine ⟨θ, φ, h, ?_⟩
    refine ⟨by simp [cycleBasis], h.one_lt, h.phi_pos, h.phi_lt, ?_, ?_⟩ <;>
      simp [cycleBasis, lc0, lc1, lf]
  | succ n ih =>
    obtain ⟨c, d, hR, hRP⟩ := ih
    have hGood : Good F := ⟨⟨_, _, h⟩, hA⟩
    have hAn := (good_cycleForm hGood n).2
    have hN := hR.next hAn
    have e : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, cycleForm_succ hGood]
    refine ⟨_, _, hN, ?_⟩
    obtain ⟨hdet, hc, hd0, hd1, hU, hV⟩ := hRP
    have hw := hR.cycleW_ge
    have hc0 : c ≠ 0 := by linarith
    have hd : d ≠ 0 := hd0.ne'
    have hB : cycleBasis F (n + 1) = cycleBasis F n * cycleMat (cycleW (cycleForm F n)) := rfl
    rw [hB]
    refine ⟨?_, hN.one_lt, hN.phi_pos, hN.phi_lt, ?_, ?_⟩
    · rw [Matrix.det_mul, det_cycleMat]
      rcases hdet with h' | h' <;> rw [h'] <;> simp
    · rw [lc1_mul_cycleMat, lc0_mul_cycleMat]
      have : lc0 (-θ) (cycleBasis F n) = lc1 (-θ) (cycleBasis F n) / c := by rw [hU]; field_simp
      rw [this]; ring
    · rw [lc1_mul_cycleMat, lc0_mul_cycleMat]
      have : lc0 φ (cycleBasis F n) = -(lc1 φ (cycleBasis F n)) / d := by rw [hV]; field_simp
      rw [this]; ring

theorem rp_growth {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) (n : ℕ) :
    |lc0 (-θ) (cycleBasis F n)| < |lc0 (-θ) (cycleBasis F (n + 1))| ∧
    |lc0 (-θ) (cycleBasis F n)| + |lc0 (-θ) (cycleBasis F (n + 1))| ≤ |lc0 (-θ) (cycleBasis F (n + 2))| := by
  have hGood : Good F := ⟨⟨_, _, h⟩, hA⟩
  obtain ⟨c, d, hR, hRP⟩ := rp_seq h hA n
  obtain ⟨c1, d1, hR1, hRP1⟩ := rp_seq h hA (n + 1)
  have hw := hR.cycleW_ge
  obtain ⟨hdet, hc, hd0, hd1, hU, hV⟩ := hRP
  have hB : cycleBasis F (n + 1) = cycleBasis F n * cycleMat (cycleW (cycleForm F n)) := rfl
  have hB2 : cycleBasis F (n + 2) = cycleBasis F (n + 1) * cycleMat (cycleW (cycleForm F (n + 1))) := rfl
  have hα := (h.nz hA).1
  have hA0 : lc0 (-θ) (cycleBasis F n) ≠ 0 := RP.lc0_ne hα ⟨hdet, hc, hd0, hd1, hU, hV⟩
  have hpos : 0 < |lc0 (-θ) (cycleBasis F n)| := abs_pos.2 hA0
  have e1 : lc0 (-θ) (cycleBasis F (n + 1)) = c * lc0 (-θ) (cycleBasis F n) := by
    rw [hB, lc0_mul_cycleMat, hU]
  have hw' : (1 : ℝ) ≤ (cycleW (cycleForm F n) : ℝ) := by exact_mod_cast hw
  have e2 : lc0 (-θ) (cycleBasis F (n + 2)) =
      lc0 (-θ) (cycleBasis F n) * (1 + cycleW (cycleForm F n) * c) := by
    rw [hB2, lc0_mul_cycleMat, hB, lc1_mul_cycleMat, hU]
    ring
  rw [e2, e1, abs_mul, abs_mul, abs_of_pos (by linarith : 0 < c),
    abs_of_pos (by nlinarith : 0 < 1 + (cycleW (cycleForm F n) : ℝ) * c)]
  have hwc : c ≤ (cycleW (cycleForm F n) : ℝ) * c := by nlinarith
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hwc hpos.le]

theorem rp_ge_one {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) (n : ℕ) :
    (n : ℝ) ≤ |lc0 (-θ) (cycleBasis F n)| ∧ 1 ≤ |lc0 (-θ) (cycleBasis F n)| := by
  have h0 : |lc0 (-θ) (cycleBasis F 0)| = 1 := by simp [cycleBasis, lc0, lf]
  have key : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≤ |lc0 (-θ) (cycleBasis F (n + 1))| := by
    intro n
    induction n with
    | zero =>
      have := (rp_growth h hA 0).1
      rw [h0] at this
      simp; linarith
    | succ k ih =>
      have := (rp_growth h hA (k + 1)).1
      have h2 := (rp_growth h hA k).2
      have h3 := (rp_growth h hA k).1
      have h4 : (1 : ℝ) ≤ |lc0 (-θ) (cycleBasis F k)| := by
        clear ih h2 h3 this
        induction k with
        | zero => rw [h0]
        | succ j ihj => have := (rp_growth h hA j).1; linarith
      push_cast at ih ⊢
      linarith
  cases n with
  | zero => simp [h0]
  | succ k =>
    have := key k
    refine ⟨this, ?_⟩
    push_cast at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem classX {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F)
    {S : Matrix (Fin 2) (Fin 2) ℤ} {c d : ℝ} (hS : RP (-θ) φ S c d) (h1 : 1 ≤ |lc0 (-θ) S|) :
    ∃ m : ℕ, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ S = ε • cycleBasis F m := by
  classical
  obtain ⟨hα, hβ⟩ := h.nz hA
  have hex : ∃ n : ℕ, |lc0 (-θ) S| < |lc0 (-θ) (cycleBasis F n)| := by
    refine ⟨⌈|lc0 (-θ) S|⌉₊ + 1, ?_⟩
    have := (rp_ge_one h hA (⌈|lc0 (-θ) S|⌉₊ + 1)).1
    have h2 := Nat.le_ceil |lc0 (-θ) S|
    push_cast at this
    linarith
  have hn0 := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hn0
    have : |lc0 (-θ) (cycleBasis F 0)| = 1 := by simp [cycleBasis, lc0, lf]
    linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin : ¬ |lc0 (-θ) S| < |lc0 (-θ) (cycleBasis F m)| := Nat.find_min hex (by omega)
  rw [hm] at hn0
  obtain ⟨c', d', -, hRP⟩ := rp_seq h hA m
  have hB : cycleBasis F (m + 1) = cycleBasis F m * cycleMat (cycleW (cycleForm F m)) := rfl
  rw [hB, lc0_mul_cycleMat] at hn0
  obtain ⟨ε, hε, hSε⟩ := RP.unique hα hβ hRP hS (not_lt.1 hmin) hn0
  exact ⟨m, ε, hε, hSε⟩

/-! ### Helpers: every reduced pair comes from the sequence -/

theorem act_smul_sign {F : Matrix (Fin 2) (Fin 2) ℝ} (B : Matrix (Fin 2) (Fin 2) ℤ) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) : act (ε • B) F = act B F := by
  rcases hε with rfl | rfl
  · rw [one_smul]
  · unfold act
    rw [neg_smul, one_smul]
    simp [castM, Matrix.map_neg]

theorem cycleForm_pred {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) (m : ℤ) :
    cycleForm F (m - 1) = cyclePrev (cycleForm F m) := by
  have h := cycleForm_succ hG (m - 1)
  rw [sub_add_cancel] at h
  rw [h, (good_cycleForm hG (m - 1)).prev_next]

theorem cycleForm_add {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) (j m : ℤ) :
    cycleForm (cycleForm F j) m = cycleForm F (j + m) := by
  have hG' := good_cycleForm hG j
  induction m using Int.induction_on with
  | zero => simp [cycleForm_zero]
  | succ i ih => rw [cycleForm_succ hG', ih, ← add_assoc, cycleForm_succ hG]
  | pred i ih =>
    rw [cycleForm_pred hG', ih, show j + (-(i : ℤ) - 1) = j + -(i : ℤ) - 1 by ring, cycleForm_pred hG]

theorem lc0_mul (γ : ℝ) (P T : Matrix (Fin 2) (Fin 2) ℤ) :
    lc0 γ (P * T) = T 0 0 * lc0 γ P + T 1 0 * lc1 γ P := by
  simp only [lc0, lc1, lf, Matrix.mul_apply, Fin.sum_univ_two]; push_cast; ring

theorem lc1_mul (γ : ℝ) (P T : Matrix (Fin 2) (Fin 2) ℤ) :
    lc1 γ (P * T) = T 0 1 * lc0 γ P + T 1 1 * lc1 γ P := by
  simp only [lc0, lc1, lf, Matrix.mul_apply, Fin.sum_univ_two]; push_cast; ring

theorem RP.mul {α β θ φ c d : ℝ} {P T : Matrix (Fin 2) (Fin 2) ℤ} (hP : RP α β P θ φ)
    (hT : RP (-θ) φ T c d) : RP α β (P * T) c d ∧ lc0 α (P * T) = lc0 α P * lc0 (-θ) T := by
  obtain ⟨hdP, -, -, -, hU, hV⟩ := hP
  obtain ⟨hdT, hc, hd0, hd1, hU', hV'⟩ := hT
  have k0 : lc0 α (P * T) = lc0 α P * lc0 (-θ) T := by rw [lc0_mul, hU]; simp only [lc0, lf]; ring
  have k1 : lc1 α (P * T) = lc0 α P * lc1 (-θ) T := by rw [lc1_mul, hU]; simp only [lc1, lf]; ring
  have k2 : lc0 β (P * T) = lc0 β P * lc0 φ T := by rw [lc0_mul, hV]; simp only [lc0, lf]; ring
  have k3 : lc1 β (P * T) = lc0 β P * lc1 φ T := by rw [lc1_mul, hV]; simp only [lc1, lf]; ring
  refine ⟨⟨?_, hc, hd0, hd1, ?_, ?_⟩, k0⟩
  · rw [Matrix.det_mul]
    rcases hdP with h | h <;> rcases hdT with h' | h' <;> rw [h, h'] <;> norm_num
  · rw [k1, k0, hU']; ring
  · rw [k3, k2, hV']; ring

/-- Helper: a matrix whose columns form a reduced pair takes `f` to one of the `f_m`. -/
theorem Rd.exists_cycleForm {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F)
    {T : Matrix (Fin 2) (Fin 2) ℤ} {c d : ℝ} (hT : RP (-θ) φ T c d) :
    ∃ m : ℤ, act T F = cycleForm F m := by
  have hG : Good F := ⟨⟨_, _, h⟩, hA⟩
  have hL := hT.lc0_ne (h.nz hA).1
  have hLp : 0 < |lc0 (-θ) T| := abs_pos.2 hL
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 ≤ k * |lc0 (-θ) T| := by
    refine ⟨⌈1 / |lc0 (-θ) T|⌉₊, ?_⟩
    have := Nat.le_ceil (1 / |lc0 (-θ) T|)
    rwa [div_le_iff₀ hLp] at this
  set F' := cycleForm F (-(k : ℤ)) with hF'
  obtain ⟨⟨θ1, φ1, h1⟩, hA1⟩ := good_cycleForm hG (-(k : ℤ))
  have hG1 : Good F' := ⟨⟨_, _, h1⟩, hA1⟩
  obtain ⟨c', d', hR, hRP⟩ := rp_seq h1 hA1 k
  have hback : cycleForm F' k = F := by rw [hF', cycleForm_add hG]; simp [cycleForm_zero]
  rw [hback] at hR
  have hc' : c' = θ := hR.red.1.symm.trans h.red.1
  have hd' : d' = φ := hR.red.2.symm.trans h.red.2
  subst hc' hd'
  obtain ⟨hRP2, hmul⟩ := hRP.mul hT
  have hge := (rp_ge_one h1 hA1 k).1
  have h1le : 1 ≤ |lc0 (-θ1) (cycleBasis F' k * T)| := by
    rw [hmul, abs_mul]; nlinarith [abs_nonneg (lc0 (-θ1) (cycleBasis F' k))]
  obtain ⟨m, ε, hε, hS⟩ := classX h1 hA1 hRP2 h1le
  refine ⟨-(k : ℤ) + m, ?_⟩
  have hspec := (cycleBasis_spec hG1 k).1
  rw [hback] at hspec
  rw [← cycleForm_add hG, ← hF', (cycleBasis_spec hG1 m).1, ← act_smul_sign (cycleBasis F' m) hε, ← hS,
    act_mul, ← hspec]

/-- Helper: `f(T x)` in terms of the values of the two linear factors on the columns of `T`. -/
theorem Rd.val_act_lc {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (T : Matrix (Fin 2) (Fin 2) ℤ)
    (x : Fin 2 → ℝ) : val (act T F) x =
      F 0 0 * (x 0 * lc0 (-θ) T + x 1 * lc1 (-θ) T) * (x 0 * lc0 φ T + x 1 * lc1 φ T) := by
  rw [val_act, h.val_eq]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, castM, lc0, lc1, lf]
  ring

/-- Helper: an integral `T` with `f(T x) = σ f(x)` and `det T = σ` (`σ = ±1`) keeps each linear factor. -/
theorem Rd.rp_of_act {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ)
    {T : Matrix (Fin 2) (Fin 2) ℤ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hdet : T.det = σ)
    (hT : act T F = (σ : ℝ) • F) : RP (-θ) φ T θ φ := by
  have key : ∀ x : Fin 2 → ℝ, F 0 0 * (x 0 * lc0 (-θ) T + x 1 * lc1 (-θ) T) * (x 0 * lc0 φ T + x 1 * lc1 φ T) =
      F 0 0 * (σ * ((x 0 + θ * x 1) * (x 0 - φ * x 1))) := by
    intro x
    rw [← h.val_act_lc, hT]
    simp only [val, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [show x ⬝ᵥ (F *ᵥ x) = val F x from rfl, h.val_eq]; ring
  have ha := h.a_ne
  have e1 : lc0 (-θ) T * lc0 φ T = σ := by
    have := key ![1, 0]; simp at this
    exact mul_left_cancel₀ ha (by linear_combination this)
  have e2 : lc1 (-θ) T * lc1 φ T = -(σ * θ * φ) := by
    have := key ![0, 1]; simp at this
    exact mul_left_cancel₀ ha (by linear_combination this)
  have e3 : (lc0 (-θ) T + lc1 (-θ) T) * (lc0 φ T + lc1 φ T) = σ * ((1 + θ) * (1 - φ)) := by
    have := key ![1, 1]; simp at this
    exact mul_left_cancel₀ ha (by linear_combination this)
  have hS : (σ : ℝ) ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hdet' : (T 0 0 : ℝ) * T 1 1 - T 0 1 * T 1 0 = σ := by
    rw [Matrix.det_fin_two] at hdet; exact_mod_cast hdet
  have D : lc0 (-θ) T * lc1 φ T - lc1 (-θ) T * lc0 φ T = -(θ + φ) * σ := by
    simp only [lc0, lc1, lf]; linear_combination (-(θ + φ)) * hdet'
  have E4 : lc1 (-θ) T * lc0 φ T = σ * θ := by linear_combination (e3 - e1 - e2 - D) / 2
  have E5 : lc0 (-θ) T * lc1 φ T = -(σ * φ) := by linear_combination (e3 - e1 - e2 + D) / 2
  have E1 : lc0 (-θ) T * lc0 φ T = σ := by linear_combination e1
  refine ⟨by rw [hdet]; rcases hσ with rfl | rfl <;> simp, h.one_lt, h.phi_pos, h.phi_lt, ?_, ?_⟩
  · linear_combination (-(lc1 (-θ) T - θ * lc0 (-θ) T)) * hS + (-(σ : ℝ) * lc1 (-θ) T) * E1 +
      ((σ : ℝ) * lc0 (-θ) T) * E4
  · linear_combination (-(lc1 φ T + φ * lc0 φ T)) * hS + (-(σ : ℝ) * lc1 φ T) * E1 +
      ((σ : ℝ) * lc0 φ T) * E5

theorem det_gl (T : GL (Fin 2) ℤ) : T.val.det = 1 ∨ T.val.det = -1 :=
  Int.isUnit_iff.mp (Matrix.isUnits_det_units T)

/-! ### Helpers: negation, signs, determinants -/

theorem redPhi_neg (F : Matrix (Fin 2) (Fin 2) ℝ) : redPhi (-F) = redPhi F := by
  unfold redPhi; simp [neg_div_neg_eq]

theorem redTheta_neg (F : Matrix (Fin 2) (Fin 2) ℝ) : redTheta (-F) = redTheta F := by
  unfold redTheta; simp [neg_div_neg_eq]

theorem act_neg (T : Matrix (Fin 2) (Fin 2) ℤ) (F : Matrix (Fin 2) (Fin 2) ℝ) : act T (-F) = -act T F := by
  unfold act; simp

theorem cycleW_neg (F : Matrix (Fin 2) (Fin 2) ℝ) : cycleW (-F) = cycleW F := by
  unfold cycleW; rw [redPhi_neg]

theorem cycleNext_neg (F : Matrix (Fin 2) (Fin 2) ℝ) : cycleNext (-F) = -cycleNext F := by
  unfold cycleNext; rw [cycleW_neg, act_neg]

theorem cyclePrev_neg (F : Matrix (Fin 2) (Fin 2) ℝ) : cyclePrev (-F) = -cyclePrev F := by
  unfold cyclePrev; rw [redTheta_neg, act_neg]

theorem cycleForm_neg (F : Matrix (Fin 2) (Fin 2) ℝ) (m : ℤ) : cycleForm (-F) m = -cycleForm F m := by
  have hN : ∀ n : ℕ, cycleNext^[n] (-F) = -(cycleNext^[n] F) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, cycleNext_neg]
  have hP : ∀ n : ℕ, cyclePrev^[n] (-F) = -(cyclePrev^[n] F) := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, cyclePrev_neg]
  cases m with
  | ofNat n => exact hN n
  | negSucc n => exact hP (n + 1)

theorem Good.rd {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good G) : Rd G (redTheta G) (redPhi G) := by
  obtain ⟨⟨θ, φ, h⟩, _⟩ := hG
  rw [h.red.1, h.red.2]; exact h

theorem Rd.a_next {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) :
    cycleNext F 0 0 = -(F 0 0 * θ * φ) := by
  unfold cycleNext
  have h1 := h.val_next (cycleW F) ![1, 0]
  rw [val_e0 (isSymm_act h.symm _)] at h1
  simpa using h1

/-- Helper: the leading coefficients `a_m` alternate in sign. -/
theorem sign_cycleForm {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) (n : ℕ) :
    0 < (-1) ^ n * (cycleForm F n 0 0 * F 0 0) := by
  induction n with
  | zero =>
    obtain ⟨⟨θ, φ, h⟩, _⟩ := hG
    simpa [cycleForm_zero] using mul_self_pos.2 h.a_ne
  | succ n ih =>
    obtain ⟨⟨θ, φ, h⟩, _⟩ := good_cycleForm hG n
    have e : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, cycleForm_succ hG, h.a_next, pow_succ]
    have : 0 < θ * φ := mul_pos (by linarith [h.one_lt]) h.phi_pos
    have key : (-1 : ℝ) ^ n * (-1) * (-(cycleForm F n 0 0 * θ * φ) * F 0 0) =
        ((-1) ^ n * (cycleForm F n 0 0 * F 0 0)) * (θ * φ) := by ring
    rw [key]; exact mul_pos ih this

theorem Rd.det_eq {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) :
    F.det = -(F 0 0 ^ 2 * (θ + φ) ^ 2 / 4) := by
  obtain ⟨e1, e2⟩ := h.entries
  rw [Matrix.det_fin_two, h.symm.apply 0 1, e1, e2]; ring

theorem Rd.eq_smul {G F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (hG : Rd G θ φ) (hF : Rd F θ φ) {σ : ℝ}
    (h : G 0 0 = σ * F 0 0) : G = σ • F := by
  obtain ⟨g1, g2⟩ := hG.entries
  obtain ⟨f1, f2⟩ := hF.entries
  have g3 := hG.symm.apply 0 1
  have f3 := hF.symm.apply 0 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [g1, g2, g3, f1, f2, f3, h] <;> ring

theorem det_act_int (T : Matrix (Fin 2) (Fin 2) ℤ) (F : Matrix (Fin 2) (Fin 2) ℝ) :
    (act T F).det = (T.det : ℝ) ^ 2 * F.det := by
  have : (castM T).det = (T.det : ℝ) := by
    simpa [RingHom.mapMatrix_apply] using ((Int.castRingHom ℝ).map_det T).symm
  unfold act
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, this]; ring

/-! ### Helpers: a period of `w_m` is a period of `f_m` up to sign -/

theorem contr_seq {δ : ℕ → ℝ} (hstep : ∀ n, δ n ≠ 0 → |δ (n + 1)| < |δ n|) (hstep' : ∀ n, |δ (n + 1)| ≤ |δ n|)
    {r : ℕ} (hr : 0 < r) (hper : δ r = δ 0) : δ 0 = 0 := by
  by_contra h0
  have : ∀ n, |δ (n + 1)| < |δ 0| := by
    intro n; induction n with
    | zero => exact hstep 0 h0
    | succ k ih => exact lt_of_le_of_lt (hstep' _) ih
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have := this k
  rw [hper] at this
  exact lt_irrefl _ this

theorem expand_seq {ε : ℕ → ℝ} (hstep : ∀ n, ε (n + 1) ≠ 0 → |ε n| < |ε (n + 1)|)
    (hstep' : ∀ n, |ε n| ≤ |ε (n + 1)|) {r : ℕ} (hr : 0 < r) (hper : ε r = ε 0) : ε 0 = 0 := by
  by_contra h0
  have : ∀ n, |ε 0| < |ε (n + 1)| := by
    intro n; induction n with
    | zero =>
      refine hstep 0 (fun h1 => ?_)
      have := hstep' 0
      rw [h1, abs_zero] at this
      exact h0 (abs_nonpos_iff.1 this)
    | succ k ih => exact lt_of_lt_of_le ih (hstep' _)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have := this k
  rw [hper] at this
  exact lt_irrefl _ this

theorem theta_succ {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) (m : ℤ) :
    redTheta (cycleForm F (m + 1)) = cycleSeqW F m + 1 / redTheta (cycleForm F m) := by
  have h := (good_cycleForm hG m)
  rw [cycleForm_succ hG, (h.rd.next h.2).red.1]; rfl

theorem phi_succ {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) (m : ℤ) :
    redPhi (cycleForm F (m + 1)) = 1 / redPhi (cycleForm F m) - cycleSeqW F m := by
  have h := (good_cycleForm hG m)
  rw [cycleForm_succ hG, (h.rd.next h.2).red.2]; rfl

/-- Helper: if the forms have a period `r > 0`, every period `s` of `w_m` gives `f_s = (-1)^s f`. -/
theorem cycleForm_eq_of_period {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) {r : ℕ} (hr : 0 < r)
    (hper : ∀ n : ℤ, cycleForm F (n + r) = cycleForm F n) {s : ℕ}
    (hs : ∀ n : ℤ, cycleSeqW F (n + s) = cycleSeqW F n) :
    cycleForm F s = ((-1 : ℝ) ^ s) • F := by
  set th : ℤ → ℝ := fun m => redTheta (cycleForm F m) with hth
  set ph : ℤ → ℝ := fun m => redPhi (cycleForm F m) with hph
  have hR : ∀ m, Rd (cycleForm F m) (th m) (ph m) := fun m => (good_cycleForm hG m).rd
  have hthp : ∀ n : ℤ, th (n + r) = th n := fun n => by simp only [hth, hper]
  have hphp : ∀ n : ℤ, ph (n + r) = ph n := fun n => by simp only [hph, hper]
  -- θ_s = θ
  have hθ : th s = th 0 := by
    let δ : ℕ → ℝ := fun n => th ((n : ℤ) + s) - th n
    have hrec : ∀ n : ℕ, δ (n + 1) * (th n * th ((n : ℤ) + s)) = -δ n := by
      intro n
      have h1 := theta_succ hG ((n : ℤ) + s)
      have h2 := theta_succ hG (n : ℤ)
      rw [hs] at h1
      have p1 : th n ≠ 0 := by linarith [(hR n).one_lt]
      have p2 : th ((n : ℤ) + s) ≠ 0 := by linarith [(hR ((n : ℤ) + s)).one_lt]
      simp only [δ]
      rw [show ((n + 1 : ℕ) : ℤ) + s = (n : ℤ) + s + 1 by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring]
      simp only [hth] at h1 h2 p1 p2 ⊢
      rw [h1, h2]; field_simp; ring
    have hP : ∀ n : ℕ, 1 < th n * th ((n : ℤ) + s) := fun n => by
      have := (hR n).one_lt; have := (hR ((n : ℤ) + s)).one_lt; nlinarith
    have e : ∀ n, |δ (n + 1)| * (th n * th ((n : ℤ) + s)) = |δ n| := fun n => by
      have := congrArg abs (hrec n)
      rwa [abs_neg, abs_mul, abs_of_pos (lt_trans zero_lt_one (hP n))] at this
    have h0 := contr_seq (δ := δ) (fun n hn => by
        have := e n
        have hpos : 0 < |δ (n + 1)| := by
          rcases (abs_nonneg (δ (n + 1))).lt_or_eq with h | h
          · exact h
          · rw [← h, zero_mul] at this; exact absurd (abs_eq_zero.1 this.symm) hn
        nlinarith [hP n])
      (fun n => by have := e n; nlinarith [hP n, abs_nonneg (δ (n + 1))]) hr (by
        simp only [δ]; have h0 := hthp 0; rw [zero_add] at h0
        rw [add_comm (r : ℤ) (s : ℤ), hthp, h0]; simp)
    simp only [δ] at h0
    simpa using sub_eq_zero.1 h0
  -- φ_s = φ
  have hφ : ph s = ph 0 := by
    let ε : ℕ → ℝ := fun n => ph ((n : ℤ) + s) - ph n
    have hrec : ∀ n : ℕ, ε n * ((cycleSeqW F n + ph ((n : ℤ) + 1 + s)) * (cycleSeqW F n + ph ((n : ℤ) + 1))) =
        -ε (n + 1) := by
      intro n
      have h1 := phi_succ hG ((n : ℤ) + s)
      have h2 := phi_succ hG (n : ℤ)
      rw [hs] at h1
      have p1 : ph n ≠ 0 := (hR n).phi_pos.ne'
      have p2 : ph ((n : ℤ) + s) ≠ 0 := (hR ((n : ℤ) + s)).phi_pos.ne'
      simp only [ε]
      rw [show ((n + 1 : ℕ) : ℤ) + s = (n : ℤ) + s + 1 by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring,
        show (n : ℤ) + 1 + s = (n : ℤ) + s + 1 by ring]
      simp only [hph] at h1 h2 p1 p2 ⊢
      rw [h1, h2]; field_simp; ring
    have hP : ∀ n : ℕ, 1 < (cycleSeqW F n + ph ((n : ℤ) + 1 + s)) * (cycleSeqW F n + ph ((n : ℤ) + 1)) :=
      fun n => by
        have hw : (1 : ℝ) ≤ cycleSeqW F n := by exact_mod_cast (hR n).cycleW_ge
        have := (hR ((n : ℤ) + 1 + s)).phi_pos; have := (hR ((n : ℤ) + 1)).phi_pos; nlinarith
    have e : ∀ n, |ε n| * ((cycleSeqW F n + ph ((n : ℤ) + 1 + s)) * (cycleSeqW F n + ph ((n : ℤ) + 1))) =
        |ε (n + 1)| := fun n => by
      have := congrArg abs (hrec n)
      rwa [abs_neg, abs_mul, abs_of_pos (lt_trans zero_lt_one (hP n))] at this
    have h0 := expand_seq (ε := ε) (fun n hn => by
        have := e n
        have hpos : 0 < |ε n| := by
          rcases (abs_nonneg (ε n)).lt_or_eq with h | h
          · exact h
          · rw [← h, zero_mul] at this; exact absurd (abs_eq_zero.1 this.symm) hn
        nlinarith [hP n])
      (fun n => by have := e n; nlinarith [hP n, abs_nonneg (ε n)]) hr (by
        simp only [ε]; have h0 := hphp 0; rw [zero_add] at h0
        rw [add_comm (r : ℤ) (s : ℤ), hphp, h0]; simp)
    simp only [ε] at h0
    simpa using sub_eq_zero.1 h0
  -- the leading coefficients
  have hRs : Rd (cycleForm F s) (th 0) (ph 0) := by rw [← hθ, ← hφ]; exact hR s
  have hR0 : Rd F (th 0) (ph 0) := hR 0
  have hdet : (cycleForm F s).det = F.det := by
    rw [(cycleBasis_spec hG s).1, det_act_int, (cycleBasis_spec hG s).2]; push_cast
    rw [← pow_mul, mul_comm s 2, pow_mul]; norm_num
  rw [hRs.det_eq, hR0.det_eq] at hdet
  have hpos : 0 < (th 0 + ph 0) ^ 2 := by have := hR0.one_lt; have := hR0.phi_pos; positivity
  have hsq : cycleForm F s 0 0 ^ 2 = F 0 0 ^ 2 := by
    have : cycleForm F s 0 0 ^ 2 * (th 0 + ph 0) ^ 2 = F 0 0 ^ 2 * (th 0 + ph 0) ^ 2 := by linarith
    exact mul_right_cancel₀ hpos.ne' this
  have hsg := sign_cycleForm hG s
  have ha := mul_self_pos.2 hR0.a_ne
  apply hRs.eq_smul hR0
  rcases Nat.even_or_odd s with he | ho
  · rw [he.neg_one_pow] at hsg ⊢
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · rw [h, one_mul]
    · rw [h] at hsg; nlinarith
  · rw [ho.neg_one_pow] at hsg ⊢
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · rw [h] at hsg; nlinarith
    · rw [h]; ring

/-! ### Helpers: integral forms -/

/-- Helper: `G` is the matrix of a classically integral form of determinant `d`. -/
def IntF (d : ℤ) (G : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ p : ℤ × ℤ × ℤ, p.1 * p.2.2 - p.2.1 ^ 2 = d ∧ G = !![(p.1 : ℝ), p.2.1; p.2.1, p.2.2]

theorem IntF.map_act {d : ℤ} {G : Matrix (Fin 2) (Fin 2) ℝ} (h : IntF d G) (T : Matrix (Fin 2) (Fin 2) ℤ)
    (hT : T.det = 1 ∨ T.det = -1) : IntF d (act T G) := by
  obtain ⟨⟨a, b, c⟩, hd, rfl⟩ := h
  refine ⟨(a * T 0 0 ^ 2 + 2 * b * T 0 0 * T 1 0 + c * T 1 0 ^ 2,
    a * T 0 0 * T 0 1 + b * (T 0 0 * T 1 1 + T 0 1 * T 1 0) + c * T 1 0 * T 1 1,
    a * T 0 1 ^ 2 + 2 * b * T 0 1 * T 1 1 + c * T 1 1 ^ 2), ?_, ?_⟩
  · rw [Matrix.det_fin_two] at hT
    simp only at hd ⊢
    have e : (a * T 0 0 ^ 2 + 2 * b * T 0 0 * T 1 0 + c * T 1 0 ^ 2) *
        (a * T 0 1 ^ 2 + 2 * b * T 0 1 * T 1 1 + c * T 1 1 ^ 2) -
        (a * T 0 0 * T 0 1 + b * (T 0 0 * T 1 1 + T 0 1 * T 1 0) + c * T 1 0 * T 1 1) ^ 2 =
        (T 0 0 * T 1 1 - T 0 1 * T 1 0) ^ 2 * (a * c - b ^ 2) := by ring
    rw [e, hd]
    rcases hT with h | h <;> rw [h] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Reduction.act, castM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem intF_cycleForm {F : Matrix (Fin 2) (Fin 2) ℝ} {d : ℤ} (hI : IntF d F) (m : ℤ) :
    IntF d (cycleForm F m) := by
  have hN : ∀ n : ℕ, IntF d (cycleNext^[n] F) := by
    intro n; induction n with
    | zero => exact hI
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.map_act _ (Or.inr (det_cycleMat _))
  have hP : ∀ n : ℕ, IntF d (cyclePrev^[n] F) := by
    intro n; induction n with
    | zero => exact hI
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.map_act _ (Or.inr (by simp [Matrix.det_fin_two_of]))
  cases m with
  | ofNat n => exact hN n
  | negSucc n => exact hP (n + 1)

/-- Helper: the sequence of an integral form is periodic (by Lemma 3.5). -/
theorem exists_form_period {F : Matrix (Fin 2) (Fin 2) ℝ} (hG : Good F) {d : ℤ} (hd : d < 0) (hI : IntF d F) :
    ∃ r : ℕ, 0 < r ∧ ∀ n : ℤ, cycleForm F (n + r) = cycleForm F n := by
  set S := (fun p : ℤ × ℤ × ℤ => !![(p.1 : ℝ), p.2.1; p.2.1, p.2.2]) ''
    {p : ℤ × ℤ × ℤ | p.1 * p.2.2 - p.2.1 ^ 2 = d ∧ IsClassicallyReduced !![(p.1 : ℝ), p.2.1; p.2.1, p.2.2]}
  have hS : S.Finite := (finite_isClassicallyReduced hd).image _
  have hmem : ∀ m : ℕ, cycleForm F m ∈ S := by
    intro m
    obtain ⟨p, hp, he⟩ := intF_cycleForm hI m
    obtain ⟨⟨θ, φ, h⟩, -⟩ := good_cycleForm hG m
    exact ⟨p, ⟨hp, he ▸ h.isClassicallyReduced⟩, he.symm⟩
  obtain ⟨i, j, hij, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem (f := fun m : ℕ => cycleForm F m) hmem hS
  refine ⟨j - i, by omega, fun n => ?_⟩
  have he' : cycleForm F i = cycleForm F j := he
  have e : n + ((j - i : ℕ) : ℤ) = (j : ℤ) + (n - i) := by push_cast [hij.le]; ring
  rw [e, ← cycleForm_add hG, ← he', cycleForm_add hG]
  congr 1; ring

theorem isSymm_cmat (a b c : ℤ) : (!![(a : ℝ), b; b, c]).IsSymm := by
  unfold Matrix.IsSymm; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem aniso_of_cform {a b c : ℤ} (h : ¬ (cform a b c).IsotropicIn ℚ) : Aniso !![(a : ℝ), b; b, c] := by
  intro x hx h0
  apply h
  refine ⟨x, hx, ?_⟩
  rw [evalIn_cform]
  rw [← realMat_cform, val_realMat_cform] at h0
  exact_mod_cast h0

theorem mem_autPlus_cform_iff {a b c : ℤ} (U : GL (Fin 2) ℤ) :
    U ∈ Siegel.AutPlus (cform a b c) ↔ act U.val !![(a : ℝ), b; b, c] = !![(a : ℝ), b; b, c] ∧ U.val.det = 1 := by
  rw [Siegel.mem_autPlus_iff, mem_aut_iff_act, realMat_cform]

/-- Helper: a matrix with integral entries and determinant `±1`, as an element of `GL₂(ℤ)`. -/
noncomputable def toGL (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = 1 ∨ B.det = -1) : GL (Fin 2) ℤ :=
  Matrix.nonsingInvUnit B (Int.isUnit_iff.mpr hB)

theorem toGL_val (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = 1 ∨ B.det = -1) : (toGL B hB).val = B := rfl

/-- Helper: the improper equivalences of `f` with `-f` given by an odd period, and conversely. -/
theorem improper_neg_iff {F : Matrix (Fin 2) (Fin 2) ℝ} {θ φ : ℝ} (h : Rd F θ φ) (hA : Aniso F) {r : ℕ} (hr : 0 < r)
    (hper : ∀ n : ℤ, cycleForm F (n + r) = cycleForm F n) :
    (∃ M : GL (Fin 2) ℤ, M.val.det = -1 ∧ act M.val F = -F) ↔
      ∃ r : ℕ, Odd r ∧ ∀ n : ℤ, cycleSeqW F (n + r) = cycleSeqW F n := by
  have hG : Good F := ⟨⟨_, _, h⟩, hA⟩
  constructor
  · rintro ⟨M, hMdet, hMF⟩
    have hRP := h.rp_of_act (σ := -1) (Or.inr rfl) hMdet (by rw [hMF]; simp)
    obtain ⟨m, hm⟩ := h.exists_cycleForm hA hRP
    rw [hMF] at hm
    have key : ∀ k : ℕ, cycleForm F k = -F → ∃ r : ℕ, Odd r ∧ ∀ n : ℤ, cycleSeqW F (n + r) = cycleSeqW F n := by
      intro k hk
      refine ⟨k, ?_, fun n => ?_⟩
      · rcases Nat.even_or_odd k with he | ho
        · have := sign_cycleForm hG k
          rw [he.neg_one_pow, hk] at this
          simp only [Matrix.neg_apply] at this
          nlinarith [mul_self_pos.2 h.a_ne]
        · exact ho
      · show cycleW (cycleForm F (n + k)) = cycleW (cycleForm F n)
        rw [add_comm, ← cycleForm_add hG, hk, cycleForm_neg, cycleW_neg]
    cases m with
    | ofNat k => exact key k hm.symm
    | negSucc k =>
      apply key (k + 1)
      have h0 : F = cycleForm (cycleForm F (Int.negSucc k)) ((k + 1 : ℕ) : ℤ) := by
        rw [cycleForm_add hG]; simp [Int.negSucc_eq, cycleForm_zero]
      rw [← hm, cycleForm_neg] at h0
      exact neg_eq_iff_eq_neg.mp h0.symm
  · rintro ⟨r', hr'odd, hr'per⟩
    have hF' := cycleForm_eq_of_period hG hr hper hr'per
    rw [hr'odd.neg_one_pow, neg_one_smul] at hF'
    have hdet : (cycleBasis F r').det = -1 := by rw [(cycleBasis_spec hG r').2, hr'odd.neg_one_pow]
    refine ⟨toGL _ (Or.inr hdet), hdet, ?_⟩
    rw [toGL_val, ← (cycleBasis_spec hG r').1, hF']

/-- Helper: an integral matrix (3.14) with $t^2 + du^2 = -1$ is an improper equivalence of `f` with `-f`. -/
theorem anti_of_pellMat {a b c : ℤ} {N : Matrix (Fin 2) (Fin 2) ℤ} {t u : ℝ}
    (hN : castM N = pellMat (a : ℝ) b c t u) (ht : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = -1) :
    N.det = -1 ∧ act N !![(a : ℝ), b; b, c] = -!![(a : ℝ), b; b, c] := by
  constructor
  · have : (castM N).det = (N.det : ℝ) := by
      simpa [RingHom.mapMatrix_apply] using ((Int.castRingHom ℝ).map_det N).symm
    rw [hN, Matrix.det_fin_two] at this
    simp only [pellMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at this
    have h' : (N.det : ℝ) = -1 := by rw [← this]; linear_combination ht
    exact_mod_cast h'
  · unfold act
    rw [hN]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pellMat, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (a : ℝ) * ht
    · linear_combination (b : ℝ) * ht
    · linear_combination (b : ℝ) * ht
    · linear_combination (c : ℝ) * ht

/-- Helper: the entry relations of an improper equivalence of `f` with `-f`. -/
theorem anti_rel {a b c : ℤ} {M : Matrix (Fin 2) (Fin 2) ℤ} (hdet : M.det = -1)
    (hM : act M !![(a : ℝ), b; b, c] = -!![(a : ℝ), b; b, c]) :
    a * (M 1 1 - M 0 0) = 2 * b * M 1 0 ∧ a * M 0 1 = -c * M 1 0 ∧
      M 0 0 * M 1 1 - M 0 1 * M 1 0 = -1 := by
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e11 := congrFun (congrFun hM 1) 1
  simp [act, castM, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  rw [Matrix.det_fin_two] at hdet
  have hd : (M 0 0 : ℝ) * M 1 1 - M 0 1 * M 1 0 = -1 := by exact_mod_cast hdet
  refine ⟨?_, ?_, hdet⟩
  · have : (a : ℝ) * (M 1 1 - M 0 0) = 2 * b * M 1 0 := by
      linear_combination (M 1 1 : ℝ) * e00 - (M 1 0 : ℝ) * e01 - (M 0 0 * a + M 1 0 * b : ℝ) * hd
    exact_mod_cast this
  · have : (a : ℝ) * M 0 1 = -c * M 1 0 := by
      linear_combination (M 0 1 : ℝ) * e00 - (M 0 0 : ℝ) * e01 + (M 0 0 * b + M 1 0 * c : ℝ) * hd
    exact_mod_cast this

/-- **Lemma 3.6, Corollary** (Cassels, Ch. 13, §3, p. 297), corrected: let $f$ be a classically reduced real binary
form without nonzero rational zeros. Every classically reduced form $g(\vec{x}) = f(T\vec{x})$, $T \in GL_2(\mathbb{Z})$,
is $f_m(x, y)$ or $f_m(-y, x)$ for some $m \in \mathbb{Z}$.

*Erratum*: Cassels states that every classically reduced form *properly* equivalent
to $f$ is one of the $f_m$. That is false: $f(-y, x)$ is classically reduced (its roots are $1/\phi$ and $1/\theta$),
properly equivalent to $f$, and in general not among the $f_m$; e.g. for $f = -6x^2 - 8xy + 3y^2$ the sequence has
period $6$ ($w = 3, 3, 1, 1, 1, 1$; forms $-6x^2 - 8xy + 3y^2$, $3x^2 + 10xy - 3y^2$, $-3x^2 - 8xy + 6y^2$,
$6x^2 + 4xy - 5y^2$, $-5x^2 - 6xy + 5y^2$, $5x^2 + 4xy - 6y^2$) and does not contain $3x^2 + 8xy - 6y^2 = f(-y, x)$.
The $f_m(-y, x)$ are the forms whose root $\theta$ belongs to the other linear factor; Cassels' statement holds
exactly when $f$ has an improper integral automorph. Stated for all $T \in GL_2(\mathbb{Z})$ (proper and improper). -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.6, Cor., p. 297"]
theorem mem_cycleForm_of_isClassicallyReduced {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm)
    (hred : IsClassicallyReduced F) (haniso : ∀ x : Fin 2 → ℚ, x ≠ 0 → val F (fun i => (x i : ℝ)) ≠ 0)
    (T : GL (Fin 2) ℤ) (hG : IsClassicallyReduced (act T.val F)) :
    ∃ m : ℤ, act T.val F = cycleForm F m ∨ act T.val F = act !![0, -1; 1, 0] (cycleForm F m) := by
  obtain ⟨θ, φ, h⟩ := rd_of_red hF hred
  have hA : Aniso F := haniso
  obtain ⟨θ', φ', h'⟩ := rd_of_red (isSymm_act hF _) hG
  have hdet := det_gl T
  obtain ⟨hα, hβ⟩ := h.nz hA
  have hL0 : lc0 (-θ) T.val ≠ 0 := fun h0 => by
    obtain ⟨_, _⟩ := hα _ _ h0; rcases col0_ne hdet with h1 | h1 <;> contradiction
  have hM0 : lc0 φ T.val ≠ 0 := fun h0 => by
    obtain ⟨_, _⟩ := hβ _ _ h0; rcases col0_ne hdet with h1 | h1 <;> contradiction
  have hG00 : act T.val F 0 0 = F 0 0 * (lc0 (-θ) T.val * lc0 φ T.val) := by
    have := h.val_act_lc T.val ![1, 0]
    rw [val_e0 (isSymm_act hF _)] at this
    simp at this; linear_combination this
  have hGa : act T.val F 0 0 ≠ 0 := h'.a_ne
  rcases fac_unique hGa (θ := θ') (φ := φ') (θ' := lc1 (-θ) T.val / lc0 (-θ) T.val)
      (φ' := -(lc1 φ T.val / lc0 φ T.val)) (fun x => by
        rw [← h'.val_eq, h.val_act_lc, hG00]; field_simp; ring) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hRP : RP (-θ) φ T.val θ' φ' :=
      ⟨hdet, h'.one_lt, h'.phi_pos, h'.phi_lt, by rw [e1]; field_simp, by rw [e2]; field_simp⟩
    obtain ⟨m, hm⟩ := h.exists_cycleForm hA hRP
    exact ⟨m, Or.inl hm⟩
  · set J : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0] with hJ
    have hJ0 : ∀ γ, lc0 γ (T.val * J) = -lc1 γ T.val := fun γ => by rw [lc0_mul]; simp [J]
    have hJ1 : ∀ γ, lc1 γ (T.val * J) = lc0 γ T.val := fun γ => by rw [lc1_mul]; simp [J]
    have hL1 : lc1 (-θ) T.val ≠ 0 := by
      intro h0; rw [h0] at e2; simp at e2; linarith [h'.phi_pos]
    have hM1 : lc1 φ T.val ≠ 0 := by
      intro h0; rw [h0] at e1; simp at e1; linarith [h'.one_lt]
    have hRP : RP (-θ) φ (T.val * J) (1 / φ') (1 / θ') := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Matrix.det_mul]
        have : J.det = 1 := by simp [J, Matrix.det_fin_two_of]
        rw [this, mul_one]; exact hdet
      · rw [lt_div_iff₀ h'.phi_pos]; linarith [h'.phi_lt]
      · exact one_div_pos.2 (by linarith [h'.one_lt])
      · rw [div_lt_one (by linarith [h'.one_lt])]; exact h'.one_lt
      · rw [hJ0, hJ1, e2]; field_simp
      · rw [hJ0, hJ1, e1]; field_simp
    obtain ⟨m, hm⟩ := h.exists_cycleForm hA hRP
    refine ⟨m, Or.inr ?_⟩
    rw [← hm, ← act_mul, Matrix.mul_assoc]
    have : J * !![0, -1; 1, 0] = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [J]
    rw [this, Matrix.mul_one]

/-- **Lemma 3.7** (Cassels, Ch. 13, §3, p. 298): let $f = ax^2 + 2bxy + cy^2$ be classically integral, indefinite
($ac - b^2 < 0$), anisotropic and classically reduced (every such form is equivalent to a classically reduced one,
Lemma 3.6, which is how Cassels starts the sequence). Then (i) the sequence $w_m$ is periodic; (ii) if $s > 0$ is
the least even period and $T_s = B_s$ (Cassels (3.51): $T_s\vec{a}_0 = \vec{a}_s$, $T_s\vec{a}_1 = \vec{a}_{s+1}$),
the group $O^+(f)$ of proper integral automorphs is generated by $T_s$ and $-I$; (iii) $f$ is improperly equivalent
to $-f$ if and only if the sequence $w_m$ has an odd period. (The display (3.51) is garbled in the machine-read
text.) -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.7, (3.51)–(3.52), p. 298"]
theorem lemma_3_7 {a b c : ℤ} (hind : a * c - b ^ 2 < 0) (haniso : ¬ (cform a b c).IsotropicIn ℚ)
    (hred : IsClassicallyReduced !![(a : ℝ), b; b, c]) :
    (∃ r : ℕ, 0 < r ∧ ∀ n : ℤ, cycleSeqW !![(a : ℝ), b; b, c] (n + r) = cycleSeqW !![(a : ℝ), b; b, c] n) ∧
    (∀ s : ℕ, 0 < s → Even s → (∀ n : ℤ, cycleSeqW !![(a : ℝ), b; b, c] (n + s) = cycleSeqW !![(a : ℝ), b; b, c] n) →
      (∀ s' : ℕ, 0 < s' → s' < s → Even s' →
        ¬ ∀ n : ℤ, cycleSeqW !![(a : ℝ), b; b, c] (n + s') = cycleSeqW !![(a : ℝ), b; b, c] n) →
      ∀ T : GL (Fin 2) ℤ, T.val = cycleBasis !![(a : ℝ), b; b, c] s →
        Subgroup.closure {T, -1} = Siegel.AutPlus (cform a b c)) ∧
    ((∃ M : GL (Fin 2) ℤ, M.val.det = -1 ∧ act M.val !![(a : ℝ), b; b, c] = -!![(a : ℝ), b; b, c]) ↔
      ∃ r : ℕ, Odd r ∧ ∀ n : ℤ, cycleSeqW !![(a : ℝ), b; b, c] (n + r) = cycleSeqW !![(a : ℝ), b; b, c] n) := by
  set F : Matrix (Fin 2) (Fin 2) ℝ := !![(a : ℝ), b; b, c] with hFdef
  have hFs : F.IsSymm := isSymm_cmat a b c
  have hA : Aniso F := aniso_of_cform haniso
  obtain ⟨θ, φ, h⟩ := rd_of_red hFs hred
  have hG : Good F := ⟨⟨θ, φ, h⟩, hA⟩
  have hI : IntF (a * c - b ^ 2) F := ⟨(a, b, c), rfl, rfl⟩
  obtain ⟨r, hr, hper⟩ := exists_form_period hG hind hI
  refine ⟨⟨r, hr, fun n => ?_⟩, ?_, improper_neg_iff h hA hr hper⟩
  · show cycleW (cycleForm F (n + r)) = cycleW (cycleForm F n); rw [hper]
  intro s hs heven hsper hmin T hT
  have hFs' : cycleForm F s = F := by
    rw [cycleForm_eq_of_period hG hr hper hsper, heven.neg_one_pow, one_smul]
  have hdetB : (cycleBasis F s).det = 1 := by rw [(cycleBasis_spec hG s).2, heven.neg_one_pow]
  have hTF : act T.val F = F := by rw [hT, ← (cycleBasis_spec hG s).1, hFs']
  have hTmem : T ∈ Siegel.AutPlus (cform a b c) := (mem_autPlus_cform_iff T).2 ⟨hTF, hT ▸ hdetB⟩
  have rpA : ∀ V ∈ Siegel.AutPlus (cform a b c), RP (-θ) φ V.val θ φ := fun V hV => by
    obtain ⟨h1, h2⟩ := (mem_autPlus_cform_iff V).1 hV
    exact h.rp_of_act (Or.inl rfl) h2 (by rw [h1]; simp [hFdef])
  have gmul : ∀ V ∈ Siegel.AutPlus (cform a b c), ∀ W ∈ Siegel.AutPlus (cform a b c),
      lc0 (-θ) (V * W).val = lc0 (-θ) V.val * lc0 (-θ) W.val := fun V hV W hW => by
    rw [Units.val_mul]; exact ((rpA V hV).mul (rpA W hW)).2
  have g1 : lc0 (-θ) (1 : GL (Fin 2) ℤ).val = 1 := by simp [lc0, lf]
  have hstrict : StrictMono fun n => |lc0 (-θ) (cycleBasis F n)| :=
    strictMono_nat_of_lt_succ fun n => (rp_growth h hA n).1
  have hB0 : |lc0 (-θ) (cycleBasis F 0)| = 1 := by simp [cycleBasis, lc0, lf]
  have hΛ : 1 < |lc0 (-θ) T.val| := by rw [hT, ← hB0]; exact hstrict hs
  have hΛ0 : lc0 (-θ) T.val ≠ 0 := by intro h0; rw [h0, abs_zero] at hΛ; linarith
  have gpow : ∀ ν : ℤ, lc0 (-θ) (T ^ ν).val = lc0 (-θ) T.val ^ ν := by
    have ginv : lc0 (-θ) T⁻¹.val * lc0 (-θ) T.val = 1 := by
      rw [← gmul _ (inv_mem hTmem) _ hTmem, inv_mul_cancel, g1]
    intro ν
    induction ν using Int.induction_on with
    | zero => simpa using g1
    | succ i ih => rw [_root_.zpow_add_one, gmul _ (zpow_mem hTmem _) _ hTmem, ih, zpow_add_one₀ hΛ0]
    | pred i ih =>
      rw [_root_.zpow_sub_one, gmul _ (zpow_mem hTmem _) _ (inv_mem hTmem), ih, zpow_sub_one₀ hΛ0,
        eq_inv_of_mul_eq_one_left ginv]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hTmem
    · exact neg_mem_autPlus (one_mem _)
  intro U hU
  have hU0 : 0 < |lc0 (-θ) U.val| := abs_pos.2 ((rpA U hU).lc0_ne (h.nz hA).1)
  obtain ⟨ν, hν1, hν2⟩ := exists_mem_Ico_zpow hU0 hΛ
  have hmem' : U * T ^ (-ν) ∈ Siegel.AutPlus (cform a b c) := mul_mem hU (zpow_mem hTmem _)
  have hg : |lc0 (-θ) (U * T ^ (-ν)).val| = |lc0 (-θ) U.val| / |lc0 (-θ) T.val| ^ ν := by
    rw [gmul _ hU _ (zpow_mem hTmem _), gpow, abs_mul, abs_zpow, _root_.zpow_neg, div_eq_mul_inv]
  have hΛ0' : |lc0 (-θ) T.val| ≠ 0 := ne_of_gt (by linarith)
  have hpowpos : 0 < |lc0 (-θ) T.val| ^ ν := zpow_pos (by linarith) ν
  have hU1 : 1 ≤ |lc0 (-θ) (U * T ^ (-ν)).val| := by
    rw [hg, le_div_iff₀ hpowpos, one_mul]; exact hν1
  have hU2 : |lc0 (-θ) (U * T ^ (-ν)).val| < |lc0 (-θ) T.val| := by
    rw [hg, div_lt_iff₀ hpowpos]
    calc |lc0 (-θ) U.val| < |lc0 (-θ) T.val| ^ (ν + 1) := hν2
      _ = _ := by rw [zpow_add_one₀ hΛ0']; ring
  obtain ⟨m, ε, hε, hS⟩ := classX h hA (rpA _ hmem') hU1
  have hsm : ∀ B : Matrix (Fin 2) (Fin 2) ℤ, lc0 (-θ) (ε • B) = ε * lc0 (-θ) B := fun B => by
    simp only [lc0, lf, Matrix.smul_apply, smul_eq_mul]; push_cast; ring
  have hlc : |lc0 (-θ) (U * T ^ (-ν)).val| = |lc0 (-θ) (cycleBasis F m)| := by
    rw [hS, hsm, abs_mul]; rcases hε with rfl | rfl <;> simp
  have hms : m < s := hstrict.lt_iff_lt.1 (by
    show |lc0 (-θ) (cycleBasis F m)| < |lc0 (-θ) (cycleBasis F s)|
    rw [← hlc, ← hT]; exact hU2)
  have hFm : cycleForm F m = F := by
    rw [(cycleBasis_spec hG m).1, ← act_smul_sign (cycleBasis F m) hε, ← hS]
    exact ((mem_autPlus_cform_iff _).1 hmem').1
  have hm0 : m = 0 := by
    by_contra hm0
    have hev : Even m := by
      rcases Nat.even_or_odd m with he | ho
      · exact he
      · have := sign_cycleForm hG m
        rw [ho.neg_one_pow, hFm] at this
        nlinarith [mul_self_pos.2 h.a_ne]
    exact hmin m (Nat.pos_of_ne_zero hm0) hms hev (fun n => by
      show cycleW (cycleForm F (n + m)) = cycleW (cycleForm F n)
      rw [add_comm, ← cycleForm_add hG, hFm])
  subst hm0
  have hU' : U * T ^ (-ν) = 1 ∨ U * T ^ (-ν) = -1 := by
    rcases hε with rfl | rfl
    · left; ext1; rw [hS]; simp [cycleBasis]
    · right; ext1; rw [hS]; simp [cycleBasis]
  have hUeq : U = (U * T ^ (-ν)) * T ^ ν := by
    rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rw [hUeq]
  refine mul_mem ?_ (zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) _)
  rcases hU' with h1 | h1 <;> rw [h1]
  · exact one_mem _
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- **Lemma 3.7, Corollary, properly primitive case** (Cassels, Ch. 13, §3, p. 298): let $f = ax^2 + 2bxy + cy^2$ be
properly primitive ($\gcd(a, 2b, c) = 1$), indefinite with determinant $d = ac - b^2 < 0$, anisotropic and
classically reduced. Pell's equation with $-1$, $t^2 + du^2 = -1$ (3.25), has an integral solution if and only if the
sequence $w_m$ has an odd period. -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.7, Cor., p. 298 (properly primitive)"]
theorem pell_neg_iff_odd_period_proper {a b c : ℤ} (hpp : Int.gcd a (Int.gcd (2 * b) c) = 1)
    (hind : a * c - b ^ 2 < 0) (haniso : ¬ (cform a b c).IsotropicIn ℚ)
    (hred : IsClassicallyReduced !![(a : ℝ), b; b, c]) :
    (∃ t u : ℤ, t ^ 2 + (a * c - b ^ 2) * u ^ 2 = -1) ↔
      ∃ r : ℕ, Odd r ∧ ∀ n : ℤ, cycleSeqW !![(a : ℝ), b; b, c] (n + r) = cycleSeqW !![(a : ℝ), b; b, c] n := by
  have hFs := isSymm_cmat a b c
  have hA := aniso_of_cform haniso
  obtain ⟨θ, φ, h⟩ := rd_of_red hFs hred
  have hG : Good !![(a : ℝ), b; b, c] := ⟨⟨θ, φ, h⟩, hA⟩
  obtain ⟨r, hr, hper⟩ := exists_form_period hG hind ⟨(a, b, c), rfl, rfl⟩
  rw [← improper_neg_iff h hA hr hper]
  have ha := ne_zero_a_of_aniso haniso
  constructor
  · rintro ⟨t, u, ht⟩
    have ht' : (t : ℝ) ^ 2 + (a * c - b ^ 2) * (u : ℝ) ^ 2 = -1 := by exact_mod_cast ht
    have hN : castM (pellMat a b c t u) = pellMat (a : ℝ) b c t u := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [pellMat, castM]
    obtain ⟨hd, hact⟩ := anti_of_pellMat hN ht'
    exact ⟨toGL _ (Or.inr hd), hd, hact⟩
  · rintro ⟨M, hMdet, hMF⟩
    obtain ⟨r1, r2, hd⟩ := anti_rel hMdet hMF
    have hdvd : a ∣ M.val 1 0 := by
      refine dvd_of_gcd3 hpp ?_ ?_
      · exact ⟨M.val 1 1 - M.val 0 0, by linarith⟩
      · exact ⟨-M.val 0 1, by linarith⟩
    obtain ⟨u, hu⟩ := hdvd
    have hq : M.val 0 1 = -c * u := by apply mul_left_cancel₀ ha; rw [r2, hu]; ring
    have hs : M.val 1 1 - M.val 0 0 = 2 * b * u := by apply mul_left_cancel₀ ha; rw [r1, hu]; ring
    refine ⟨M.val 0 0 + b * u, u, ?_⟩
    rw [hu, hq] at hd
    linear_combination hd - M.val 0 0 * hs

/-- **Lemma 3.7, Corollary, improperly primitive case** (Cassels, Ch. 13, §3, p. 298): let $f = ax^2 + 2bxy + cy^2$ be
primitive and improperly primitive ($a, c$ even, $b$ odd), indefinite with determinant $d = ac - b^2 < 0$,
anisotropic and classically reduced. Pell's equation with $-1$, $t^2 + du^2 = -1$ (3.25), has a solution with
$2t, 2u, t - u \in \mathbb{Z}$ (the integrality conditions (3.15'') of Theorem 3.1) if and only if the sequence $w_m$
has an odd period. -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.7, Cor., p. 298 (improperly primitive)"]
theorem pell_neg_iff_odd_period_improper {a b c : ℤ} (hprim : Int.gcd a (Int.gcd b c) = 1)
    (ha : Even a) (hc : Even c) (hb : Odd b) (hind : a * c - b ^ 2 < 0) (haniso : ¬ (cform a b c).IsotropicIn ℚ)
    (hred : IsClassicallyReduced !![(a : ℝ), b; b, c]) :
    (∃ t u : ℚ, t ^ 2 + (a * c - b ^ 2) * u ^ 2 = -1 ∧ (∃ k : ℤ, 2 * t = k) ∧ (∃ k : ℤ, 2 * u = k) ∧
        (∃ k : ℤ, t - u = k)) ↔
      ∃ r : ℕ, Odd r ∧ ∀ n : ℤ, cycleSeqW !![(a : ℝ), b; b, c] (n + r) = cycleSeqW !![(a : ℝ), b; b, c] n := by
  have hFs := isSymm_cmat a b c
  have hA := aniso_of_cform haniso
  obtain ⟨θ, φ, h⟩ := rd_of_red hFs hred
  have hG : Good !![(a : ℝ), b; b, c] := ⟨⟨θ, φ, h⟩, hA⟩
  obtain ⟨r, hr, hper⟩ := exists_form_period hG hind ⟨(a, b, c), rfl, rfl⟩
  rw [← improper_neg_iff h hA hr hper]
  have ha0 := ne_zero_a_of_aniso haniso
  have ha0' : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
  constructor
  · rintro ⟨t, u, ht, -, ⟨k, hk⟩, ⟨l, hl⟩⟩
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨c', hc'⟩ := hc
    obtain ⟨β, hβ⟩ := hb
    have hu : ((u : ℚ) : ℝ) = (k : ℝ) / 2 := by
      have : (u : ℚ) = k / 2 := by linarith
      rw [this]; push_cast; ring
    have htu : ((t : ℚ) : ℝ) = l + (k : ℝ) / 2 := by
      have : (t : ℚ) = l + k / 2 := by linarith
      rw [this]; push_cast; ring
    have ht' : ((t : ℚ) : ℝ) ^ 2 + (a * c - b ^ 2) * ((u : ℚ) : ℝ) ^ 2 = -1 := by
      have := congrArg (fun q : ℚ => (q : ℝ)) ht; push_cast at this ⊢; linear_combination this
    have hN : castM !![l - β * k, -c' * k; a' * k, l + (β + 1) * k] =
        pellMat (a : ℝ) b c ((t : ℚ) : ℝ) ((u : ℚ) : ℝ) := by
      rw [hu, htu, ha', hc', hβ]
      ext i j; fin_cases i <;> fin_cases j <;> simp [pellMat, castM] <;> ring
    obtain ⟨hd, hact⟩ := anti_of_pellMat hN ht'
    exact ⟨toGL _ (Or.inr hd), hd, hact⟩
  · rintro ⟨M, hMdet, hMF⟩
    obtain ⟨r1, r2, hd⟩ := anti_rel hMdet hMF
    have hdvd : a ∣ 2 * M.val 1 0 := by
      refine dvd_of_gcd3 hprim ?_ ?_
      · exact ⟨M.val 1 1 - M.val 0 0, by linarith⟩
      · exact ⟨-2 * M.val 0 1, by linarith⟩
    obtain ⟨k, hk⟩ := hdvd
    have hs : M.val 1 1 - M.val 0 0 = b * k := by
      apply mul_left_cancel₀ ha0
      have : a * (b * k) = b * (a * k) := by ring
      rw [r1, this, ← hk]; ring
    have hq : 2 * M.val 0 1 = -c * k := by
      apply mul_left_cancel₀ ha0
      have : a * (-c * k) = -c * (a * k) := by ring
      rw [this, ← hk]; linear_combination 2 * r2
    obtain ⟨β, hβ⟩ := hb
    have hpar : M.val 0 0 + M.val 1 1 - k = 2 * (β * k + M.val 0 0) := by
      rw [hβ] at hs; linarith
    have hs' : (M.val 1 1 : ℚ) - M.val 0 0 = b * k := by exact_mod_cast hs
    have hq' : 2 * (M.val 0 1 : ℚ) = -c * k := by exact_mod_cast hq
    have hk' : 2 * (M.val 1 0 : ℚ) = a * k := by exact_mod_cast hk
    have hd' : (M.val 0 0 : ℚ) * M.val 1 1 - M.val 0 1 * M.val 1 0 = -1 := by exact_mod_cast hd
    refine ⟨((M.val 0 0 : ℚ) + M.val 1 1) / 2, (k : ℚ) / 2, ?_, ⟨M.val 0 0 + M.val 1 1, by push_cast; ring⟩,
      ⟨k, by ring⟩, ⟨β * k + M.val 0 0, ?_⟩⟩
    · linear_combination hd' + (((M.val 1 1 : ℚ) - M.val 0 0 + b * k) / 4) * hs' +
        ((M.val 1 0 : ℚ) / 2) * hq' - ((c : ℚ) * k / 4) * hk'
    · have : ((M.val 0 0 + M.val 1 1 - k : ℤ) : ℚ) = 2 * ((β * k + M.val 0 0 : ℤ) : ℚ) := by
        exact_mod_cast hpar
      push_cast at this ⊢
      linarith

end QuadFormsKB.Reduction
