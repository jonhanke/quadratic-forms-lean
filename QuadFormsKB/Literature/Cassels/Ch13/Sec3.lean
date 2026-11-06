/-
# Cassels, Chapter 13, §3: automorphs of binary forms

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §3, *Binary forms*, pp. 289–293: real automorphs
of indefinite binary forms (Lemma 3.1), isotropic forms (Lemma 3.2), the proper integral automorphs of an anisotropic
form and Pell's equation (Theorem 3.1 and Corollary, (3.13)–(3.24)), bounded representatives of orbits of
representations (Lemma 3.3 and Corollaries 1, 2) and the example $a^2 - 82b^2 = 2$ (p. 293).

**Conventions.** Cassels writes a binary form as $f(x, y) = ax^2 + 2bxy + cy^2$ (3.5) with matrix
$F = \begin{pmatrix} a & b \\ b & c\end{pmatrix}$ (3.6) and determinant $d = ac - b^2$ (3.7); in this section $f$ is
*classically integral*, $a, b, c \in \mathbb{Z}$ (3.8). Here that form is `cform a b c` $=$ `BinQF.mk a (2 * b) c`
(the library's `BinQF` has middle coefficient $2b$). Variables are $\vec{x} = (x_0, x_1)$ (Cassels' $(x, y)$).
Integral automorphs: `Siegel.Aut`, proper ones `Siegel.AutPlus` ($\det = 1$, Cassels' $O^+(f)$). Real automorphs of a
real form with matrix $F$: `realAut F` ($S^{\mathsf T}FS = F$). $D = -d = b^2 - ac$ (3.21).
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic
import QuadFormsKB.Siegel.KneserCert

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- Helper: the matrix `t I + u N` of a binary form with matrix `[[α, β], [β, γ]]`. -/
def binM (α β γ t u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![t - β * u, -γ * u; α * u, t + β * u]

/-- Helper: product of two matrices `t I + u N`. -/
theorem binM_mul (α β γ t u t' u' : ℝ) :
    binM α β γ t u * binM α β γ t' u' =
      binM α β γ (t * t' + (β ^ 2 - α * γ) * u * u') (t * u' + t' * u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Helper: `binM 1 0 = 1`. -/
theorem binM_one (α β γ : ℝ) : binM α β γ 1 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [binM]

/-- Helper: determinant of `t I + u N`. -/
theorem binM_det (α β γ t u : ℝ) :
    (binM α β γ t u).det = t ^ 2 + (α * γ - β ^ 2) * u ^ 2 := by
  rw [Matrix.det_fin_two]; simp [binM]; ring

/-- Helper: `t I + u N` is a proper real automorph when `t² - D u² = 1`. -/
theorem binM_aut (α β γ t u : ℝ) (ht : t ^ 2 + (α * γ - β ^ 2) * u ^ 2 = 1) :
    (binM α β γ t u)ᵀ * !![α, β; β, γ] * binM α β γ t u = !![α, β; β, γ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    first
    | linear_combination α * ht
    | linear_combination β * ht
    | linear_combination γ * ht

/-- Helper: `t` and `u` are determined by `t I + u N`. -/
theorem binM_inj {α β γ t u t' u' : ℝ} (hdet : α * γ - β ^ 2 < 0)
    (h : binM α β γ t u = binM α β γ t' u') : t = t' ∧ u = u' := by
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h10 := congrFun (congrFun h 1) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [binM] at h00 h11 h10 h01
  have ht : t = t' := by linarith
  refine ⟨ht, ?_⟩
  subst ht
  by_contra hu
  have hu' : u - u' ≠ 0 := sub_ne_zero.mpr hu
  have ha : α = 0 := h10.resolve_left hu
  have hg : γ = 0 := h01.resolve_left hu
  have h3 : β * (u - u') = 0 := by linarith
  have hb : β = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hu'
  rw [ha, hg, hb] at hdet
  norm_num at hdet

/-- Helper: relations among the entries of a real proper automorph. -/
theorem real_rel (α β γ p q r s : ℝ) (e1 : α * p ^ 2 + 2 * β * p * r + γ * r ^ 2 = α)
    (e2 : α * q ^ 2 + 2 * β * q * s + γ * s ^ 2 = γ)
    (e3 : α * p * q + β * (p * s + q * r) + γ * r * s = β)
    (hd : p * s - q * r = 1) :
    α * (s - p) = 2 * β * r ∧ α * q = -γ * r ∧ γ * (s - p) = -2 * β * q := by
  refine ⟨?_, ?_, ?_⟩
  · grind
  · grind
  · grind

/-- Helper: an improper real automorph has trace zero. -/
theorem tr_zero (α β γ p q r s : ℝ) (hdet : α * γ - β ^ 2 < 0)
    (e1 : α * p ^ 2 + 2 * β * p * r + γ * r ^ 2 = α)
    (e2 : α * q ^ 2 + 2 * β * q * s + γ * s ^ 2 = γ)
    (e3 : α * p * q + β * (p * s + q * r) + γ * r * s = β)
    (hd : p * s - q * r = -1) : p + s = 0 := by
  have h1 : α * (p + s) = 0 := by grind
  have h2 : β * (p + s) = 0 := by grind
  have h3 : γ * (p + s) = 0 := by grind
  by_contra hc
  have ha : α = 0 := (mul_eq_zero.mp h1).resolve_right hc
  have hb : β = 0 := (mul_eq_zero.mp h2).resolve_right hc
  have hg : γ = 0 := (mul_eq_zero.mp h3).resolve_right hc
  rw [ha, hb, hg] at hdet
  norm_num at hdet

/-- Helper: improper real automorphs of a binary form square to `1`. -/
theorem improper_sq (α β γ : ℝ) (hdet : α * γ - β ^ 2 < 0) (S : GL (Fin 2) ℝ)
    (hS : S ∈ realAut !![α, β; β, γ]) (hd : S.val.det = -1) : S * S = 1 := by
  have hS' : S.valᵀ * !![α, β; β, γ] * S.val = !![α, β; β, γ] := hS
  have e11 := congrFun (congrFun hS' 0) 0
  have e12 := congrFun (congrFun hS' 0) 1
  have e22 := congrFun (congrFun hS' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at e11 e12 e22
  rw [Matrix.det_fin_two] at hd
  have ht := tr_zero α β γ (S.val 0 0) (S.val 0 1) (S.val 1 0) (S.val 1 1) hdet
    (by linear_combination e11) (by linear_combination e22) (by linear_combination e12)
    (by linear_combination hd)
  have hs : S.val 1 1 = -S.val 0 0 := by linarith
  have hd2 : S.val 0 0 * S.val 0 0 + S.val 0 1 * S.val 1 0 = 1 := by
    rw [hs] at hd; linarith
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs] <;> linarith

/-- Helper: the reflection matrix attached to a vector `v` with `κ f(v) = 1`. -/
def reflM (α β γ v0 v1 κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - 2 * v0 * (α * v0 + β * v1) * κ, -2 * v0 * (β * v0 + γ * v1) * κ;
    -2 * v1 * (α * v0 + β * v1) * κ, 1 - 2 * v1 * (β * v0 + γ * v1) * κ]

/-- Helper: the reflection matrix is an improper automorph squaring to `1`. -/
theorem reflM_aut (α β γ v0 v1 κ : ℝ)
    (hκ : κ * (v0 * (α * v0 + β * v1) + v1 * (β * v0 + γ * v1)) = 1) :
    (reflM α β γ v0 v1 κ)ᵀ * !![α, β; β, γ] * reflM α β γ v0 v1 κ = !![α, β; β, γ] ∧
      reflM α β γ v0 v1 κ * reflM α β γ v0 v1 κ = 1 ∧ (reflM α β γ v0 v1 κ).det = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> grind
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [reflM, Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · rw [Matrix.det_fin_two]; simp [reflM]; grind

/-- Helper: an improper real automorph exists. -/
theorem exists_improper (α β γ : ℝ) (hdet : α * γ - β ^ 2 < 0) :
    ∃ S ∈ realAut !![α, β; β, γ], S.val.det = -1 := by
  have : ∃ v0 v1 : ℝ, v0 * (α * v0 + β * v1) + v1 * (β * v0 + γ * v1) ≠ 0 := by
    by_contra hc
    push Not at hc
    have h1 := hc 1 0
    have h2 := hc 0 1
    have h3 := hc 1 1
    have : α = 0 := by linarith
    have : γ = 0 := by linarith
    have : β = 0 := by nlinarith
    nlinarith
  obtain ⟨v0, v1, hk0⟩ := this
  obtain ⟨h1, h2, h3⟩ := reflM_aut α β γ v0 v1 _ (inv_mul_cancel₀ hk0)
  exact ⟨⟨reflM α β γ v0 v1 _, reflM α β γ v0 v1 _, h2, h2⟩, h1, h3⟩

/-- Helper: `O⁺_ℝ(f) ≅ ℝˣ` for an explicit indefinite binary form. -/
theorem realAutPlus_equiv (α β γ : ℝ) (hdet : α * γ - β ^ 2 < 0) :
    Nonempty (realAutPlus !![α, β; β, γ] ≃* ℝˣ) := by
  have hD : 0 < β ^ 2 - α * γ := by linarith
  have hD' : β ^ 2 - α * γ ≠ 0 := hD.ne'
  obtain ⟨δ, hδ, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * δ = β ^ 2 - α * γ :=
    ⟨√(β ^ 2 - α * γ), Real.sqrt_pos.mpr hD, Real.mul_self_sqrt hD.le⟩
  let tR : ℝ → ℝ := fun x => (x + x⁻¹) / 2
  let uR : ℝ → ℝ := fun x => (x - x⁻¹) / (2 * δ)
  have hpell : ∀ x : ℝ, x ≠ 0 → tR x ^ 2 + (α * γ - β ^ 2) * uR x ^ 2 = 1 := by
    intro x hx
    simp only [tR, uR]
    field_simp
    grind
  have hmul_t : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 →
      tR (x * y) = tR x * tR y + (β ^ 2 - α * γ) * uR x * uR y := by
    intro x y hx hy
    simp only [tR, uR]
    field_simp
    grind
  have hmul_u : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → uR (x * y) = tR x * uR y + tR y * uR x := by
    intro x y hx hy
    simp only [tR, uR]
    field_simp
    ring
  have hrec : ∀ x : ℝ, x ≠ 0 → x = tR x + δ * uR x := by
    intro x hx
    simp only [tR, uR]
    field_simp
    ring
  have hone_t : tR 1 = 1 := by simp [tR]
  have hone_u : uR 1 = 0 := by simp [uR]
  have hinv : ∀ ε : ℝˣ, binM α β γ (tR ε) (uR ε) * binM α β γ (tR ε) (-uR ε) = 1 := by
    intro ε
    rw [binM_mul]
    have h1 : tR ε * tR ε + (β ^ 2 - α * γ) * uR ε * -uR ε = 1 := by
      linear_combination hpell ε ε.ne_zero
    have h2 : tR ε * -uR ε + tR ε * uR ε = 0 := by ring
    rw [h1, h2, binM_one]
  have hinv' : ∀ ε : ℝˣ, binM α β γ (tR ε) (-uR ε) * binM α β γ (tR ε) (uR ε) = 1 := by
    intro ε
    rw [binM_mul]
    have h1 : tR ε * tR ε + (β ^ 2 - α * γ) * -uR ε * uR ε = 1 := by
      linear_combination hpell ε ε.ne_zero
    have h2 : tR ε * uR ε + tR ε * -uR ε = 0 := by ring
    rw [h1, h2, binM_one]
  let M : ℝˣ → GL (Fin 2) ℝ := fun ε =>
    ⟨binM α β γ (tR ε) (uR ε), binM α β γ (tR ε) (-uR ε), hinv ε, hinv' ε⟩
  let φ0 : ℝˣ →* GL (Fin 2) ℝ :=
    { toFun := M
      map_one' := by
        apply Units.ext
        show binM α β γ (tR ((1 : ℝˣ) : ℝ)) (uR ((1 : ℝˣ) : ℝ)) = 1
        rw [Units.val_one, hone_t, hone_u, binM_one]
      map_mul' := by
        intro ε ε'
        apply Units.ext
        show binM α β γ (tR ((ε * ε' : ℝˣ) : ℝ)) (uR ((ε * ε' : ℝˣ) : ℝ)) =
          binM α β γ (tR ε) (uR ε) * binM α β γ (tR ε') (uR ε')
        rw [binM_mul, Units.val_mul, hmul_t _ _ ε.ne_zero ε'.ne_zero, hmul_u _ _ ε.ne_zero ε'.ne_zero]
        }
  have hmem : ∀ ε, φ0 ε ∈ realAutPlus !![α, β; β, γ] := by
    intro ε
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact binM_aut α β γ _ _ (hpell ε ε.ne_zero)
    · rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact (binM_det α β γ _ _).trans (hpell ε ε.ne_zero)
  let φ := φ0.codRestrict (realAutPlus !![α, β; β, γ]) hmem
  refine ⟨(MulEquiv.ofBijective φ ⟨?_, ?_⟩).symm⟩
  · intro ε ε' h
    have h1 : binM α β γ (tR ε) (uR ε) = binM α β γ (tR ε') (uR ε') := by
      have := congrArg (fun g : realAutPlus !![α, β; β, γ] => (g : GL (Fin 2) ℝ).val) h
      exact this
    obtain ⟨ht, hu⟩ := binM_inj hdet h1
    apply Units.ext
    rw [hrec _ ε.ne_zero, hrec _ ε'.ne_zero, ht, hu]
  · rintro ⟨T, hT⟩
    obtain ⟨hT1, hT2⟩ := Subgroup.mem_inf.mp hT
    have hT1' : T.valᵀ * !![α, β; β, γ] * T.val = !![α, β; β, γ] := hT1
    have hdT : T.val.det = 1 := by
      have := (MonoidHom.mem_ker.mp hT2)
      have h2 := congrArg Units.val this
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2
    have e11 := congrFun (congrFun hT1' 0) 0
    have e12 := congrFun (congrFun hT1' 0) 1
    have e22 := congrFun (congrFun hT1' 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at e11 e12 e22
    have hdT' := hdT
    rw [Matrix.det_fin_two] at hdT'
    obtain ⟨r1, r2, r3⟩ := real_rel α β γ (T.val 0 0) (T.val 0 1) (T.val 1 0) (T.val 1 1)
      (by linear_combination e11) (by linear_combination e22) (by linear_combination e12)
      (by linear_combination hdT')
    set t : ℝ := (T.val 0 0 + T.val 1 1) / 2 with ht
    set u : ℝ := (α * T.val 0 1 - γ * T.val 1 0 - β * (T.val 0 0 - T.val 1 1)) /
      (2 * (β ^ 2 - α * γ)) with hu
    have hTM : T.val = binM α β γ t u := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [binM, ht, hu] <;> field_simp <;> grind
    have hpT : t ^ 2 + (α * γ - β ^ 2) * u ^ 2 = 1 := by
      rw [← binM_det, ← hTM]; exact hdT
    have hprod : (t + δ * u) * (t - δ * u) = 1 := by
      linear_combination hpT + (-(u ^ 2)) * hδ2
    have hne : t + δ * u ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
    refine ⟨Units.mk0 (t + δ * u) hne, ?_⟩
    apply Subtype.ext
    apply Units.ext
    show binM α β γ (tR (t + δ * u)) (uR (t + δ * u)) = T.val
    have hinvE : (t + δ * u)⁻¹ = t - δ * u := inv_eq_of_mul_eq_one_right hprod
    have h1 : tR (t + δ * u) = t := by simp only [tR]; rw [hinvE]; ring
    have h2 : uR (t + δ * u) = u := by
      simp only [uR]; rw [hinvE]; field_simp; ring
    rw [h1, h2, hTM]

/-- **Lemma 3.1** (Cassels, Ch. 13, §3, p. 289): the group $O^+_{\mathbb{R}}(f)$ of real proper automorphs of an
indefinite binary form is isomorphic to the multiplicative group $\mathbb{R}^{\times}$ of the non-zero reals; improper
real automorphs exist, and they all have order $2$. A real binary form ($F$ symmetric) is regular and indefinite iff
$\det F < 0$. -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.1, p. 289"]
theorem binary_realAut {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (hdet : F.det < 0) :
    Nonempty (realAutPlus F ≃* ℝˣ) ∧ (∃ S ∈ realAut F, S.val.det = -1) ∧
      ∀ S ∈ realAut F, S.val.det = -1 → S * S = 1 := by
  obtain ⟨α, β, γ, rfl⟩ : ∃ α β γ : ℝ, F = !![α, β; β, γ] := by
    refine ⟨F 0 0, F 0 1, F 1 1, ?_⟩
    have h10 := hF.apply 0 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10]
  have hd' : α * γ - β ^ 2 < 0 := by
    rw [Matrix.det_fin_two_of] at hdet; linarith
  exact ⟨realAutPlus_equiv α β γ hd', exists_improper α β γ hd', fun S hS hd => improper_sq α β γ hd' S hS hd⟩

/-! ### Classically integral binary forms -/

/-- **Cassels' binary form** $f(x, y) = ax^2 + 2bxy + cy^2$ (Ch. 13, (3.5), p. 290), classically integral
($a, b, c \in \mathbb{Z}$, (3.8)), as an integral form: `BinQF.mk a (2 * b) c`. Its real matrix is
$\begin{pmatrix} a & b \\ b & c\end{pmatrix}$ (`realMat_cform`). -/
@[kb "cassels1978" "Ch. 13, §3, (3.5)–(3.8), p. 290 (as an integral form; the polynomial function is Cassels.Ch13.binF)"]
def cform (a b c : ℤ) : BinQF := BinQF.mk a (2 * b) c

/-- The real matrix of `cform a b c` is $\begin{pmatrix} a & b \\ b & c\end{pmatrix}$ ((3.6)). -/
theorem realMat_cform (a b c : ℤ) : realMat (cform a b c) = !![(a : ℝ), b; b, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cform, QuadForm.hessian, BinQF.mk, QuadForm.ofUpper] <;> ring

/-- $f(x_0, x_1) = ax_0^2 + 2bx_0x_1 + cx_1^2$ for `cform a b c`. -/
theorem eval_cform (a b c : ℤ) (x : Fin 2 → ℤ) :
    QuadForm.eval (cform a b c) x = a * x 0 ^ 2 + 2 * b * x 0 * x 1 + c * x 1 ^ 2 := by
  simp [cform, QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, BinQF.mk, QuadForm.ofUpper]
  ring

/-- Helper: `cform` evaluated over any commutative ring `K`. -/
theorem evalIn_cform (K : Type*) [CommRing K] (a b c : ℤ) (x : Fin 2 → K) :
    (cform a b c).evalIn K x = a * x 0 ^ 2 + 2 * b * x 0 * x 1 + c * x 1 ^ 2 := by
  simp [cform, QuadForm.evalIn, Fin.sum_univ_two, BinQF.mk, QuadForm.ofUpper]
  ring

/-- Helper: `val` of the real matrix of `cform`. -/
theorem val_realMat_cform (a b c : ℤ) (x : Fin 2 → ℝ) :
    val (realMat (cform a b c)) x = a * x 0 ^ 2 + 2 * b * x 0 * x 1 + c * x 1 ^ 2 := by
  rw [← QuadForm.evalIn_real_eq_val, evalIn_cform]

/-- Helper: a binary form evaluated over any commutative ring. -/
theorem binqf_evalIn (K : Type*) [CommRing K] (f : BinQF) (x : Fin 2 → K) :
    f.evalIn K x = (f.a : K) * x 0 ^ 2 + (f.b : K) * x 0 * x 1 + (f.c : K) * x 1 ^ 2 := by
  have h10 : f.coeff 1 0 = 0 := f.upper (show id 0 < id 1 by decide)
  simp [QuadForm.evalIn, Fin.sum_univ_two, BinQF.a, BinQF.b, BinQF.c]
  ring

/-- Helper: entry relations of an automorph of the binary form `(A, B, C)`. -/
theorem binqf_rel (A B C p q r s : ℤ) (e1 : A * p ^ 2 + B * p * r + C * r ^ 2 = A)
    (e2 : A * q ^ 2 + B * q * s + C * s ^ 2 = C)
    (e3 : A * (p + q) ^ 2 + B * (p + q) * (r + s) + C * (r + s) ^ 2 = A + B + C)
    (hd : p * s - q * r = 1) :
    A * (s - p) = B * r ∧ A * q = -C * r ∧ C * (s - p) = -B * q := by
  have e3' : 2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s = B := by
    linear_combination e3 - e1 - e2
  refine ⟨?_, ?_, ?_⟩
  · grind
  · grind
  · grind

/-- Helper: the integral core of Lemma 3.2 (i): the relations force `T = ±I`. -/
theorem pm_core (A B C M p q r s : ℤ) (hM0 : M ≠ 0) (hM : B ^ 2 - 4 * A * C = M ^ 2)
    (rel1 : A * (s - p) = B * r) (rel2 : A * q = -C * r) (rel3 : C * (s - p) = -B * q)
    (hd : p * s - q * r = 1) : q = 0 ∧ r = 0 ∧ s = p ∧ (p = 1 ∨ p = -1) := by
  by_cases hA : A = 0
  · subst hA
    have hB : B ≠ 0 := by
      intro h0; rw [h0] at hM; apply hM0; nlinarith
    have hr : r = 0 := by
      have : B * r = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hB
      · exact h
    subst hr
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' (by linarith : p * s = 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      have : B * q = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hB
      · exact ⟨h, rfl, rfl, Or.inl rfl⟩
    · subst h1; subst h2
      have : B * q = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hB
      · exact ⟨h, rfl, rfl, Or.inr rfl⟩
  · have key : (M * r) ^ 2 = A ^ 2 * ((p + s) ^ 2 - 4) := by grind
    have hdvd : A ∣ M * r := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨(p + s) ^ 2 - 4, key⟩
    obtain ⟨w, hw⟩ := hdvd
    have hw2 : (p + s) ^ 2 - 4 = w ^ 2 := by
      have hA2 : A ^ 2 ≠ 0 := pow_ne_zero 2 hA
      apply mul_left_cancel₀ hA2
      rw [← key, hw]; ring
    generalize hT : p + s = tr at hw2
    have hlt : |w| < |tr| := by
      apply sq_lt_sq.mp; nlinarith
    have hw1 : |w| ≤ 1 := by
      by_contra hc
      rw [not_le] at hc
      have h1 : |w| + 1 ≤ |tr| := hlt
      nlinarith [sq_abs w, sq_abs tr, abs_nonneg w]
    have hw0 : w = 0 := by
      have hwb := abs_le.mp hw1
      have htr : |tr| ≤ 3 := by
        have : |tr| ^ 2 ≤ 9 := by nlinarith [sq_abs w, sq_abs tr]
        nlinarith [abs_nonneg tr]
      have htb := abs_le.mp htr
      obtain ⟨h1, h2⟩ := hwb
      obtain ⟨h3, h4⟩ := htb
      interval_cases w <;> interval_cases tr <;> omega
    subst hw0
    have hr : r = 0 := by
      have : M * r = 0 := by rw [hw]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hM0
      · exact h
    subst hr
    have hs : s = p := by
      have : A * (s - p) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hA
      · linarith
    have hq : q = 0 := by
      have : A * q = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hA
      · exact h
    subst hs; subst hq
    refine ⟨rfl, rfl, rfl, ?_⟩
    have : s * s = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1

/-- Helper: the Hessian determinant of a binary form is `4ac - b²`. -/
theorem binqf_det (f : BinQF) : f.hessian.det = 4 * f.a * f.c - f.b ^ 2 := by
  have h10 : f.coeff 1 0 = 0 := f.upper (show id 0 < id 1 by decide)
  rw [Matrix.det_fin_two]
  simp [QuadForm.hessian, h10, BinQF.a, BinQF.b, BinQF.c]
  ring

/-- Helper: an injective map to pairs with fixed nonzero product has finite fibre sets. -/
theorem finite_of_inj (n : ℤ) (hn : n ≠ 0) (Φ : (Fin 2 → ℤ) → ℤ × ℤ) (hΦ : Function.Injective Φ)
    (S : Set (Fin 2 → ℤ)) (h : ∀ x ∈ S, (Φ x).1 * (Φ x).2 = n) : S.Finite := by
  have hbox : (Set.Icc (-|n|) |n| ×ˢ Set.Icc (-|n|) |n| : Set (ℤ × ℤ)).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  refine (hbox.preimage hΦ.injOn).subset ?_
  intro x hx
  have hx' := h x hx
  have hu : (Φ x).1 ≠ 0 := fun h0 => hn (by rw [← hx', h0, zero_mul])
  have hv : (Φ x).2 ≠ 0 := fun h0 => hn (by rw [← hx', h0, mul_zero])
  have h1 : 1 ≤ |(Φ x).1| := Int.one_le_abs hu
  have h2 : 1 ≤ |(Φ x).2| := Int.one_le_abs hv
  have h3 : |(Φ x).1| * |(Φ x).2| = |n| := by rw [← abs_mul, hx']
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
  refine ⟨abs_le.mp ?_, abs_le.mp ?_⟩ <;> nlinarith

/-- Helper: an isotropic nondegenerate binary form has square, nonzero discriminant. -/
theorem binqf_disc_sq (f : BinQF) (hreg : f.Nondegenerate) (hiso : f.IsotropicIn ℚ) :
    ∃ M : ℤ, M ≠ 0 ∧ f.b ^ 2 - 4 * f.a * f.c = M ^ 2 := by
  have hdet : 4 * f.a * f.c - f.b ^ 2 ≠ 0 := by rw [← binqf_det]; exact hreg
  obtain ⟨x, hx0, hx⟩ := hiso
  rw [binqf_evalIn] at hx
  have hsq : IsSquare (((f.b ^ 2 - 4 * f.a * f.c : ℤ)) : ℚ) := by
    by_cases h1 : x 1 = 0
    · have hx0' : x 0 ≠ 0 := by
        intro h; apply hx0; ext i; fin_cases i <;> simp [h, h1]
      rw [h1] at hx
      have h2 : (f.a : ℚ) = 0 := by
        have : (f.a : ℚ) * x 0 ^ 2 = 0 := by simpa using hx
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hx0'
      refine ⟨f.b, ?_⟩; push_cast; rw [h2]; ring
    · refine ⟨(2 * f.a * x 0 + f.b * x 1) / x 1, ?_⟩
      push_cast
      field_simp
      linear_combination (-4 * (f.a : ℚ)) * hx
  obtain ⟨M, hM⟩ := Rat.isSquare_intCast_iff.mp hsq
  refine ⟨M, ?_, by rw [hM]; ring⟩
  intro h0
  apply hdet
  rw [h0] at hM
  linarith

/-- Helper: Lemma 3.2 (ii) for integral binary forms. -/
theorem binqf_finite (f : BinQF) (hreg : f.Nondegenerate) (hiso : f.IsotropicIn ℚ) (e : ℤ) (he : e ≠ 0) :
    {x : Fin 2 → ℤ | QuadForm.eval f x = e}.Finite := by
  obtain ⟨M, hM0, hM⟩ := binqf_disc_sq f hreg hiso
  have hev : ∀ x : Fin 2 → ℤ, QuadForm.eval f x = f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2 := by
    intro x; simpa using binqf_evalIn ℤ f x
  by_cases hA : f.a = 0
  · have hB : f.b ≠ 0 := by
      intro h0; apply hM0; rw [h0, hA] at hM; nlinarith
    refine finite_of_inj e he (fun x => (x 1, f.b * x 0 + f.c * x 1)) ?_ _ ?_
    · intro x y h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have h3 : f.b * (x 0 - y 0) = 0 := by rw [h1] at h2; linarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hB
      · ext i; fin_cases i
        · simp; linarith
        · simpa using h1
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      rw [hev, hA] at hx
      simp only
      linear_combination hx
  · refine finite_of_inj (4 * f.a * e) (mul_ne_zero (mul_ne_zero (by norm_num) hA) he)
      (fun x => (2 * f.a * x 0 + (f.b - M) * x 1, 2 * f.a * x 0 + (f.b + M) * x 1)) ?_ _ ?_
    · intro x y h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have h3 : M * (x 1 - y 1) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hM0
      · have h4 : x 1 = y 1 := by linarith
        have h5 : f.a * (x 0 - y 0) = 0 := by rw [h4] at h1; linarith
        rcases mul_eq_zero.mp h5 with h | h
        · exact absurd h hA
        · ext i; fin_cases i
          · simp; linarith
          · simpa using h4
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      rw [hev] at hx
      simp only
      linear_combination (4 * f.a) * hx + (x 1) ^ 2 * hM

/-- **Lemma 3.2** (Cassels, Ch. 13, §3, p. 290): let $f$ be an isotropic regular binary integral form. (i) The only
proper integral automorphs of $f$ are $\pm I$. (ii) Every integer $e \ne 0$ has only finitely many integral
representations $f(\vec{a}) = e$. Cassels' $f$ is classically integral; here $f$ is any integer-valued binary form
(a generalization). Regularity ($\det \ne 0$) is implicit in Cassels (his proof writes $f = kUV$ with $U, V$
independent); for $f = x^2$ (ii) fails. -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.2, p. 290"]
theorem binary_isotropic_aut (f : BinQF) (hreg : f.Nondegenerate) (hiso : f.IsotropicIn ℚ) :
    (∀ T ∈ Siegel.AutPlus f, T = 1 ∨ T = -1) ∧
      ∀ e : ℤ, e ≠ 0 → {x : Fin 2 → ℤ | QuadForm.eval f x = e}.Finite := by
  refine ⟨fun T hT => ?_, fun e he => binqf_finite f hreg hiso e he⟩
  obtain ⟨M, hM0, hM⟩ := binqf_disc_sq f hreg hiso
  obtain ⟨hA, hd⟩ := Siegel.mem_autPlus_iff.mp hT
  have hev : ∀ x : Fin 2 → ℤ, QuadForm.eval f x = f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2 := by
    intro x; simpa using binqf_evalIn ℤ f x
  have h1 := hA ![1, 0]
  have h2 := hA ![0, 1]
  have h3 := hA ![1, 1]
  rw [Matrix.det_fin_two] at hd
  simp only [hev, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2 h3
  simp at h1 h2 h3
  obtain ⟨r1, r2, r3⟩ := binqf_rel f.a f.b f.c (T.val 0 0) (T.val 0 1) (T.val 1 0) (T.val 1 1)
    (by linear_combination h1) (by linear_combination h2) (by linear_combination h3)
    (by linear_combination hd)
  obtain ⟨hq, hr, hs, hp⟩ := pm_core f.a f.b f.c M (T.val 0 0) (T.val 0 1) (T.val 1 0) (T.val 1 1)
    hM0 hM r1 r2 r3 (by linear_combination hd)
  rcases hp with hp | hp
  · left
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hq, hr, hs, hp]
  · right
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hq, hr, hs, hp]

/-- **Cassels' matrix (3.14)** $T = \begin{pmatrix} t - bu & -cu \\ au & t + bu\end{pmatrix}$, attached to a solution
$(t, u)$ of Pell's equation $t^2 + du^2 = 1$ (3.13) ($d = ac - b^2$; equivalently $t^2 - Du^2 = 1$ with $D = -d$; the
display is garbled in the machine-read text, the sign is confirmed by Example 6, p. 329), over any commutative ring.
Then $\det T = t^2 + du^2$.

Superseded as the tagged definition of (3.14) by `Cassels.Ch13.autMat`, the same matrix
(`Cassels.Ch13.pellMat_eq_autMat`). -/
def pellMat {R : Type*} [CommRing R] (a b c t u : R) : Matrix (Fin 2) (Fin 2) R :=
  !![t - b * u, -c * u; a * u, t + b * u]

/-- Helper: the entry relations of a proper integral automorph (from `H T = adj(Tᵀ) H`). -/
theorem aut_rel_poly (a b c p q r s : ℤ) (e1 : a * p ^ 2 + 2 * b * p * r + c * r ^ 2 = a)
    (e2 : a * q ^ 2 + 2 * b * q * s + c * s ^ 2 = c)
    (e3 : a * (p + q) ^ 2 + 2 * b * (p + q) * (r + s) + c * (r + s) ^ 2 = a + 2 * b + c)
    (hd : p * s - q * r = 1) :
    a * (s - p) = 2 * b * r ∧ a * q = -c * r ∧ c * (s - p) = -2 * b * q := by
  have e3' : a * p * q + b * (p * s + q * r) + c * r * s = b := by
    have : 2 * (a * p * q + b * (p * s + q * r) + c * r * s) = 2 * b := by
      linear_combination e3 - e1 - e2
    omega
  refine ⟨?_, ?_, ?_⟩
  · grind
  · grind
  · grind

/-- Helper: entry relations of `T ∈ O⁺(cform a b c)`. -/
theorem autPlus_rel {a b c : ℤ} {T : GL (Fin 2) ℤ} (hT : T ∈ Siegel.AutPlus (cform a b c)) :
    a * (T.val 1 1 - T.val 0 0) = 2 * b * T.val 1 0 ∧ a * T.val 0 1 = -c * T.val 1 0 ∧
      c * (T.val 1 1 - T.val 0 0) = -2 * b * T.val 0 1 ∧
      T.val 0 0 * T.val 1 1 - T.val 0 1 * T.val 1 0 = 1 := by
  obtain ⟨hA, hd⟩ := Siegel.mem_autPlus_iff.mp hT
  have h1 := hA ![1, 0]
  have h2 := hA ![0, 1]
  have h3 := hA ![1, 1]
  rw [Matrix.det_fin_two] at hd
  simp only [eval_cform, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2 h3
  simp at h1 h2 h3
  have := aut_rel_poly a b c (T.val 0 0) (T.val 0 1) (T.val 1 0) (T.val 1 1)
    (by linear_combination h1) (by linear_combination h2) (by linear_combination h3)
    (by linear_combination hd)
  exact ⟨this.1, this.2.1, this.2.2, hd⟩

/-- Helper: a proper integral automorph of `cform a b c` (`a ≠ 0`) is the real matrix (3.14) with
`t = (T₀₀ + T₁₁)/2`, `u = T₁₀ / a`, and these satisfy Pell's equation. -/
theorem autPlus_castM {a b c : ℤ} (ha : a ≠ 0) {T : GL (Fin 2) ℤ}
    (hT : T ∈ Siegel.AutPlus (cform a b c)) :
    castM T.val = pellMat (a : ℝ) b c (((T.val 0 0 : ℝ) + T.val 1 1) / 2) ((T.val 1 0 : ℝ) / a) ∧
      (((T.val 0 0 : ℝ) + T.val 1 1) / 2) ^ 2 + (a * c - b ^ 2) * ((T.val 1 0 : ℝ) / a) ^ 2 = 1 := by
  obtain ⟨r1, r2, r3, hd⟩ := autPlus_rel hT
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have r1' : (a : ℝ) * (T.val 1 1 - T.val 0 0) = 2 * b * T.val 1 0 := by exact_mod_cast r1
  have r2' : (a : ℝ) * T.val 0 1 = -c * T.val 1 0 := by exact_mod_cast r2
  have hd' : (T.val 0 0 : ℝ) * T.val 1 1 - T.val 0 1 * T.val 1 0 = 1 := by exact_mod_cast hd
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [castM, pellMat] <;> field_simp <;> linarith
  · field_simp
    grind

/-- Helper: anisotropy gives `a ≠ 0`. -/
theorem ne_zero_a_of_aniso {a b c : ℤ} (h : ¬ (cform a b c).IsotropicIn ℚ) : a ≠ 0 := by
  intro ha
  apply h
  refine ⟨![1, 0], ?_, ?_⟩
  · intro h0; have := congrFun h0 0; simp at this
  · rw [evalIn_cform]; simp [ha]

/-- Helper: anisotropy gives `c ≠ 0`. -/
theorem ne_zero_c_of_aniso {a b c : ℤ} (h : ¬ (cform a b c).IsotropicIn ℚ) : c ≠ 0 := by
  intro hc
  apply h
  refine ⟨![0, 1], ?_, ?_⟩
  · intro h0; have := congrFun h0 1; simp at this
  · rw [evalIn_cform]; simp [hc]

/-- Helper: from `gcd(a, gcd(m, c)) = 1`, `a ∣ m r` and `a ∣ c r` we get `a ∣ r`. -/
theorem dvd_of_gcd3 {a m c r : ℤ} (h : Int.gcd a (Int.gcd m c) = 1) (h1 : a ∣ m * r) (h2 : a ∣ c * r) :
    a ∣ r := by
  have e1 := Int.gcd_eq_gcd_ab a (Int.gcd m c : ℤ)
  have e2 := Int.gcd_eq_gcd_ab m c
  rw [h] at e1
  have : r = (a * Int.gcdA a (Int.gcd m c : ℤ)) * r +
      (Int.gcdA m c * (m * r) + Int.gcdB m c * (c * r)) * Int.gcdB a (Int.gcd m c : ℤ) := by
    have e1' : (1 : ℤ) = a * Int.gcdA a (Int.gcd m c : ℤ) + (Int.gcd m c : ℤ) * Int.gcdB a (Int.gcd m c : ℤ) := by
      exact_mod_cast e1
    calc r = 1 * r := by ring
      _ = _ := by rw [e1', e2]; ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
    (dvd_mul_of_dvd_left (dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)) _)

/-- **Theorem 3.1, the properly primitive case** (Cassels, Ch. 13, §3, (3.14)–(3.15'), pp. 291–292): let
$f = ax^2 + 2bxy + cy^2$ be primitive ($\gcd(a, b, c) = 1$, (3.9)), properly primitive ($\gcd(a, 2b, c) = 1$, (3.10)),
indefinite ($d = ac - b^2 < 0$) and anisotropic. Then the proper integral automorphs of $f$ are exactly the matrices
(3.14) with $t, u \in \mathbb{Z}$ and $t^2 + du^2 = 1$.

Kept beside `Cassels.Ch13.proper_eq_autMat`, whose direction "automorph ⇒ (3.14)" needs only $a \ne 0$. -/
@[kb "cassels1978" "Ch. 13, §3, Thm. 3.1, (3.13)–(3.15'), pp. 291–292 (properly primitive)"]
theorem autPlus_cform_iff_proper {a b c : ℤ} (hprim : Int.gcd a (Int.gcd b c) = 1)
    (hpp : Int.gcd a (Int.gcd (2 * b) c) = 1) (hind : a * c - b ^ 2 < 0)
    (haniso : ¬ (cform a b c).IsotropicIn ℚ) (T : GL (Fin 2) ℤ) :
    T ∈ Siegel.AutPlus (cform a b c) ↔
      ∃ t u : ℤ, t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1 ∧ T.val = pellMat a b c t u := by
  have ha := ne_zero_a_of_aniso haniso
  constructor
  · intro hT
    obtain ⟨r1, r2, r3, hd⟩ := autPlus_rel hT
    have hdvd : a ∣ T.val 1 0 := by
      refine dvd_of_gcd3 hpp ?_ ?_
      · exact ⟨T.val 1 1 - T.val 0 0, by linarith⟩
      · exact ⟨-T.val 0 1, by linarith⟩
    obtain ⟨u, hu⟩ := hdvd
    have hq : T.val 0 1 = -c * u := by
      apply mul_left_cancel₀ ha; rw [r2, hu]; ring
    have hs : T.val 1 1 - T.val 0 0 = 2 * b * u := by
      apply mul_left_cancel₀ ha; rw [r1, hu]; ring
    refine ⟨T.val 0 0 + b * u, u, ?_, ?_⟩
    · rw [hu, hq] at hd
      grind
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pellMat] <;> grind
  · rintro ⟨t, u, ht, hT⟩
    refine Siegel.mem_autPlus_iff.mpr ⟨fun x => ?_, ?_⟩
    · rw [hT]
      simp only [eval_cform, pellMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp
      linear_combination (a * x 0 ^ 2 + 2 * b * x 0 * x 1 + c * x 1 ^ 2) * ht
    · rw [hT, Matrix.det_fin_two]
      simp [pellMat]
      linear_combination ht

/-- **Theorem 3.1, the improperly primitive case** (Cassels, Ch. 13, §3, (3.14)–(3.15''), pp. 291–292): let
$f = ax^2 + 2bxy + cy^2$ be primitive ((3.9)) and improperly primitive ($\tfrac12 f \in \mathbb{Z}[x, y]$ but
$\tfrac12 f$ not classically integral, i.e. $a, c$ even and $b$ odd), indefinite and anisotropic. Then the proper
integral automorphs of $f$ are exactly the matrices (3.14) with rational $t, u$ such that $2t, 2u, t - u \in \mathbb{Z}$
and $t^2 + du^2 = 1$. (The conditions (3.15'') are partly garbled in the machine-read text; reconstructed from the
integrality of (3.14).) -/
@[kb "cassels1978" "Ch. 13, §3, Thm. 3.1, (3.13)–(3.15''), pp. 291–292 (improperly primitive)"]
theorem autPlus_cform_iff_improper {a b c : ℤ} (hprim : Int.gcd a (Int.gcd b c) = 1)
    (ha : Even a) (hc : Even c) (hb : Odd b) (hind : a * c - b ^ 2 < 0)
    (haniso : ¬ (cform a b c).IsotropicIn ℚ) (T : GL (Fin 2) ℤ) :
    T ∈ Siegel.AutPlus (cform a b c) ↔
      ∃ t u : ℚ, t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1 ∧ (∃ k : ℤ, 2 * t = k) ∧ (∃ k : ℤ, 2 * u = k) ∧
        (∃ k : ℤ, t - u = k) ∧ T.val.map (Int.cast : ℤ → ℚ) = pellMat (a : ℚ) b c t u := by
  have ha0 := ne_zero_a_of_aniso haniso
  have ha0' : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
  constructor
  · intro hT
    obtain ⟨r1, r2, r3, hd⟩ := autPlus_rel hT
    have hdvd : a ∣ 2 * T.val 1 0 := by
      refine dvd_of_gcd3 hprim ?_ ?_
      · exact ⟨T.val 1 1 - T.val 0 0, by linarith⟩
      · exact ⟨-2 * T.val 0 1, by linarith⟩
    obtain ⟨k, hk⟩ := hdvd
    have hs : T.val 1 1 - T.val 0 0 = b * k := by
      apply mul_left_cancel₀ ha0
      have : a * (b * k) = b * (a * k) := by ring
      rw [r1, this, ← hk]; ring
    have hq : 2 * T.val 0 1 = -c * k := by
      apply mul_left_cancel₀ ha0
      have : a * (-c * k) = -c * (a * k) := by ring
      rw [this, ← hk]; linear_combination 2 * r2
    obtain ⟨β, hβ⟩ := hb
    have hpar : T.val 0 0 + T.val 1 1 - k = 2 * (β * k + T.val 0 0) := by
      rw [hβ] at hs; linarith
    have e : ∀ i j, ((T.val i j : ℤ) : ℚ) = (T.val i j : ℚ) := fun _ _ => rfl
    have hs' : (T.val 1 1 : ℚ) - T.val 0 0 = b * k := by exact_mod_cast hs
    have hq' : 2 * (T.val 0 1 : ℚ) = -c * k := by exact_mod_cast hq
    have hk' : 2 * (T.val 1 0 : ℚ) = a * k := by exact_mod_cast hk
    have hd' : (T.val 0 0 : ℚ) * T.val 1 1 - T.val 0 1 * T.val 1 0 = 1 := by exact_mod_cast hd
    refine ⟨((T.val 0 0 : ℚ) + T.val 1 1) / 2, (k : ℚ) / 2, ?_, ⟨T.val 0 0 + T.val 1 1, by push_cast; ring⟩,
      ⟨k, by push_cast; ring⟩, ⟨β * k + T.val 0 0, ?_⟩, ?_⟩
    · grind
    · have : ((T.val 0 0 + T.val 1 1 - k : ℤ) : ℚ) = 2 * ((β * k + T.val 0 0 : ℤ) : ℚ) := by
        exact_mod_cast hpar
      push_cast at this ⊢
      linarith
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pellMat] <;> grind
  · rintro ⟨t, u, ht, -, -, -, hT⟩
    have h00 : (T.val 0 0 : ℚ) = t - b * u := by simpa [pellMat] using congrFun (congrFun hT 0) 0
    have h01 : (T.val 0 1 : ℚ) = -c * u := by simpa [pellMat] using congrFun (congrFun hT 0) 1
    have h10 : (T.val 1 0 : ℚ) = a * u := by simpa [pellMat] using congrFun (congrFun hT 1) 0
    have h11 : (T.val 1 1 : ℚ) = t + b * u := by simpa [pellMat] using congrFun (congrFun hT 1) 1
    refine Siegel.mem_autPlus_iff.mpr ⟨fun x => ?_, ?_⟩
    · apply Int.cast_injective (α := ℚ)
      simp only [eval_cform, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      push_cast
      rw [h00, h01, h10, h11]
      linear_combination ((a : ℚ) * x 0 ^ 2 + 2 * b * x 0 * x 1 + c * x 1 ^ 2) * ht
    · apply Int.cast_injective (α := ℚ)
      rw [Matrix.det_fin_two]
      push_cast
      rw [h00, h01, h10, h11]
      linear_combination ht

/-- Helper: `η(T) = t + u√D` with `t = (T₀₀ + T₁₁)/2`, `u = T₁₀/a`, `D = b² - ac`. -/
noncomputable def etaOf (a b c : ℤ) (T : GL (Fin 2) ℤ) : ℝ :=
  ((T.val 0 0 : ℝ) + T.val 1 1) / 2 + ((T.val 1 0 : ℝ) / a) * √((b : ℝ) ^ 2 - a * c)

/-- Helper: `t` and `u` are determined by the matrix (3.14). -/
theorem pellMat_inj_real {a b c : ℤ} (ha : (a : ℝ) ≠ 0) {t u t' u' : ℝ}
    (h : pellMat (a : ℝ) b c t u = pellMat (a : ℝ) b c t' u') : t = t' ∧ u = u' := by
  have h10 := congrFun (congrFun h 1) 0
  have h00 := congrFun (congrFun h 0) 0
  simp [pellMat] at h10 h00
  have hu : u = u' := by
    rcases h10 with h | h
    · exact h
    · first | exact absurd h ha | exact absurd (by exact_mod_cast h) ha
  subst hu
  exact ⟨by linarith, rfl⟩

/-- Helper: if `castM T = pellMat t u` then `η(T) = t + u√D`. -/
theorem etaOf_eq {a b c : ℤ} (ha : a ≠ 0) {T : GL (Fin 2) ℤ} {t u : ℝ}
    (h : castM T.val = pellMat (a : ℝ) b c t u) : etaOf a b c T = t + u * √((b : ℝ) ^ 2 - a * c) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [castM, pellMat] at h00 h10 h11
  unfold etaOf
  rw [h00, h10, h11]
  field_simp
  ring

/-- Helper: product of two matrices (3.14). -/
theorem pellMat_mul {R : Type*} [CommRing R] (a b c t u t' u' : R) :
    pellMat a b c t u * pellMat a b c t' u' =
      pellMat a b c (t * t' + (b ^ 2 - a * c) * u * u') (t * u' + t' * u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pellMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Helper: `η` is multiplicative on `O⁺(f)`. -/
theorem etaOf_mul {a b c : ℤ} (ha : a ≠ 0) (hind : a * c - b ^ 2 < 0) {T S : GL (Fin 2) ℤ}
    (hT : T ∈ Siegel.AutPlus (cform a b c)) (hS : S ∈ Siegel.AutPlus (cform a b c)) :
    etaOf a b c (T * S) = etaOf a b c T * etaOf a b c S := by
  obtain ⟨t, u, hT1, hT2⟩ : ∃ t u : ℝ, castM T.val = pellMat (a : ℝ) b c t u ∧
      t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1 := ⟨_, _, autPlus_castM ha hT⟩
  obtain ⟨t', u', hS1, hS2⟩ : ∃ t u : ℝ, castM S.val = pellMat (a : ℝ) b c t u ∧
      t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1 := ⟨_, _, autPlus_castM ha hS⟩
  have hD : (0 : ℝ) ≤ (b : ℝ) ^ 2 - a * c := by
    have : (0 : ℤ) ≤ b ^ 2 - a * c := by linarith
    exact_mod_cast this
  have hs : √((b : ℝ) ^ 2 - a * c) ^ 2 = (b : ℝ) ^ 2 - a * c := Real.sq_sqrt hD
  have hm : castM (T * S).val = pellMat (a : ℝ) b c (t * t' + ((b : ℝ) ^ 2 - a * c) * u * u')
      (t * u' + t' * u) := by
    rw [Units.val_mul, castM_mul, hT1, hS1, pellMat_mul]
  rw [etaOf_eq ha hm, etaOf_eq ha hT1, etaOf_eq ha hS1]
  linear_combination (-(u * u')) * hs

/-- Helper: `η(1) = 1`. -/
theorem etaOf_one (a b c : ℤ) : etaOf a b c 1 = 1 := by
  simp [etaOf]

/-- Helper: `η(-T) = -η(T)`. -/
theorem etaOf_neg (a b c : ℤ) (T : GL (Fin 2) ℤ) : etaOf a b c (-T) = -etaOf a b c T := by
  simp [etaOf]
  ring

/-- Helper: `η ≠ 0`, `η⁻¹ = t - u√D` and `T₀₀ + T₁₁ = η + η⁻¹`. -/
theorem etaOf_data {a b c : ℤ} (ha : a ≠ 0) (hind : a * c - b ^ 2 < 0) {T : GL (Fin 2) ℤ}
    (hT : T ∈ Siegel.AutPlus (cform a b c)) :
    etaOf a b c T ≠ 0 ∧
      (etaOf a b c T)⁻¹ = ((T.val 0 0 : ℝ) + T.val 1 1) / 2 - ((T.val 1 0 : ℝ) / a) * √((b : ℝ) ^ 2 - a * c) ∧
      ((T.val 0 0 : ℝ) + T.val 1 1) = etaOf a b c T + (etaOf a b c T)⁻¹ := by
  obtain ⟨-, hT2⟩ := autPlus_castM ha hT
  have hD : (0 : ℝ) ≤ (b : ℝ) ^ 2 - a * c := by
    have : (0 : ℤ) ≤ b ^ 2 - a * c := by linarith
    exact_mod_cast this
  have hs : √((b : ℝ) ^ 2 - a * c) ^ 2 = (b : ℝ) ^ 2 - a * c := Real.sq_sqrt hD
  have hprod : etaOf a b c T * (((T.val 0 0 : ℝ) + T.val 1 1) / 2 - ((T.val 1 0 : ℝ) / a) *
      √((b : ℝ) ^ 2 - a * c)) = 1 := by
    unfold etaOf
    linear_combination hT2 - ((T.val 1 0 : ℝ) / a) ^ 2 * hs
  have hne : etaOf a b c T ≠ 0 := by
    intro h; rw [h] at hprod; simp at hprod
  have hinv : (etaOf a b c T)⁻¹ = ((T.val 0 0 : ℝ) + T.val 1 1) / 2 - ((T.val 1 0 : ℝ) / a) *
      √((b : ℝ) ^ 2 - a * c) := by
    exact inv_eq_of_mul_eq_one_right hprod
  refine ⟨hne, hinv, ?_⟩
  rw [hinv]; unfold etaOf; ring

/-- Helper: `η` is injective on `O⁺(f)`. -/
theorem etaOf_injOn {a b c : ℤ} (ha : a ≠ 0) (hind : a * c - b ^ 2 < 0) {T S : GL (Fin 2) ℤ}
    (hT : T ∈ Siegel.AutPlus (cform a b c)) (hS : S ∈ Siegel.AutPlus (cform a b c))
    (h : etaOf a b c T = etaOf a b c S) : T = S := by
  obtain ⟨hT1, -⟩ := autPlus_castM ha hT
  obtain ⟨hS1, -⟩ := autPlus_castM ha hS
  obtain ⟨-, hTi, -⟩ := etaOf_data ha hind hT
  obtain ⟨-, hSi, -⟩ := etaOf_data ha hind hS
  have hDpos : (0 : ℝ) < (b : ℝ) ^ 2 - a * c := by
    have : (0 : ℤ) < b ^ 2 - a * c := by linarith
    exact_mod_cast this
  have hsq : 0 < √((b : ℝ) ^ 2 - a * c) := Real.sqrt_pos.mpr hDpos
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have h1 := h
  have h2 : (etaOf a b c T)⁻¹ = (etaOf a b c S)⁻¹ := by rw [h]
  rw [hTi, hSi] at h2
  unfold etaOf at h1
  have ht : ((T.val 0 0 : ℝ) + T.val 1 1) / 2 = ((S.val 0 0 : ℝ) + S.val 1 1) / 2 := by linarith
  have hu : ((T.val 1 0 : ℝ) / a) = ((S.val 1 0 : ℝ) / a) := by
    have : ((T.val 1 0 : ℝ) / a) * √((b : ℝ) ^ 2 - a * c) = ((S.val 1 0 : ℝ) / a) * √((b : ℝ) ^ 2 - a * c) := by
      linarith
    exact mul_right_cancel₀ hsq.ne' this
  have hmat : castM T.val = castM S.val := by rw [hT1, hS1, ht, hu]
  apply Units.ext
  ext i j
  have := congrFun (congrFun hmat i) j
  simpa [castM] using this

/-- Helper: `η` of the inverse. -/
theorem etaOf_inv {a b c : ℤ} (ha : a ≠ 0) (hind : a * c - b ^ 2 < 0) {T : GL (Fin 2) ℤ}
    (hT : T ∈ Siegel.AutPlus (cform a b c)) : etaOf a b c T⁻¹ = (etaOf a b c T)⁻¹ := by
  have h := etaOf_mul ha hind hT (inv_mem hT)
  rw [mul_inv_cancel, etaOf_one] at h
  obtain ⟨hne, -⟩ := etaOf_data ha hind hT
  exact eq_inv_of_mul_eq_one_right h.symm

/-- Helper: no `η` strictly between `1` and `3/2` in absolute value. -/
theorem etaOf_not_small {a b c : ℤ} (ha : a ≠ 0) (hind : a * c - b ^ 2 < 0) {T : GL (Fin 2) ℤ}
    (hT : T ∈ Siegel.AutPlus (cform a b c)) :
    ¬ (1 < |etaOf a b c T| ∧ |etaOf a b c T| < 3 / 2) := by
  rintro ⟨h1, h2⟩
  obtain ⟨hne, -, htr⟩ := etaOf_data ha hind hT
  set n : ℤ := T.val 0 0 + T.val 1 1 with hn
  have hn' : (n : ℝ) = etaOf a b c T + (etaOf a b c T)⁻¹ := by rw [← htr]; simp [hn]
  set η := etaOf a b c T
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hη : η < -1 := by rw [abs_of_neg hneg] at h1; linarith
    have hη2 : -(3/2) < η := by rw [abs_of_neg hneg] at h2; linarith
    have hinv2 : η⁻¹ < 0 := inv_lt_zero.mpr hneg
    have hinv : -1 < η⁻¹ := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [mul_inv_cancel₀ hne]
    have hlow : (n : ℝ) < -2 := by
      have : η * η⁻¹ = 1 := mul_inv_cancel₀ hne
      nlinarith
    have hup : (-3 : ℝ) < n := by
      have : η * η⁻¹ = 1 := mul_inv_cancel₀ hne
      nlinarith
    have : n < -2 := by exact_mod_cast hlow
    have : -3 < n := by exact_mod_cast hup
    omega
  · have hη : 1 < η := by rw [abs_of_pos hpos] at h1; linarith
    have hη2 : η < 3/2 := by rw [abs_of_pos hpos] at h2; linarith
    have hinv2 : 0 < η⁻¹ := inv_pos.mpr hpos
    have hinv : η⁻¹ < 1 := inv_lt_one_of_one_lt₀ hη
    have : η * η⁻¹ = 1 := mul_inv_cancel₀ hne
    have hlow : (2 : ℝ) < n := by nlinarith
    have hup : (n : ℝ) < 3 := by nlinarith
    have : 2 < n := by exact_mod_cast hlow
    have : n < 3 := by exact_mod_cast hup
    omega

/-- Helper: `-T ∈ O⁺(f)` for `T ∈ O⁺(f)`. -/
theorem neg_mem_autPlus {a b c : ℤ} {T : GL (Fin 2) ℤ} (hT : T ∈ Siegel.AutPlus (cform a b c)) :
    -T ∈ Siegel.AutPlus (cform a b c) := by
  obtain ⟨hA, hd⟩ := Siegel.mem_autPlus_iff.mp hT
  refine Siegel.mem_autPlus_iff.mpr ⟨fun x => ?_, ?_⟩
  · have := hA (-x)
    simp only [eval_cform, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Units.val_neg,
      Matrix.neg_apply, Pi.neg_apply] at this ⊢
    linear_combination this
  · simp [Matrix.det_neg, hd]

/-- Helper: `pellMat a b c 1 0 = 1`. -/
theorem pellMat_one_zero {R : Type*} [CommRing R] (a b c : R) : pellMat a b c 1 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pellMat]

/-- Helper: integral Pell solutions give proper automorphs. -/
theorem mem_autPlus_of_pellMat {a b c : ℤ} {T : GL (Fin 2) ℤ} {t u : ℤ}
    (ht : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1) (hT : T.val = pellMat a b c t u) :
    T ∈ Siegel.AutPlus (cform a b c) := by
  refine Siegel.mem_autPlus_iff.mpr ⟨fun x => ?_, ?_⟩
  · rw [hT]
    simp only [eval_cform, pellMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    linear_combination (a * x 0 ^ 2 + 2 * b * x 0 * x 1 + c * x 1 ^ 2) * ht
  · rw [hT, Matrix.det_fin_two]
    simp [pellMat]
    linear_combination ht

/-- Helper: anisotropy forces `b² - ac` to be a non-square. -/
theorem not_isSquare_of_aniso {a b c : ℤ} (h : ¬ (cform a b c).IsotropicIn ℚ) :
    ¬ IsSquare (b ^ 2 - a * c) := by
  rintro ⟨m, hm⟩
  have ha := ne_zero_a_of_aniso h
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  apply h
  refine ⟨![((m : ℚ) - b) / a, 1], ?_, ?_⟩
  · intro h0; have := congrFun h0 1; simp at this
  · rw [evalIn_cform]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hm' : (b : ℚ) ^ 2 - a * c = m * m := by exact_mod_cast hm
    field_simp
    linear_combination (-1 : ℚ) * hm'

/-- Helper: there is a proper automorph with `|η| ≠ 1`. -/
theorem exists_eta_ne_one {a b c : ℤ} (ha : a ≠ 0) (hind : a * c - b ^ 2 < 0)
    (haniso : ¬ (cform a b c).IsotropicIn ℚ) :
    ∃ T ∈ Siegel.AutPlus (cform a b c), |etaOf a b c T| ≠ 1 := by
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare (d := b ^ 2 - a * c) (by linarith)
    (not_isSquare_of_aniso haniso)
  have hprod : pellMat a b c x y * pellMat a b c x (-y) = 1 := by
    rw [pellMat_mul]
    have h1 : x * x + (b ^ 2 - a * c) * y * -y = 1 := by linear_combination hxy
    have h2 : x * -y + x * y = 0 := by ring
    rw [h1, h2, pellMat_one_zero]
  have hprod' : pellMat a b c x (-y) * pellMat a b c x y = 1 := by
    rw [pellMat_mul]
    have h1 : x * x + (b ^ 2 - a * c) * -y * y = 1 := by linear_combination hxy
    have h2 : x * y + x * -y = 0 := by ring
    rw [h1, h2, pellMat_one_zero]
  let T : GL (Fin 2) ℤ := ⟨pellMat a b c x y, pellMat a b c x (-y), hprod, hprod'⟩
  have hT : T ∈ Siegel.AutPlus (cform a b c) :=
    mem_autPlus_of_pellMat (t := x) (u := y) (by linear_combination hxy) rfl
  refine ⟨T, hT, ?_⟩
  have hcast : castM T.val = pellMat (a : ℝ) b c (x : ℝ) (y : ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [T, castM, pellMat]
  rw [etaOf_eq ha hcast]
  have hD : (0 : ℝ) ≤ (b : ℝ) ^ 2 - a * c := by
    have : (0 : ℤ) ≤ b ^ 2 - a * c := by linarith
    exact_mod_cast this
  have hs : √((b : ℝ) ^ 2 - a * c) ^ 2 = (b : ℝ) ^ 2 - a * c := Real.sq_sqrt hD
  have hxy' : (x : ℝ) ^ 2 - ((b : ℝ) ^ 2 - a * c) * y ^ 2 = 1 := by exact_mod_cast hxy
  have hsq : 0 < √((b : ℝ) ^ 2 - a * c) := by
    apply Real.sqrt_pos.mpr
    have : (0 : ℤ) < b ^ 2 - a * c := by linarith
    exact_mod_cast this
  have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  intro habs
  have hprod2 : ((x : ℝ) + y * √((b : ℝ) ^ 2 - a * c)) * ((x : ℝ) - y * √((b : ℝ) ^ 2 - a * c)) = 1 := by
    linear_combination hxy' - (y : ℝ) ^ 2 * hs
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp habs with h | h
  · rw [h] at hprod2
    have : (x : ℝ) - y * √((b : ℝ) ^ 2 - a * c) = 1 := by linarith
    have : (y : ℝ) * √((b : ℝ) ^ 2 - a * c) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hy' h
    · exact hsq.ne' h
  · rw [h] at hprod2
    have : (x : ℝ) - y * √((b : ℝ) ^ 2 - a * c) = -1 := by linarith
    have : (y : ℝ) * √((b : ℝ) ^ 2 - a * c) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hy' h
    · exact hsq.ne' h

/-- Helper: `η(T^k) = η(T)^k`. -/
theorem etaOf_zpow {a b c : ℤ} (ha : a ≠ 0) (hind : a * c - b ^ 2 < 0) {T : GL (Fin 2) ℤ}
    (hT : T ∈ Siegel.AutPlus (cform a b c)) (k : ℤ) : etaOf a b c (T ^ k) = (etaOf a b c T) ^ k := by
  have hne := (etaOf_data ha hind hT).1
  induction k using Int.induction_on with
  | zero => simp [etaOf_one]
  | succ k ih =>
    rw [_root_.zpow_add_one, etaOf_mul ha hind (zpow_mem hT k) hT, ih, zpow_add_one₀ hne]
  | pred k ih =>
    have h1 : T ^ (-(k : ℤ) - 1) = T ^ (-(k : ℤ)) * T⁻¹ := by rw [_root_.zpow_sub_one]
    rw [h1, etaOf_mul ha hind (zpow_mem hT _) (inv_mem hT), ih, etaOf_inv ha hind hT, zpow_sub_one₀ hne]

/-- **Theorem 3.1, the group structure** (Cassels, Ch. 13, §3, p. 291): the group $O^+(f)$ of proper integral
automorphs of a primitive indefinite anisotropic binary form consists of the $\pm T_0^{\nu}$ ($\nu \in \mathbb{Z}$),
where $T_0$ has infinite order. -/
@[kb "cassels1978" "Ch. 13, §3, Thm. 3.1, p. 291 (O⁺(f) = {±T₀^ν})"]
theorem autPlus_cform_cyclic {a b c : ℤ} (hprim : Int.gcd a (Int.gcd b c) = 1) (hind : a * c - b ^ 2 < 0)
    (haniso : ¬ (cform a b c).IsotropicIn ℚ) :
    ∃ T₀ ∈ Siegel.AutPlus (cform a b c), orderOf T₀ = 0 ∧
      ∀ T ∈ Siegel.AutPlus (cform a b c), ∃ ν : ℤ, T = T₀ ^ ν ∨ T = -(T₀ ^ ν) := by
  have ha := ne_zero_a_of_aniso haniso
  let S : AddSubgroup ℝ :=
    { carrier := {x | ∃ T ∈ Siegel.AutPlus (cform a b c), Real.log |etaOf a b c T| = x}
      zero_mem' := ⟨1, one_mem _, by simp [etaOf_one]⟩
      add_mem' := by
        rintro _ _ ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩
        refine ⟨T * T', mul_mem hT hT', ?_⟩
        rw [etaOf_mul ha hind hT hT', abs_mul, Real.log_mul]
        · exact abs_ne_zero.mpr (etaOf_data ha hind hT).1
        · exact abs_ne_zero.mpr (etaOf_data ha hind hT').1
      neg_mem' := by
        rintro _ ⟨T, hT, rfl⟩
        refine ⟨T⁻¹, inv_mem hT, ?_⟩
        rw [etaOf_inv ha hind hT, abs_inv, Real.log_inv] }
  have hdisj : Disjoint (S : Set ℝ) (Set.Ioo 0 (Real.log (3 / 2))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨T, hT, rfl⟩ ⟨h0, h1⟩
    apply etaOf_not_small ha hind hT
    have hpos : 0 < |etaOf a b c T| := abs_pos.mpr (etaOf_data ha hind hT).1
    exact ⟨(Real.log_pos_iff hpos.le).mp h0, (Real.log_lt_log_iff hpos (by norm_num)).mp h1⟩
  have hcyc : IsAddCyclic S :=
    AddSubgroup.isAddCyclic_of_disjoint_Ioo_zero (Real.log_pos (by norm_num)) hdisj
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨T₁, hT₁, hne1⟩ := exists_eta_ne_one ha hind haniso
  have hg0 : (g : ℝ) ≠ 0 := by
    intro h0
    have hx : (⟨Real.log |etaOf a b c T₁|, T₁, hT₁, rfl⟩ : S) ∈ AddSubgroup.zmultiples g := hg _
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    have := congrArg Subtype.val hk
    simp [h0] at this
    rw [← Real.log_abs] at this
    have hpos : 0 < |etaOf a b c T₁| := abs_pos.mpr (etaOf_data ha hind hT₁).1
    exact hne1 (Real.eq_one_of_pos_of_log_eq_zero hpos this.symm)
  obtain ⟨T₀, hT₀, hlog⟩ := g.2
  have hpos0 : 0 < |etaOf a b c T₀| := abs_pos.mpr (etaOf_data ha hind hT₀).1
  refine ⟨T₀, hT₀, ?_, ?_⟩
  · by_contra hord
    have hp : 0 < orderOf T₀ := Nat.pos_of_ne_zero hord
    have h1 := pow_orderOf_eq_one T₀
    have h2 : etaOf a b c (T₀ ^ ((orderOf T₀ : ℕ) : ℤ)) = 1 := by
      rw [zpow_natCast, h1, etaOf_one]
    rw [etaOf_zpow ha hind hT₀] at h2
    have h3 : |etaOf a b c T₀| ^ (orderOf T₀) = 1 := by
      have := congrArg abs h2
      rwa [abs_zpow, abs_one, zpow_natCast] at this
    have h4 : |etaOf a b c T₀| = 1 := (pow_eq_one_iff_of_nonneg hpos0.le hp.ne').mp h3
    apply hg0
    rw [← hlog, h4]; simp
  · intro T hT
    have hx : (⟨Real.log |etaOf a b c T|, T, hT, rfl⟩ : S) ∈ AddSubgroup.zmultiples g := hg _
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    have hk' : (k : ℝ) * g = Real.log |etaOf a b c T| := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨k, ?_⟩
    have hTk : T₀ ^ k ∈ Siegel.AutPlus (cform a b c) := zpow_mem hT₀ k
    have habs : |etaOf a b c T| = |etaOf a b c (T₀ ^ k)| := by
      have hposT : 0 < |etaOf a b c T| := abs_pos.mpr (etaOf_data ha hind hT).1
      have hposk : 0 < |etaOf a b c (T₀ ^ k)| := abs_pos.mpr (etaOf_data ha hind hTk).1
      apply Real.log_injOn_pos hposT hposk
      rw [← hk', etaOf_zpow ha hind hT₀, abs_zpow, Real.log_zpow, hlog]
    rcases abs_eq_abs.mp habs with h | h
    · left; exact etaOf_injOn ha hind hT hTk h
    · right
      refine etaOf_injOn ha hind hT (neg_mem_autPlus hTk) ?_
      rw [etaOf_neg]; exact h

/-! ### The linear factors $L$, $M$ ((3.21)–(3.24)) -/

/-- **The linear form $L$** of (3.22) (Cassels, Ch. 13, p. 292): $L(x, y) = ax + by + y\sqrt{D}$, $D = b^2 - ac$
(3.21). -/
@[kb "cassels1978" "Ch. 13, §3, (3.21)–(3.22), p. 292 (the linear form L)"]
noncomputable def linL (a b c : ℤ) (x : Fin 2 → ℝ) : ℝ :=
  a * x 0 + b * x 1 + x 1 * √((b : ℝ) ^ 2 - a * c)

/-- **The linear form $M$** of (3.22): $M(x, y) = ax + by - y\sqrt{D}$. -/
@[kb "cassels1978" "Ch. 13, §3, (3.21)–(3.22), p. 292 (the linear form M)"]
noncomputable def linM (a b c : ℤ) (x : Fin 2 → ℝ) : ℝ :=
  a * x 0 + b * x 1 - x 1 * √((b : ℝ) ^ 2 - a * c)

/-- **(3.22)** (Cassels, Ch. 13, p. 292): $af(x, y) = (ax + by)^2 - Dy^2 = L(x, y)M(x, y)$ when $D = b^2 - ac \ge 0$. -/
@[kb "cassels1978" "Ch. 13, §3, (3.22), p. 292"]
theorem linL_mul_linM {a b c : ℤ} (hD : 0 ≤ b ^ 2 - a * c) (x : Fin 2 → ℝ) :
    linL a b c x * linM a b c x = a * val (realMat (cform a b c)) x := by
  have hs : √((b : ℝ) ^ 2 - a * c) ^ 2 = (b : ℝ) ^ 2 - a * c :=
    Real.sq_sqrt (by exact_mod_cast hD)
  rw [val_realMat_cform]
  unfold linL linM
  linear_combination (-(x 1) ^ 2) * hs

/-- **(3.23)–(3.24)** (Cassels, Ch. 13, p. 292): for the matrix $T$ of (3.14), with $t^2 + du^2 = 1$,
$L(T\vec{x}) = \eta L(\vec{x})$ and $M(T\vec{x}) = \eta^{-1}M(\vec{x})$, where $\eta = t + u\sqrt{D}$ and
$\eta^{-1} = t - u\sqrt{D}$. -/
@[kb "cassels1978" "Ch. 13, §3, (3.23)–(3.24), p. 292"]
theorem linL_pellMat {a b c : ℤ} (hD : 0 ≤ b ^ 2 - a * c) {t u : ℝ}
    (ht : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1) (x : Fin 2 → ℝ) :
    linL a b c (pellMat (a : ℝ) b c t u *ᵥ x) = (t + u * √((b : ℝ) ^ 2 - a * c)) * linL a b c x ∧
      linM a b c (pellMat (a : ℝ) b c t u *ᵥ x) = (t - u * √((b : ℝ) ^ 2 - a * c)) * linM a b c x ∧
      (t + u * √((b : ℝ) ^ 2 - a * c)) * (t - u * √((b : ℝ) ^ 2 - a * c)) = 1 := by
  have hs : √((b : ℝ) ^ 2 - a * c) ^ 2 = (b : ℝ) ^ 2 - a * c :=
    Real.sq_sqrt (by exact_mod_cast hD)
  refine ⟨?_, ?_, ?_⟩
  · simp only [linL, pellMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    linear_combination (-(u * x 1)) * hs
  · simp only [linM, pellMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    linear_combination (-u * x 1) * hs
  · linear_combination ht + (-u ^ 2) * hs

/-- **Theorem 3.1, Corollary, first part** (Cassels, Ch. 13, §3, p. 292): if $t, u$ satisfy $t^2 + du^2 = -1$ (3.25),
then the matrix $T$ of (3.14) satisfies $f(T\vec{x}) = -f(\vec{x})$ and $\det T = -1$: it is an improper equivalence of
$f$ with $-f$ (integral when $t, u$ satisfy the integrality conditions (3.15)).

Superseded by `Cassels.Ch13.thm_3_1_cor`, the same statement over every commutative ring. -/
theorem pellMat_neg_one {a b c : ℤ} {t u : ℚ} (ht : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = -1) :
    (∀ x : Fin 2 → ℚ, (cform a b c).evalIn ℚ (pellMat (a : ℚ) b c t u *ᵥ x) = -(cform a b c).evalIn ℚ x) ∧
      (pellMat (a : ℚ) b c t u).det = -1 := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [evalIn_cform, evalIn_cform]
    simp only [pellMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    linear_combination (↑a * x 0 ^ 2 + 2 * ↑b * x 0 * x 1 + ↑c * x 1 ^ 2) * ht
  · rw [Matrix.det_fin_two]
    simp [pellMat]
    linear_combination ht

/-- Helper: a norm `-1` unit `p + q√D > 1` has `p, q > 0`. -/
theorem neg_pell_pos {D : ℤ} (hD : 0 < D) {p q : ℤ} (h : p ^ 2 - D * q ^ 2 = -1)
    (hw : 1 < (p : ℝ) + q * √(D : ℝ)) : 0 < p ∧ 0 < q := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hs : 0 < √(D : ℝ) := Real.sqrt_pos.mpr hDr
  have hss : √(D : ℝ) * √(D : ℝ) = D := Real.mul_self_sqrt hDr.le
  have h' : (p : ℝ) ^ 2 - D * q ^ 2 = -1 := by exact_mod_cast h
  have hprod : ((p : ℝ) + q * √(D : ℝ)) * ((p : ℝ) - q * √(D : ℝ)) = -1 := by
    linear_combination h' - (q : ℝ) ^ 2 * hss
  have hlow : -1 < (p : ℝ) - q * √(D : ℝ) := by nlinarith
  constructor
  · have : (0 : ℝ) < p := by linarith
    exact_mod_cast this
  · have hneg : (p : ℝ) - q * √(D : ℝ) < 0 := by nlinarith
    have : (0 : ℝ) < q * √(D : ℝ) := by linarith
    have : (0 : ℝ) < q := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    exact_mod_cast this

/-- **Theorem 3.1, Corollary, second part** (Cassels, Ch. 13, §3, p. 292): let $D > 0$ not be a square. If
$\eta_0 = t_0 + u_0\sqrt{D}$ is the least $\eta > 1$ coming from an integral solution of $t^2 - Du^2 = 1$ (the
fundamental solution), and $\eta_1 = t_1 + u_1\sqrt{D}$ is the least one coming from an integral solution
$t_1, u_1 > 0$ of $t^2 - Du^2 = -1$, then $\eta_1^2 = \eta_0$. Stated for integral solutions (Cassels allows the
half-integral ones (3.15'') in the improperly primitive case). -/
@[kb "cassels1978" "Ch. 13, §3, Thm. 3.1, Cor., p. 292 (η₁² = η₀)"]
theorem pell_neg_fundamental_sq {D : ℤ} (hD : 0 < D) (hsq : ¬ IsSquare D) {η₀ η₁ : ℝ}
    (h₀ : IsLeast {η : ℝ | 1 < η ∧ ∃ t u : ℤ, t ^ 2 - D * u ^ 2 = 1 ∧ η = t + u * √(D : ℝ)} η₀)
    (h₁ : IsLeast {η : ℝ | ∃ t u : ℤ, 0 < t ∧ 0 < u ∧ t ^ 2 - D * u ^ 2 = -1 ∧ η = t + u * √(D : ℝ)} η₁) :
    η₁ ^ 2 = η₀ := by
  obtain ⟨⟨hε1, t₀, u₀, ht₀, hε⟩, hmin₀⟩ := h₀
  obtain ⟨⟨t₁, u₁, ht₁pos, hu₁pos, ht₁, hθ⟩, hmin₁⟩ := h₁
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hs : 0 < √(D : ℝ) := Real.sqrt_pos.mpr hDr
  have hss : √(D : ℝ) * √(D : ℝ) = D := Real.mul_self_sqrt hDr.le
  set s := √(D : ℝ) with hsdef
  have ht₀' : (t₀ : ℝ) ^ 2 - D * u₀ ^ 2 = 1 := by exact_mod_cast ht₀
  have ht₁' : (t₁ : ℝ) ^ 2 - D * u₁ ^ 2 = -1 := by exact_mod_cast ht₁
  have hθ1 : 1 < η₁ := by
    rw [hθ]
    have : (1 : ℝ) ≤ t₁ := by exact_mod_cast ht₁pos
    have : (0 : ℝ) < u₁ * s := mul_pos (by exact_mod_cast hu₁pos) hs
    linarith
  have hθpos : 0 < η₁ := by linarith
  have hεpos : 0 < η₀ := by linarith
  -- ε ≤ θ²
  have hA : η₀ ≤ η₁ ^ 2 := by
    apply hmin₀
    refine ⟨by nlinarith, t₁ ^ 2 + D * u₁ ^ 2, 2 * t₁ * u₁, ?_, ?_⟩
    · linear_combination (t₁ ^ 2 - D * u₁ ^ 2 - 1) * ht₁
    · rw [hθ]; push_cast
      linear_combination (u₁ : ℝ) ^ 2 * hss
  -- w = ε / θ
  have hw : (((D * u₀ * u₁ - t₀ * t₁ : ℤ) : ℝ) + ((t₀ * u₁ - u₀ * t₁ : ℤ) : ℝ) * s) * η₁ = η₀ := by
    rw [hθ, hε]; push_cast
    linear_combination (-(t₀ : ℝ) - u₀ * s) * ht₁' + ((u₁ : ℝ) ^ 2 * t₀ - u₀ * u₁ * t₁) * hss
  have hpq : (D * u₀ * u₁ - t₀ * t₁) ^ 2 - D * (t₀ * u₁ - u₀ * t₁) ^ 2 = -1 := by
    linear_combination (t₁ ^ 2 - D * u₁ ^ 2) * ht₀ + ht₁
  have hw' : (((t₁ * t₀ - D * u₁ * u₀ : ℤ) : ℝ) + ((u₁ * t₀ - t₁ * u₀ : ℤ) : ℝ) * s) * η₀ = η₁ := by
    rw [hθ, hε]; push_cast
    linear_combination ((t₁ : ℝ) + u₁ * s) * ht₀' + (u₀ * u₁ * t₀ - (u₀ : ℝ) ^ 2 * t₁) * hss
  have hp'q' : (t₁ * t₀ - D * u₁ * u₀) ^ 2 - D * (u₁ * t₀ - t₁ * u₀) ^ 2 = -1 := by
    linear_combination (t₁ ^ 2 - D * u₁ ^ 2) * ht₀ + ht₁
  rcases lt_trichotomy (((D * u₀ * u₁ - t₀ * t₁ : ℤ) : ℝ) + ((t₀ * u₁ - u₀ * t₁ : ℤ) : ℝ) * s) 1 with
    hlt | heq | hgt
  · exfalso
    have h1 : η₀ < η₁ := by nlinarith
    have hgt' : 1 < ((t₁ * t₀ - D * u₁ * u₀ : ℤ) : ℝ) + ((u₁ * t₀ - t₁ * u₀ : ℤ) : ℝ) * s := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    obtain ⟨hp', hq'⟩ := neg_pell_pos hD hp'q' hgt'
    have := hmin₁ ⟨t₁ * t₀ - D * u₁ * u₀, u₁ * t₀ - t₁ * u₀, hp', hq', hp'q', rfl⟩
    nlinarith
  · exfalso
    have hprodR : (((D * u₀ * u₁ - t₀ * t₁ : ℤ) : ℝ) + ((t₀ * u₁ - u₀ * t₁ : ℤ) : ℝ) * s) *
        (((D * u₀ * u₁ - t₀ * t₁ : ℤ) : ℝ) - ((t₀ * u₁ - u₀ * t₁ : ℤ) : ℝ) * s) = -1 := by
      have : (((D * u₀ * u₁ - t₀ * t₁ : ℤ) : ℝ)) ^ 2 - D * ((t₀ * u₁ - u₀ * t₁ : ℤ) : ℝ) ^ 2 = -1 := by
        exact_mod_cast hpq
      linear_combination this - ((t₀ * u₁ - u₀ * t₁ : ℤ) : ℝ) ^ 2 * hss
    rw [heq] at hprodR
    have hp0 : ((D * u₀ * u₁ - t₀ * t₁ : ℤ) : ℝ) = 0 := by linarith
    have hp0' : D * u₀ * u₁ - t₀ * t₁ = 0 := by exact_mod_cast hp0
    rw [hp0'] at hpq
    have hq1 : D * (t₀ * u₁ - u₀ * t₁) ^ 2 = 1 := by linarith
    have hq2 : 1 ≤ (t₀ * u₁ - u₀ * t₁) ^ 2 := by
      rcases (sq_nonneg (t₀ * u₁ - u₀ * t₁)).eq_or_lt with h | h
      · rw [← h] at hq1; simp at hq1
      · exact h
    have hD1 : D = 1 := by nlinarith
    exact hsq ⟨1, by rw [hD1]; rfl⟩
  · obtain ⟨hp, hq⟩ := neg_pell_pos hD hpq hgt
    have := hmin₁ ⟨D * u₀ * u₁ - t₀ * t₁, t₀ * u₁ - u₀ * t₁, hp, hq, hpq, rfl⟩
    apply le_antisymm _ hA
    nlinarith

/-! ### Lemma 3.3 and its corollaries (pp. 292–293) -/

/-- Helper: `L`, `M` under a proper integral automorph. -/
theorem linLM_aut {a b c : ℤ} (ha : a ≠ 0) (hind : a * c - b ^ 2 < 0) {T : GL (Fin 2) ℤ}
    (hT : T ∈ Siegel.AutPlus (cform a b c)) (x : Fin 2 → ℤ) :
    linL a b c (cast (T.val *ᵥ x)) = etaOf a b c T * linL a b c (cast x) ∧
      linM a b c (cast (T.val *ᵥ x)) = (etaOf a b c T)⁻¹ * linM a b c (cast x) := by
  obtain ⟨hT1, hT2⟩ := autPlus_castM ha hT
  have hD : 0 ≤ b ^ 2 - a * c := by linarith
  obtain ⟨-, hinv, -⟩ := etaOf_data ha hind hT
  have := linL_pellMat hD hT2 (cast x)
  rw [← hT1, castM_mulVec_cast] at this
  refine ⟨?_, ?_⟩
  · rw [this.1]; rfl
  · rw [this.2.1, hinv]

/-- Helper: a nonzero integral vector has nonzero value on an anisotropic form. -/
theorem eval_ne_zero_of_aniso {a b c : ℤ} (haniso : ¬ (cform a b c).IsotropicIn ℚ) {x : Fin 2 → ℤ}
    (hx : x ≠ 0) : QuadForm.eval (cform a b c) x ≠ 0 := by
  intro h
  apply haniso
  refine ⟨fun i => (x i : ℚ), ?_, ?_⟩
  · intro h0
    apply hx
    ext i
    have := congrFun h0 i
    simpa using this
  · rw [evalIn_cform]
    have := eval_cform a b c x
    rw [h] at this
    have h' : ((0 : ℤ) : ℚ) = ((a * x 0 ^ 2 + 2 * b * x 0 * x 1 + c * x 1 ^ 2 : ℤ) : ℚ) := by rw [this]
    push_cast at h'
    linarith

/-- Helper: `L M = a f` on integral vectors. -/
theorem linL_mul_linM_int {a b c : ℤ} (hD : 0 ≤ b ^ 2 - a * c) (x : Fin 2 → ℤ) :
    linL a b c (cast x) * linM a b c (cast x) = a * ((QuadForm.eval (cform a b c) x : ℤ) : ℝ) := by
  rw [linL_mul_linM hD, val_realMat_cform, eval_cform]
  push_cast
  rfl

/-- **Lemma 3.3** (Cassels, Ch. 13, §3, p. 292): let $f = ax^2 + 2bxy + cy^2$ be classically integral, indefinite
and anisotropic, and let $T_0 \in O^+(f)$ be the matrix (3.14) of a solution $(t_0, u_0)$ of (3.13) with
$\eta_0 = t_0 + u_0\sqrt{D} > 1$. For every integral $\vec{b} \ne 0$ there is $T \in O^+(f)$ with
$$|L(T\vec{b})| \le |\eta_0\,a f(\vec{b})|^{1/2}, \qquad |M(T\vec{b})| \le |\eta_0\,a f(\vec{b})|^{1/2}.$$
Cassels takes the fundamental solution; any $\eta_0 > 1$ works (a generalization). *Erratum*:
the book prints $|\eta_0 f(\vec{b})|^{1/2}$ and writes $L(T\vec{b})M(T\vec{b}) = f(\vec{b})$
in the proof; by (3.22) the product is $af(\vec{b})$, so the factor $a$ is needed (it is $1$ in the example
$x^2 - 82y^2$). Cassels' first inequality is strict; the non-strict form is stated.

Kept beside `Cassels.Ch13.lemma_3_3` (real vectors, integral fundamental solution); the two are incomparable. -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.3, pp. 292–293"]
theorem exists_autPlus_linL_linM_le {a b c : ℤ} (hind : a * c - b ^ 2 < 0) (haniso : ¬ (cform a b c).IsotropicIn ℚ)
    {T₀ : GL (Fin 2) ℤ} (hT₀ : T₀ ∈ Siegel.AutPlus (cform a b c)) {t₀ u₀ : ℝ}
    (hpell : t₀ ^ 2 + (a * c - b ^ 2) * u₀ ^ 2 = 1) (hmat : castM T₀.val = pellMat (a : ℝ) b c t₀ u₀)
    (hη : 1 < t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) {x : Fin 2 → ℤ} (hx : x ≠ 0) :
    ∃ T ∈ Siegel.AutPlus (cform a b c),
      |linL a b c (cast (T.val *ᵥ x))| ≤
          √((t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) * |a * QuadForm.eval (cform a b c) x|) ∧
        |linM a b c (cast (T.val *ᵥ x))| ≤
          √((t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) * |a * QuadForm.eval (cform a b c) x|) := by
  have ha := ne_zero_a_of_aniso haniso
  have hD : 0 ≤ b ^ 2 - a * c := by linarith
  have hDr : (0 : ℝ) ≤ (b : ℝ) ^ 2 - a * c := by exact_mod_cast hD
  have hηT : etaOf a b c T₀ = t₀ + u₀ * √((b : ℝ) ^ 2 - a * c) := etaOf_eq ha hmat
  set η : ℝ := t₀ + u₀ * √((b : ℝ) ^ 2 - a * c) with hηdef
  have hfx := eval_ne_zero_of_aniso haniso hx
  have hLM := linL_mul_linM_int hD x
  set P : ℝ := ((|a * QuadForm.eval (cform a b c) x| : ℤ) : ℝ) with hP
  have hPeq : P = |(a : ℝ) * ((QuadForm.eval (cform a b c) x : ℤ) : ℝ)| := by
    rw [hP]; push_cast; rfl
  have hPpos : 0 < P := by
    rw [hPeq]
    exact abs_pos.mpr (mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hfx))
  have hL0 : linL a b c (cast x) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hLM
    exact hPpos.ne' (by rw [hPeq, ← hLM]; simp)
  set l : ℝ := |linL a b c (cast x)| with hl
  have hlpos : 0 < l := abs_pos.mpr hL0
  have hlm : l * |linM a b c (cast x)| = P := by
    rw [hl, ← abs_mul, hLM, hPeq]
  have hη0 : 0 < η := by linarith
  have hs : 0 < √(η * P) := Real.sqrt_pos.mpr (mul_pos hη0 hPpos)
  have hss : √(η * P) * √(η * P) = η * P := Real.mul_self_sqrt (mul_pos hη0 hPpos).le
  set s : ℝ := √(η * P) with hsdef
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (x := s / (η * l)) (y := η) (by positivity) hη
  have hTk : T₀ ^ (k + 1) ∈ Siegel.AutPlus (cform a b c) := zpow_mem hT₀ _
  refine ⟨T₀ ^ (k + 1), hTk, ?_⟩
  obtain ⟨hL, hM⟩ := linLM_aut ha hind hTk x
  rw [hL, hM, etaOf_zpow ha hind hT₀, hηT]
  have hqpos : 0 < η ^ (k + 1) := zpow_pos hη0 _
  have hqk : η ^ (k + 1) = η ^ k * η := _root_.zpow_add_one₀ hη0.ne' k
  constructor
  · rw [abs_mul, abs_of_pos hqpos, ← hl]
    have h1 : η ^ k * (η * l) ≤ s / (η * l) * (η * l) :=
      mul_le_mul_of_nonneg_right hk1 (by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at h1
    calc η ^ (k + 1) * l = η ^ k * (η * l) := by rw [hqk]; ring
      _ ≤ s := h1
  · rw [abs_mul, abs_inv, abs_of_pos hqpos, inv_mul_le_iff₀ hqpos]
    have h2 : s < η ^ (k + 1) * (η * l) := by
      have := (div_lt_iff₀ (by positivity : 0 < η * l)).mp hk2
      linarith
    have h3 : η * P < s * (η ^ (k + 1) * (η * l)) := by
      calc η * P = s * s := hss.symm
        _ < s * (η ^ (k + 1) * (η * l)) := mul_lt_mul_of_pos_left h2 hs
    have h4 : P < s * η ^ (k + 1) * l := by
      have : η * P < η * (s * η ^ (k + 1) * l) := by linarith
      exact lt_of_mul_lt_mul_left this hη0.le
    rw [← hlm] at h4
    have h5 : |linM a b c (cast x)| < s * η ^ (k + 1) :=
      lt_of_mul_lt_mul_left (by linarith) hlpos.le
    linarith

/-- **Lemma 3.3, Corollary 1** (Cassels, Ch. 13, §3, p. 293): one can determine effectively representatives of all
the orbits of representations of a given integer $e \ne 0$ by $f$. Effective form: in the setting of Lemma 3.3
($\eta_0 = t_0 + u_0\sqrt D > 1$, $D = b^2 - ac$), every integral solution of $f(\vec{x}) = e$ is moved by some
$T \in O^+(f)$ into the explicit finite box
$$|x_1| \le B_1 = \sqrt{\eta_0|ae|}/\sqrt{D}, \qquad |x_0| \le (\sqrt{\eta_0|ae|} + |b|B_1)/|a|.$$ -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.3, Cor. 1, p. 293"]
theorem exists_autPlus_rep_bounded {a b c : ℤ} (hind : a * c - b ^ 2 < 0) (haniso : ¬ (cform a b c).IsotropicIn ℚ)
    {T₀ : GL (Fin 2) ℤ} (hT₀ : T₀ ∈ Siegel.AutPlus (cform a b c)) {t₀ u₀ : ℝ}
    (hpell : t₀ ^ 2 + (a * c - b ^ 2) * u₀ ^ 2 = 1) (hmat : castM T₀.val = pellMat (a : ℝ) b c t₀ u₀)
    (hη : 1 < t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) {e : ℤ} (he : e ≠ 0) {x : Fin 2 → ℤ}
    (hx : QuadForm.eval (cform a b c) x = e) :
    ∃ T ∈ Siegel.AutPlus (cform a b c),
      |((T.val *ᵥ x) 1 : ℝ)| ≤
          √((t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) * |a * e|) / √((b : ℝ) ^ 2 - a * c) ∧
        |((T.val *ᵥ x) 0 : ℝ)| ≤
          (√((t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) * |a * e|) +
            |(b : ℝ)| * (√((t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) * |a * e|) / √((b : ℝ) ^ 2 - a * c))) / |(a : ℝ)| := by
  have ha := ne_zero_a_of_aniso haniso
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply he
    rw [← hx, eval_cform]; simp
  obtain ⟨T, hT, hL, hM⟩ := exists_autPlus_linL_linM_le hind haniso hT₀ hpell hmat hη hx0
  rw [hx] at hL hM
  refine ⟨T, hT, ?_⟩
  set B : ℝ := √((t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) * |a * e|) with hB
  have hDpos : (0 : ℝ) < (b : ℝ) ^ 2 - a * c := by
    have : (0 : ℤ) < b ^ 2 - a * c := by linarith
    exact_mod_cast this
  have hsq : 0 < √((b : ℝ) ^ 2 - a * c) := Real.sqrt_pos.mpr hDpos
  have hL' := abs_le.mp hL
  have hM' := abs_le.mp hM
  simp only [linL, linM, cast] at hL' hM'
  set sD : ℝ := √((b : ℝ) ^ 2 - a * c) with hsD
  have hY : |((T.val *ᵥ x) 1 : ℝ)| ≤ B / sD := by
    rw [le_div_iff₀ hsq]
    have : |((T.val *ᵥ x) 1 : ℝ)| * sD = |((T.val *ᵥ x) 1 : ℝ) * sD| := by
      rw [abs_mul, abs_of_pos hsq]
    rw [this, abs_le]
    constructor <;> nlinarith [hL'.1, hL'.2, hM'.1, hM'.2]
  refine ⟨hY, ?_⟩
  have hapos : 0 < |(a : ℝ)| := abs_pos.mpr (by exact_mod_cast ha)
  rw [le_div_iff₀ hapos, ← abs_mul]
  have h1 : |((T.val *ᵥ x) 1 : ℝ)| ≤ B / sD := hY
  have h2 : |(b : ℝ) * ((T.val *ᵥ x) 1 : ℝ)| ≤ |(b : ℝ)| * (B / sD) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h3 := abs_le.mp h2
  rw [abs_le]
  constructor <;> nlinarith [hL'.1, hL'.2, hM'.1, hM'.2, h3.1, h3.2]

/-- **Lemma 3.3, Corollary 2** (Cassels, Ch. 13, §3, p. 293): one can determine effectively whether two classically
integral binary forms are equivalent. Effective form, for $f$ indefinite anisotropic as in Lemma 3.3 (the remaining
cases are "trivial"): if $g(\vec{x}) = f(P\vec{x})$ for some $P \in \mathrm{GL}_2(\mathbb{Z})$, then there is such a $P$
whose first column $\vec{b} = P\vec{e}_0$ (a representation of $e = g(\vec{e}_0)$) lies in the box of Corollary 1; for
each such $\vec{b}$ it is a finite check whether a second column exists. -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.3, Cor. 2, p. 293"]
theorem exists_equiv_bounded_column {a b c : ℤ} (hind : a * c - b ^ 2 < 0) (haniso : ¬ (cform a b c).IsotropicIn ℚ)
    {T₀ : GL (Fin 2) ℤ} (hT₀ : T₀ ∈ Siegel.AutPlus (cform a b c)) {t₀ u₀ : ℝ}
    (hpell : t₀ ^ 2 + (a * c - b ^ 2) * u₀ ^ 2 = 1) (hmat : castM T₀.val = pellMat (a : ℝ) b c t₀ u₀)
    (hη : 1 < t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) {g : BinQF} {P : GL (Fin 2) ℤ}
    (hP : ∀ x, QuadForm.eval (cform a b c) (P.val *ᵥ x) = QuadForm.eval g x) :
    ∃ P' : GL (Fin 2) ℤ, (∀ x, QuadForm.eval (cform a b c) (P'.val *ᵥ x) = QuadForm.eval g x) ∧
      |(P'.val 1 0 : ℝ)| ≤
          √((t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) * |a * g.a|) / √((b : ℝ) ^ 2 - a * c) ∧
        |(P'.val 0 0 : ℝ)| ≤
          (√((t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) * |a * g.a|) +
            |(b : ℝ)| * (√((t₀ + u₀ * √((b : ℝ) ^ 2 - a * c)) * |a * g.a|) / √((b : ℝ) ^ 2 - a * c))) /
            |(a : ℝ)| := by
  have ha := ne_zero_a_of_aniso haniso
  have col0 : ∀ (M : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2), (M *ᵥ Pi.single 0 1) i = M i 0 := by
    intro M i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hga : QuadForm.eval g (Pi.single 0 1) = g.a := by
    simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, BinQF.a, Pi.single_apply]
  set x : Fin 2 → ℤ := P.val *ᵥ Pi.single 0 1 with hxdef
  have hx : QuadForm.eval (cform a b c) x = g.a := by rw [hxdef, hP, hga]
  have hx0 : x ≠ 0 := by
    intro h0
    have h1 : (P⁻¹).val *ᵥ x = Pi.single 0 1 := by
      rw [hxdef, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    have := congrFun h1 0
    simp at this
  have he : g.a ≠ 0 := by rw [← hx]; exact eval_ne_zero_of_aniso haniso hx0
  obtain ⟨T, hT, h1, h2⟩ := exists_autPlus_rep_bounded hind haniso hT₀ hpell hmat hη he hx
  refine ⟨T * P, ?_, ?_⟩
  · intro y
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, (Siegel.mem_autPlus_iff.mp hT).1 (P.val *ᵥ y), hP]
  · have e1 : (T * P).val 1 0 = (T.val *ᵥ x) 1 := by
      rw [hxdef, Matrix.mulVec_mulVec, col0, Units.val_mul]
    have e0 : (T * P).val 0 0 = (T.val *ᵥ x) 0 := by
      rw [hxdef, Matrix.mulVec_mulVec, col0, Units.val_mul]
    rw [e1, e0]
    exact ⟨h1, h2⟩

/-! ### The example $a^2 - 82b^2 = 2$ (p. 293) -/

/-- Helper: descent for `a² - 82 b² = ±2` along the automorph `(9, 1)` of `t² - 82u² = -1`. -/
theorem no_sol_82_aux : ∀ n : ℕ, ∀ a b : ℤ, b.natAbs = n → ∀ s : ℤ, (s = 2 ∨ s = -2) →
    a ^ 2 - 82 * b ^ 2 ≠ s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn s hs hab
    have hA : |a| ^ 2 - 82 * |b| ^ 2 = s := by rw [sq_abs, sq_abs]; exact hab
    have hA0 : 0 ≤ |a| := abs_nonneg a
    have hB0 : 0 ≤ |b| := abs_nonneg b
    have hBn : |b|.natAbs = n := by rw [Int.natAbs_abs]; exact hn
    clear hab hn
    generalize |a| = A at *
    generalize |b| = B at *
    rcases hB0.eq_or_lt with h0 | hpos
    · subst h0
      rcases le_or_gt A 1 with h | h <;> rcases hs with rfl | rfl <;> nlinarith
    · have h1 : 8 * B < A := by
        by_contra hc; rw [not_lt] at hc
        rcases hs with rfl | rfl <;> nlinarith
      have h2 : A < 10 * B := by
        by_contra hc; rw [not_lt] at hc
        rcases hs with rfl | rfl <;> nlinarith
      have hlt : (9 * B - A).natAbs < n := by omega
      refine ih _ hlt (9 * A - 82 * B) (9 * B - A) rfl (-s) (by rcases hs with rfl | rfl <;> simp) ?_
      linear_combination (-1 : ℤ) * hA

/-- **Example** (Cassels, Ch. 13, §3, p. 293): there are no integers $a, b$ with $a^2 - 82b^2 = 2$ (nor with
$a^2 - 82b^2 = -2$), although the equation is soluble in every $\mathbb{Z}_p$. Cassels' proof: $t_1 = 9$, $u_1 = 1$
solves $t^2 - 82u^2 = -1$, and Lemma 3.3 with $\eta_1 = 9 + \sqrt{82}$ in place of $\eta_0$ (for $\pm 2$ together)
bounds $|b|\sqrt{82}$ by $(2\eta_1)^{1/2}$, forcing $b = 0$. -/
@[kb "cassels1978" "Ch. 13, §3, Example, p. 293 (a² − 82b² = ±2 has no integral solution)"]
theorem not_exists_sq_sub_82_sq (s : ℤ) (hs : s = 2 ∨ s = -2) : ¬ ∃ a b : ℤ, a ^ 2 - 82 * b ^ 2 = s := by
  rintro ⟨a, b, h⟩
  exact no_sol_82_aux _ a b rfl s hs h

/-- Helper: the Gram form `-9X² - 164XY - 738Y²` of the 3-neighbour of `x² - 82y²` at `v = (1, 1)`. -/
def g82 : BinQF := BinQF.mk (-9) (-164) (-738)

/-- Helper: the neighbour certificate for `g82` as a 3-neighbour of `x² - 82y²`. -/
def cert82 : Siegel.Kneser.NbCert 2 where
  v := ![1, 1]
  G := !![1, 0; 1, 9]
  k := ![1, 0]
  w := ![2, 0]
  A := !![-9, 984; 1, -109]
  cW := ![18, -2]
  cV := ![1, 0]
  K := !![9, 0; -1, 1]

/-- Helper: the certificate is valid. -/
theorem cert82_valid : cert82.Valid (cform 1 0 (-82)) g82 3 := by decide

/-- Helper: `g82` is integrally equivalent to `2x² - 41y²` (via `[[4, 41], [1, 10]]`). -/
theorem intEquiv_g82 : Siegel.IntEquiv (cform 2 0 (-41)) g82 :=
  Siegel.Kneser.IsoCert.intEquiv (c := ⟨!![4, 41; 1, 10], !![-10, 41; 1, -4]⟩) (by decide)

/-- **Example, the forms** (Cassels, Ch. 13, §3, p. 293): $x^2 - 82y^2$ and $2x^2 - 41y^2$ are in the same genus
(`Siegel.SameGenus`) but are not integrally equivalent. -/
@[kb "cassels1978" "Ch. 13, §3, Example, p. 293 (x² − 82y² and 2x² − 41y²: same genus, not equivalent)"]
theorem sameGenus_not_intEquiv_82 :
    Siegel.SameGenus (cform 1 0 (-82)) (cform 2 0 (-41)) ∧
      ¬ Siegel.IntEquiv (cform 1 0 (-82)) (cform 2 0 (-41)) := by
  refine ⟨?_, ?_⟩
  · have hdet : ¬ ((3 : ℕ) : ℤ) ∣ (cform 1 0 (-82)).hessian.det := by
      rw [binqf_det]; simp [cform]
    have h1 : Siegel.SameGenus (cform 1 0 (-82)) g82 :=
      Siegel.Kneser.NbCert.sameGenus (p := 3) (c := cert82) (by norm_num) hdet cert82_valid
    exact h1.trans intEquiv_g82.sameGenus.symm
  rintro ⟨g, hg⟩
  have h := hg ![1, 0]
  rw [eval_cform, eval_cform] at h
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  exact not_exists_sq_sub_82_sq 2 (Or.inl rfl) ⟨g.val 0 0, g.val 1 0, by linarith⟩

end QuadFormsKB.Reduction
