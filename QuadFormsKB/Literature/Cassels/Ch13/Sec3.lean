import Mathlib
import QuadFormsKB.Citation

/-!
# Cassels, Chapter 13, §3: automorphs of binary forms, Pell's equation

Cassels, *Rational Quadratic Forms* (1978), Ch. 13 (*Automorphs of integral forms*), §3, pp. 289–295.

**Setting.** A binary form is $f(x,y) = ax^{2} + 2bxy + cy^{2}$ (`binF`, Cassels (3.5)) with matrix
$F = \begin{pmatrix}a&b\\b&c\end{pmatrix}$ and determinant $d(f) = ac - b^{2}$ (3.7); *classically integral* means
$a,b,c \in \mathbb Z$. A $2\times2$ matrix $T$ is an automorph (`IsBinAut`) if $f(T\vec{x}) = f(\vec{x})$; proper if
$\det T = 1$. We write $D = b^{2} - ac = -d(f)$, so Pell's equation (3.13) $t^{2} + du^{2} = 1$ is $t^{2} - Du^{2} = 1$
(Mathlib's `Pell.Solution₁ D`).

**What is proved.**
* Lemma 3.1 (`lemma_3_1_proper`, `lemma_3_1_improper`): for the normal form $xy$ (3.1), $O^{+}_{\mathbb R} \cong
  \mathbb R^{\times}$ via $s \mapsto \operatorname{diag}(s,s^{-1})$, improper automorphs exist and have order $2$.
  (Special case: Cassels reduces an arbitrary indefinite real binary form to $xy$ by a real equivalence.)
* Lemma 3.2 (`lemma_3_2_i`, `lemma_3_2_ii`): a regular isotropic integral form has only $\pm I$ as proper integral
  automorphs and represents each $e \ne 0$ only finitely often.
* Theorem 3.1 (`proper_eq_autMat`, `thm_3_1`), properly primitive case ($\gcd(a,2b,c) = 1$, (3.15a)): the proper
  integral automorphs are the $T(t,u)$ of (3.14) with $t^{2} - Du^{2} = 1$, and they are $\pm T_1^{\nu}$ with $T_1$ of
  infinite order. The improperly primitive case (3.15b), with half-integral $t,u$, is not formalized.
* Corollary to Theorem 3.1 (`thm_3_1_cor`): a solution of $t^{2} - Du^{2} = -1$ gives an improper equivalence of $f$ with
  $-f$ (first sentence; the comparison $\eta_1 = \eta_0^{2}$ is not formalized).
* Lemma 3.3 (`lemma_3_3`): every orbit of a real vector under $O^{+}(f)$ meets the region
  $\lvert L\rvert, \lvert M\rvert \le \lvert\eta_0 LM\rvert^{1/2}$.
* Lemma 3.4 (`lemma_3_4`) and Theorem 3.2 (`thm_3_2`): improper integral automorphs and the normal forms $b = 0$,
  $2b = a$.
* Lemma 3.5 (`lemma_3_5`): finiteness of classically reduced forms of given determinant $d < 0$.

**Proof notes.** Theorem 3.1 is proved without Hermite reduction or Theorem 2.2: the linear relations of the proof
(`proper_rel`) give (3.14); $(t,u) \mapsto T(t,u)$ is a group homomorphism from Pell solutions (`pellHom`, `autMat_mul`)
and Mathlib's structure theorem for Pell's equation (`Pell.IsFundamental.eq_zpow_or_neg_zpow`) gives the generator.
Lemma 3.2 (i) uses that $D$ is a nonzero square, so $T$'s trace $s$ satisfies $s^{2} - 4 = \square$, forcing $s = \pm 2$.
In Theorem 3.2, an improper automorph of a regular form has trace $0$ (`improper_rel`), so $T^{2} = I$ and Lemma 3.4
applies.

**Conventions.** Indices are 0-based: Cassels' $T = \begin{pmatrix}l&m\\n&r\end{pmatrix}$ is
$\begin{pmatrix}T_{00}&T_{01}\\T_{10}&T_{11}\end{pmatrix}$. "Primitive" in the sense of (3.10) is passed as a Bézout
relation $ax + 2by + cz = 1$.
-/

open Matrix

namespace QuadFormsKB.Cassels.Ch13

/-- The binary form $f(x,y) = ax^{2} + 2bxy + cy^{2}$ with matrix $\begin{pmatrix}a&b\\b&c\end{pmatrix}$ (Cassels (3.5)–(3.6)); its determinant is $d(f) = ac - b^{2}$ (3.7). -/
@[kb "cassels1978" "Ch. 13, §3, (3.5)–(3.7), p. 290"]
def binF {R : Type*} [CommRing R] (a b c x y : R) : R := a * x ^ 2 + 2 * b * x * y + c * y ^ 2

/-- $T = \begin{pmatrix}T_{00}&T_{01}\\T_{10}&T_{11}\end{pmatrix}$ is an *automorph* of $f = ax^{2}+2bxy+cy^{2}$: $f(T\vec{x}) = f(\vec{x})$ for all $\vec{x} = (x,y)$, where $T\vec{x} = (T_{00}x + T_{01}y,\ T_{10}x + T_{11}y)$. It is *proper* if $\det T = 1$ and *improper* if $\det T = -1$. -/
def IsBinAut {R : Type*} [CommRing R] (a b c : R) (T : Matrix (Fin 2) (Fin 2) R) : Prop :=
  ∀ x y, binF a b c (T 0 0 * x + T 0 1 * y) (T 1 0 * x + T 1 1 * y) = binF a b c x y

/-- Substitution formula: $f(lx+my,\ nx+ry)$ expanded in the coefficients of $x^{2}$, $xy$, $y^{2}$. -/
theorem binF_subst {R : Type*} [CommRing R] (a b c l m n r x y : R) :
    binF a b c (l * x + m * y) (n * x + r * y) =
      (a * l ^ 2 + 2 * b * l * n + c * n ^ 2) * x ^ 2
      + 2 * (a * l * m + b * (l * r + m * n) + c * n * r) * x * y
      + (a * m ^ 2 + 2 * b * m * r + c * r ^ 2) * y ^ 2 := by
  unfold binF; ring

/-- Over an integral domain of characteristic $0$, $T$ is an automorph of $f$ if and only if $f(T\vec{e}_0) = a$, $f(T\vec{e}_1) = c$ and the polar form of $T\vec{e}_0, T\vec{e}_1$ is $b$ (i.e. $T^{\mathsf T}FT = F$). -/
theorem isBinAut_iff {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (a b c : R)
    (T : Matrix (Fin 2) (Fin 2) R) :
    IsBinAut a b c T ↔
      a * T 0 0 ^ 2 + 2 * b * T 0 0 * T 1 0 + c * T 1 0 ^ 2 = a ∧
      a * T 0 1 ^ 2 + 2 * b * T 0 1 * T 1 1 + c * T 1 1 ^ 2 = c ∧
      a * T 0 0 * T 0 1 + b * (T 0 0 * T 1 1 + T 0 1 * T 1 0) + c * T 1 0 * T 1 1 = b := by
  constructor
  · intro h
    have h1 := h 1 0
    have h2 := h 0 1
    have h3 := h 1 1
    simp only [binF_subst] at h1 h2 h3
    unfold binF at h1 h2 h3
    refine ⟨by linear_combination h1, by linear_combination h2, ?_⟩
    have : (2 : R) * (a * T 0 0 * T 0 1 + b * (T 0 0 * T 1 1 + T 0 1 * T 1 0) + c * T 1 0 * T 1 1 - b) = 0 := by
      linear_combination h3 - h1 - h2
    have h2ne : (2 : R) ≠ 0 := two_ne_zero
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2ne)
  · rintro ⟨h1, h2, h3⟩ x y
    rw [binF_subst, h1, h2, h3]; unfold binF; ring

/-- For a proper automorph $T = \begin{pmatrix}l&m\\n&r\end{pmatrix}$ ($\det T = 1$) of $f$: $a(l-r) + 2bn = 0$, $am + cn = 0$, $c(r-l) + 2bm = 0$ (the linear system in the proof of Theorem 3.1, from $FT = (T^{\mathsf T})^{-1}F$). -/
theorem proper_rel {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {a b c : R}
    {T : Matrix (Fin 2) (Fin 2) R} (hT : IsBinAut a b c T) (hdet : T.det = 1) :
    a * (T 0 0 - T 1 1) + 2 * b * T 1 0 = 0 ∧ a * T 0 1 + c * T 1 0 = 0 ∧
      c * (T 1 1 - T 0 0) + 2 * b * T 0 1 = 0 := by
  obtain ⟨E1, E2, E3⟩ := (isBinAut_iff a b c T).1 hT
  rw [Matrix.det_fin_two] at hdet
  refine ⟨?_, ?_, ?_⟩
  · linear_combination T 1 1 * E1 - T 1 0 * E3 - (a * T 0 0 + b * T 1 0) * hdet
  · linear_combination T 1 1 * E3 - T 1 0 * E2 - (a * T 0 1 + b * T 1 1) * hdet
  · linear_combination -(T 0 1) * E3 + T 0 0 * E2 - (b * T 0 1 + c * T 1 1) * hdet


/-- For an improper automorph $T$ ($\det T = -1$) of $f$: $a\operatorname{tr}T = c\operatorname{tr}T = 2b\operatorname{tr}T = 0$; so a regular form has only improper automorphs of trace $0$. -/
theorem improper_rel {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {a b c : R}
    {T : Matrix (Fin 2) (Fin 2) R} (hT : IsBinAut a b c T) (hdet : T.det = -1) :
    a * (T 0 0 + T 1 1) = 0 ∧ c * (T 0 0 + T 1 1) = 0 ∧ 2 * b * (T 0 0 + T 1 1) = 0 := by
  obtain ⟨E1, E2, E3⟩ := (isBinAut_iff a b c T).1 hT
  rw [Matrix.det_fin_two] at hdet
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -(T 1 1) * E1 + T 1 0 * E3 + (a * T 0 0 + b * T 1 0) * hdet
  · linear_combination T 0 1 * E3 - T 0 0 * E2 + (b * T 0 1 + c * T 1 1) * hdet
  · linear_combination -(T 1 1) * E3 + T 1 0 * E2 + T 0 1 * E1 - T 0 0 * E3
      + (a * T 0 1 + b * T 1 1 + b * T 0 0 + c * T 1 0) * hdet

/-- The matrix $T(t,u) = \begin{pmatrix}t-bu&-cu\\au&t+bu\end{pmatrix}$ of Cassels (3.14). -/
@[kb "cassels1978" "Ch. 13, §3, (3.14), p. 291"]
def autMat {R : Type*} [CommRing R] (a b c t u : R) : Matrix (Fin 2) (Fin 2) R :=
  !![t - b * u, -c * u; a * u, t + b * u]

/-- $f(T(t,u)\vec{x}) = (t^{2} - Du^{2})f(\vec{x})$ with $D = b^{2}-ac = -d(f)$. -/
theorem binF_autMat {R : Type*} [CommRing R] (a b c t u x y : R) :
    binF a b c ((t - b * u) * x + (-c * u) * y) ((a * u) * x + (t + b * u) * y) =
      (t ^ 2 - (b ^ 2 - a * c) * u ^ 2) * binF a b c x y := by
  unfold binF; ring

/-- $T(t,u)T(t',u') = T(tt'+Duu',\ tu'+ut')$: the matrices (3.14) multiply like the numbers $t + u\sqrt{D}$. -/
theorem autMat_mul {R : Type*} [CommRing R] (a b c t u t' u' : R) :
    autMat a b c t u * autMat a b c t' u' =
      autMat a b c (t * t' + (b ^ 2 - a * c) * (u * u')) (t * u' + u * t') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [autMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- $\det T(t,u) = t^{2} - Du^{2}$, $D = b^{2} - ac$. -/
theorem det_autMat {R : Type*} [CommRing R] (a b c t u : R) :
    (autMat a b c t u).det = t ^ 2 - (b ^ 2 - a * c) * u ^ 2 := by
  simp [autMat, Matrix.det_fin_two]; ring


/-- If $t^{2} - Du^{2} = 1$ then $T(t,u)$ is a (proper) automorph of $f$: the converse half of (3.14). -/
theorem isBinAut_autMat {R : Type*} [CommRing R] {a b c t u : R}
    (h : t ^ 2 - (b ^ 2 - a * c) * u ^ 2 = 1) : IsBinAut a b c (autMat a b c t u) := by
  intro x y
  have := binF_autMat a b c t u x y
  rw [h, one_mul] at this
  simpa [autMat] using this

/-- **Theorem 3.1, (3.14)–(3.15a)**: if $f = ax^{2}+2bxy+cy^{2}$ is integral and properly primitive ($\gcd(a,2b,c) = 1$, written as a Bézout relation $ax + 2by + cz = 1$) with $a \ne 0$, every proper integral automorph is $T(t,u)$ for integers $t, u$ with $t^{2} - Du^{2} = 1$, $D = b^{2}-ac$. -/
@[kb "cassels1978" "Ch. 13, §3, Thm. 3.1, (3.14)–(3.15), pp. 291–292 (properly primitive case)"]
theorem proper_eq_autMat {a b c : ℤ} (hprim : ∃ x y z : ℤ, a * x + 2 * b * y + c * z = 1)
    (ha : a ≠ 0) {T : Matrix (Fin 2) (Fin 2) ℤ} (hT : IsBinAut a b c T) (hdet : T.det = 1) :
    ∃ t u : ℤ, t ^ 2 - (b ^ 2 - a * c) * u ^ 2 = 1 ∧ T = autMat a b c t u := by
  obtain ⟨R1, R2, R3⟩ := proper_rel hT hdet
  obtain ⟨x, y, z, hxyz⟩ := hprim
  set u := T 1 0 * x - (T 0 0 - T 1 1) * y - T 0 1 * z with hu
  have hn : T 1 0 = a * u := by
    rw [hu]; linear_combination (-(T 1 0)) * hxyz + y * R1 + z * R2
  have hm : T 0 1 = -c * u := by
    apply mul_left_cancel₀ ha
    linear_combination R2 - c * hn
  have hl : T 0 0 - T 1 1 = -2 * b * u := by
    apply mul_left_cancel₀ ha
    linear_combination R1 - 2 * b * hn
  have hT' : T = autMat a b c (T 1 1 - b * u) u := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [autMat]
    · linear_combination hl
    · rw [hm]; ring
    · exact hn
  refine ⟨T 1 1 - b * u, u, ?_, hT'⟩
  rw [← det_autMat, ← hT', hdet]

/-- The group homomorphism $(t,u) \mapsto T(t,u)$ from the solutions of Pell's equation $t^{2} - Du^{2} = 1$ (Mathlib's `Pell.Solution₁`, $D = b^{2}-ac$) to $SL_2(\mathbb Z)$. -/
def pellHom (a b c : ℤ) : Pell.Solution₁ (b ^ 2 - a * c) →* Matrix.SpecialLinearGroup (Fin 2) ℤ where
  toFun s := ⟨autMat a b c s.x s.y, by rw [det_autMat]; exact s.prop⟩
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [autMat]
  map_mul' s s' := by
    apply Subtype.ext
    show autMat a b c (s * s').x (s * s').y = autMat a b c s.x s.y * autMat a b c s'.x s'.y
    rw [autMat_mul, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]

/-- The matrix of `pellHom a b c s` is $T(s_x, s_y)$. -/
theorem coe_pellHom (a b c : ℤ) (s : Pell.Solution₁ (b ^ 2 - a * c)) :
    ((pellHom a b c s : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
      = autMat a b c s.x s.y := rfl

/-- $T(-t,-u) = -T(t,u)$. -/
theorem pellHom_neg (a b c : ℤ) (s : Pell.Solution₁ (b ^ 2 - a * c)) :
    pellHom a b c (-s) = -pellHom a b c s := by
  ext i j
  simp only [coe_pellHom, Matrix.SpecialLinearGroup.coe_neg, Pell.Solution₁.x_neg,
    Pell.Solution₁.y_neg]
  fin_cases i <;> fin_cases j <;> simp [autMat] <;> ring

/-- For $a \ne 0$ the map $(t,u) \mapsto T(t,u)$ is injective. -/
theorem pellHom_injective {a b c : ℤ} (ha : a ≠ 0) : Function.Injective (pellHom a b c) := by
  intro s s' h
  have h' := congrArg (fun T : Matrix.SpecialLinearGroup (Fin 2) ℤ => (T : Matrix (Fin 2) (Fin 2) ℤ)) h
  simp only [coe_pellHom] at h'
  have h10 := congrFun (congrFun h' 1) 0
  have h11 := congrFun (congrFun h' 1) 1
  simp [autMat] at h10 h11
  rcases h10 with h10 | h10
  · exact Pell.Solution₁.ext (by rw [h10] at h11; linarith) h10
  · exact absurd h10 ha

/-- If $D = b^{2}-ac$ is not a square then $a \ne 0$. -/
theorem ne_zero_of_not_isSquare {a b c : ℤ} (hsq : ¬ IsSquare (b ^ 2 - a * c)) : a ≠ 0 := by
  rintro rfl; exact hsq ⟨b, by ring⟩

/-- **Theorem 3.1** (properly primitive case): let $f = ax^{2}+2bxy+cy^{2}$ be integral, properly primitive ($\gcd(a,2b,c)=1$), indefinite ($D = b^{2}-ac > 0$) and anisotropic ($D$ not a square). Then there is a proper integral automorph $T_1$ of infinite order such that the proper integral automorphs of $f$ are exactly the $\pm T_1^{\nu}$, $\nu \in \mathbb Z$. ($T_1 = T(t_0,u_0)$ for the fundamental solution of Pell's equation $t^{2} - Du^{2} = 1$.) -/
@[kb "cassels1978" "Ch. 13, §3, Thm. 3.1, pp. 291–292 (properly primitive case)"]
theorem thm_3_1 {a b c : ℤ} (hprim : ∃ x y z : ℤ, a * x + 2 * b * y + c * z = 1)
    (hD : 0 < b ^ 2 - a * c) (hsq : ¬ IsSquare (b ^ 2 - a * c)) :
    ∃ T₁ : Matrix.SpecialLinearGroup (Fin 2) ℤ, (∀ ν : ℤ, T₁ ^ ν = 1 → ν = 0) ∧
      ∀ T : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        IsBinAut a b c (T : Matrix (Fin 2) (Fin 2) ℤ) ↔ ∃ ν : ℤ, T = T₁ ^ ν ∨ T = -(T₁ ^ ν) := by
  have ha := ne_zero_of_not_isSquare hsq
  obtain ⟨a₁, h₁⟩ := Pell.IsFundamental.exists_of_not_isSquare hD hsq
  refine ⟨pellHom a b c a₁, ?_, ?_⟩
  · intro ν hν
    rw [← map_zpow, ← (pellHom a b c).map_one] at hν
    exact (h₁.zpow_eq_one_iff ν).1 (pellHom_injective ha hν)
  · intro T
    constructor
    · intro hT
      obtain ⟨t, u, htu, hTe⟩ := proper_eq_autMat hprim ha hT T.prop
      have hs : pellHom a b c (Pell.Solution₁.mk t u htu) = T := by
        ext i j; rw [coe_pellHom, hTe]; simp
      obtain ⟨ν, hν | hν⟩ := h₁.eq_zpow_or_neg_zpow (Pell.Solution₁.mk t u htu)
      · exact ⟨ν, Or.inl (by rw [← hs, hν, map_zpow])⟩
      · exact ⟨ν, Or.inr (by rw [← hs, hν, pellHom_neg, map_zpow])⟩
    · rintro ⟨ν, hν | hν⟩
      · rw [hν, ← map_zpow, coe_pellHom]; exact isBinAut_autMat (a₁ ^ ν).prop
      · rw [hν, ← map_zpow, ← pellHom_neg, coe_pellHom]; exact isBinAut_autMat (-a₁ ^ ν).prop


/-- **Corollary to Theorem 3.1**, first statement: if $t^{2} - Du^{2} = -1$ then $T(t,u)$ has determinant $-1$ and $f(T(t,u)\vec{x}) = -f(\vec{x})$, i.e. it is an improper equivalence of $f$ with $-f$. -/
@[kb "cassels1978" "Ch. 13, §3, Cor. to Thm. 3.1, p. 292"]
theorem thm_3_1_cor {R : Type*} [CommRing R] {a b c t u : R}
    (h : t ^ 2 - (b ^ 2 - a * c) * u ^ 2 = -1) :
    (autMat a b c t u).det = -1 ∧ ∀ x y : R,
      binF a b c (autMat a b c t u 0 0 * x + autMat a b c t u 0 1 * y)
        (autMat a b c t u 1 0 * x + autMat a b c t u 1 1 * y) = -binF a b c x y := by
  refine ⟨by rw [det_autMat, h], fun x y => ?_⟩
  have := binF_autMat a b c t u x y
  rw [h] at this
  simpa [autMat] using this

/-- If $f = ax^{2}+2bxy+cy^{2}$ (integral) has a nontrivial integral zero, then $D = b^{2}-ac$ is a square. -/
theorem isSquare_of_isotropic {a b c p q : ℤ} (hpq : p ≠ 0 ∨ q ≠ 0) (hf : binF a b c p q = 0) :
    IsSquare (b ^ 2 - a * c) := by
  by_cases hq : q = 0
  · subst hq
    have hp := hpq.resolve_right (by simp)
    have ha : a = 0 := by
      unfold binF at hf; simp at hf; tauto
    exact ⟨b, by rw [ha]; ring⟩
  · have key : (a * p + b * q) ^ 2 = (b ^ 2 - a * c) * q ^ 2 := by
      unfold binF at hf; linear_combination a * hf
    have hdvd : q ^ 2 ∣ (a * p + b * q) ^ 2 := ⟨b ^ 2 - a * c, by rw [key]; ring⟩
    obtain ⟨k, hk⟩ := (Int.pow_dvd_pow_iff two_ne_zero).1 hdvd
    refine ⟨k, ?_⟩
    have : (b ^ 2 - a * c) * q ^ 2 = (k * k) * q ^ 2 := by rw [← key, hk]; ring
    exact mul_right_cancel₀ (pow_ne_zero 2 hq) this

/-- **Lemma 3.2 (i)**: the only proper integral automorphs of a regular ($ac - b^{2} \ne 0$) isotropic integral binary form are $\pm I$. -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.2 (i), p. 290"]
theorem lemma_3_2_i {a b c : ℤ} (hreg : a * c - b ^ 2 ≠ 0)
    (hiso : ∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧ binF a b c p q = 0)
    {T : Matrix (Fin 2) (Fin 2) ℤ} (hT : IsBinAut a b c T) (hdet : T.det = 1) :
    T = 1 ∨ T = -1 := by
  obtain ⟨p, q, hpq, hf⟩ := hiso
  obtain ⟨k, hk⟩ := isSquare_of_isotropic hpq hf
  have hk0 : k ≠ 0 := by rintro rfl; apply hreg; linear_combination -hk
  obtain ⟨R1, R2, R3⟩ := proper_rel hT hdet
  have hdet' := hdet
  rw [Matrix.det_fin_two] at hdet'
  set l := T 0 0
  set m := T 0 1
  set n := T 1 0
  set r := T 1 1
  have hn : n = 0 := by
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by rintro rfl; apply hreg; rw [ha]; ring
      rw [ha] at R1
      have : 2 * b * n = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by omega)
      · exact h
    · have key : (a * (l + r)) ^ 2 - 4 * a ^ 2 = (2 * n * k) ^ 2 := by
        linear_combination (a * (l - r) - 2 * b * n) * R1 + 4 * a * n * R2 + 4 * n ^ 2 * hk
          + 4 * a ^ 2 * hdet'
      have hdvd : a ^ 2 ∣ (2 * n * k) ^ 2 := ⟨(l + r) ^ 2 - 4, by rw [← key]; ring⟩
      obtain ⟨w, hw⟩ := (Int.pow_dvd_pow_iff two_ne_zero).1 hdvd
      have hsq : (l + r) ^ 2 - 4 = w ^ 2 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 ha)
        linear_combination key + (2 * n * k + a * w) * hw
      have hw0 : w = 0 := by
        set S := |l + r|
        set Q := |w|
        have hS : 0 ≤ S := abs_nonneg _
        have hQ : 0 ≤ Q := abs_nonneg _
        have hSQ : S ^ 2 - 4 = Q ^ 2 := by simp only [S, Q, sq_abs]; exact hsq
        have h1 : Q < S := by nlinarith
        have h2 : Q ≤ S - 1 := by omega
        have h3 : S ≤ 2 := by nlinarith
        have h4 : Q = 0 := by nlinarith
        exact abs_eq_zero.1 h4
      rw [hw0] at hw
      have : 2 * n * k = 0 := by simpa using hw
      rcases mul_eq_zero.1 this with h | h
      · omega
      · exact absurd h hk0
  simp only [hn, mul_zero, sub_zero, add_zero] at hdet' R2 R1
  have hlr : l * r = 1 := by linarith
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h; push Not at h; apply hreg; rw [h.1, h.2]; ring
  have hm : m = 0 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hlr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    · rw [h1, h2] at R3
      rcases hab with ha | hb
      · exact (mul_eq_zero.1 R2).resolve_left ha
      · have : 2 * b * m = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · omega
        · exact h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hlr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; ext i j; fin_cases i <;> fin_cases j <;> simp [l, m, n, r] at * <;> assumption
  · right; ext i j; fin_cases i <;> fin_cases j <;> simp [l, m, n, r] at * <;> assumption


/-- For $N \ne 0$ there are only finitely many integer pairs $(u,v)$ with $uv = N$. -/
theorem finite_mul_eq {N : ℤ} (hN : N ≠ 0) : {p : ℤ × ℤ | p.1 * p.2 = N}.Finite := by
  apply ((Set.finite_Icc (-|N|) |N|).prod (Set.finite_Icc (-|N|) |N|)).subset
  rintro ⟨u, v⟩ (h : u * v = N)
  have hu : |u| ≤ |N| := by
    rw [← h, abs_mul]
    have : v ≠ 0 := by rintro rfl; simp at h; exact hN h.symm
    have : 1 ≤ |v| := Int.one_le_abs this
    nlinarith [abs_nonneg u]
  have hv : |v| ≤ |N| := by
    rw [← h, abs_mul]
    have : u ≠ 0 := by rintro rfl; simp at h; exact hN h.symm
    have : 1 ≤ |u| := Int.one_le_abs this
    nlinarith [abs_nonneg v]
  exact ⟨abs_le.1 hu, abs_le.1 hv⟩

/-- **Lemma 3.2 (ii)**: for a regular isotropic integral binary form $f$ and an integer $e \ne 0$, there are only finitely many $(x,y) \in \mathbb Z^{2}$ with $f(x,y) = e$. -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.2 (ii), p. 290"]
theorem lemma_3_2_ii {a b c : ℤ} (hreg : a * c - b ^ 2 ≠ 0)
    (hiso : ∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧ binF a b c p q = 0) {e : ℤ} (he : e ≠ 0) :
    {v : ℤ × ℤ | binF a b c v.1 v.2 = e}.Finite := by
  obtain ⟨p, q, hpq, hf⟩ := hiso
  obtain ⟨k, hk⟩ := isSquare_of_isotropic hpq hf
  have hk0 : k ≠ 0 := by rintro rfl; apply hreg; linear_combination -hk
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by rintro rfl; apply hreg; rw [ha]; ring
    let φ : ℤ × ℤ → ℤ × ℤ := fun v => (v.2, 2 * b * v.1 + c * v.2)
    have hφ : Function.Injective φ := by
      rintro ⟨x, y⟩ ⟨x', y'⟩ h
      simp only [φ, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      have : 2 * b * (x - x') = 0 := by linarith
      have hx : x - x' = 0 := (mul_eq_zero.1 this).resolve_left (by omega)
      simp only [Prod.mk.injEq, and_true]; linarith
    apply ((finite_mul_eq he).preimage hφ.injOn).subset
    rintro ⟨x, y⟩ (h : binF a b c x y = e)
    show y * (2 * b * x + c * y) = e
    rw [← h]; unfold binF; rw [ha]; ring
  · let φ : ℤ × ℤ → ℤ × ℤ := fun v => (a * v.1 + b * v.2 - k * v.2, a * v.1 + b * v.2 + k * v.2)
    have hφ : Function.Injective φ := by
      rintro ⟨x, y⟩ ⟨x', y'⟩ h
      simp only [φ, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have : 2 * k * (y - y') = 0 := by linarith
      have hy : y - y' = 0 := (mul_eq_zero.1 this).resolve_left (by omega)
      have : a * (x - x') = 0 := by
        have : y = y' := by linarith
        subst this; linarith
      have hx : x - x' = 0 := (mul_eq_zero.1 this).resolve_left ha
      simp only [Prod.mk.injEq]; constructor <;> linarith
    apply ((finite_mul_eq (mul_ne_zero ha he)).preimage hφ.injOn).subset
    rintro ⟨x, y⟩ (h : binF a b c x y = e)
    show (a * x + b * y - k * y) * (a * x + b * y + k * y) = a * e
    rw [← h]; unfold binF; linear_combination y ^ 2 * hk


/-- $T$ is a real automorph of the form $f_0(x,y) = xy$ (Cassels (3.1)). -/
def IsXYAut (T : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ x y : ℝ, (T 0 0 * x + T 0 1 * y) * (T 1 0 * x + T 1 1 * y) = x * y

/-- $T$ is an automorph of $xy$ if and only if $T_{00}T_{10} = 0$, $T_{01}T_{11} = 0$ and $T_{00}T_{11} + T_{01}T_{10} = 1$. -/
theorem isXYAut_iff (T : Matrix (Fin 2) (Fin 2) ℝ) :
    IsXYAut T ↔ T 0 0 * T 1 0 = 0 ∧ T 0 1 * T 1 1 = 0 ∧ T 0 0 * T 1 1 + T 0 1 * T 1 0 = 1 := by
  constructor
  · intro h
    have h1 := h 1 0; have h2 := h 0 1; have h3 := h 1 1
    simp only [mul_one, mul_zero, add_zero, zero_add] at h1 h2 h3
    refine ⟨h1, h2, by linear_combination h3 - h1 - h2⟩
  · rintro ⟨h1, h2, h3⟩ x y
    linear_combination x ^ 2 * h1 + y ^ 2 * h2 + x * y * h3

/-- The homomorphism $s \mapsto \begin{pmatrix}s&0\\0&s^{-1}\end{pmatrix}$ from $\mathbb R^{\times}$ to $SL_2(\mathbb R)$ (Cassels (3.2)). -/
def xyHom : ℝˣ →* Matrix.SpecialLinearGroup (Fin 2) ℝ where
  toFun s := ⟨!![(s : ℝ), 0; 0, ((s⁻¹ : ℝˣ) : ℝ)], by simp [Matrix.det_fin_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' s s' := by
    apply Subtype.ext
    show !![((s * s' : ℝˣ) : ℝ), 0; 0, (((s * s')⁻¹ : ℝˣ) : ℝ)] =
      !![(s : ℝ), 0; 0, ((s⁻¹ : ℝˣ) : ℝ)] * !![(s' : ℝ), 0; 0, ((s'⁻¹ : ℝˣ) : ℝ)]
    rw [Matrix.mul_fin_two]; simp [mul_comm]

/-- The matrix of `xyHom s` is $\operatorname{diag}(s, s^{-1})$. -/
theorem coe_xyHom (s : ℝˣ) :
    ((xyHom s : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(s : ℝ), 0; 0, ((s⁻¹ : ℝˣ) : ℝ)] := rfl

/-- **Lemma 3.1**, proper part, for the normal form $f_0 = xy$ (3.1), to which every indefinite real binary form is real-equivalent: $s \mapsto \operatorname{diag}(s,s^{-1})$ is an injective homomorphism $\mathbb R^{\times} \to SL_2(\mathbb R)$ whose image is exactly the group $O^{+}_{\mathbb R}(f_0)$ of proper real automorphs; so $O^{+}_{\mathbb R}(f_0) \cong \mathbb R^{\times}$. -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.1, p. 289 (proper automorphs, for the normal form xy)"]
theorem lemma_3_1_proper : Function.Injective xyHom ∧
    ∀ T : Matrix.SpecialLinearGroup (Fin 2) ℝ, IsXYAut (T : Matrix (Fin 2) (Fin 2) ℝ) ↔ T ∈ xyHom.range := by
  refine ⟨?_, fun T => ?_⟩
  · intro s s' h
    have := congrArg (fun T : Matrix.SpecialLinearGroup (Fin 2) ℝ => (T : Matrix (Fin 2) (Fin 2) ℝ) 0 0) h
    exact Units.ext (by simpa [coe_xyHom] using this)
  · constructor
    · intro hT
      obtain ⟨h1, h2, h3⟩ := (isXYAut_iff _).1 hT
      have hdet := T.prop
      rw [Matrix.det_fin_two] at hdet
      have h00 : (T : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (T : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by
        linarith
      have hne : (T : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one h00
      have hne' : (T : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one h00
      have h10 : (T : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := (mul_eq_zero.1 h1).resolve_left hne
      have h01 : (T : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := (mul_eq_zero.1 h2).resolve_right hne'
      refine ⟨Units.mk0 _ hne, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [coe_xyHom, h10, h01]
      exact (eq_inv_of_mul_eq_one_right h00).symm
    · rintro ⟨s, rfl⟩
      rw [isXYAut_iff, coe_xyHom]; simp

/-- **Lemma 3.1**, improper part, for $f_0 = xy$: improper real automorphs exist, and every one has order $2$ ($T^{2} = I \ne T$). -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.1, p. 289 (improper automorphs, for the normal form xy)"]
theorem lemma_3_1_improper :
    (∃ T : Matrix (Fin 2) (Fin 2) ℝ, T.det = -1 ∧ IsXYAut T) ∧
    ∀ T : Matrix (Fin 2) (Fin 2) ℝ, T.det = -1 → IsXYAut T → T * T = 1 ∧ T ≠ 1 := by
  refine ⟨⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two], by rw [isXYAut_iff]; simp⟩, ?_⟩
  intro T hdet hT
  obtain ⟨h1, h2, h3⟩ := (isXYAut_iff _).1 hT
  rw [Matrix.det_fin_two] at hdet
  have h01 : T 0 1 * T 1 0 = 1 := by linarith
  have h00 : T 0 0 * T 1 1 = 0 := by linarith
  have hne : T 0 1 ≠ 0 := left_ne_zero_of_mul_eq_one h01
  have hne' : T 1 0 ≠ 0 := right_ne_zero_of_mul_eq_one h01
  have ha : T 0 0 = 0 := (mul_eq_zero.1 h1).resolve_right hne'
  have hd : T 1 1 = 0 := (mul_eq_zero.1 h2).resolve_left hne
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd]
    · exact h01
    · rw [mul_comm]; exact h01
  · rintro rfl; simp at ha


/-- A nonzero integral vector $(v_1,v_2)$ is $g\,(p,q)$ with $g \ne 0$ and $(p,q)$ primitive, with Bézout coefficients $py - qx = 1$. -/
theorem exists_primitive {v₁ v₂ : ℤ} (hv : v₁ ≠ 0 ∨ v₂ ≠ 0) :
    ∃ g p q x y : ℤ, g ≠ 0 ∧ v₁ = g * p ∧ v₂ = g * q ∧ p * y - q * x = 1 := by
  have hg : 0 < Int.gcd v₁ v₂ := by
    rcases hv with h | h
    · exact Int.gcd_pos_of_ne_zero_left _ h
    · exact Int.gcd_pos_of_ne_zero_right _ h
  set g : ℤ := ((Int.gcd v₁ v₂ : ℕ) : ℤ) with hgdef
  have h1 := Int.gcd_div_gcd_div_gcd hg
  have hb := Int.gcd_eq_gcd_ab (v₁ / g) (v₂ / g)
  rw [h1] at hb
  refine ⟨g, v₁ / g, v₂ / g, -Int.gcdB (v₁ / g) (v₂ / g), Int.gcdA (v₁ / g) (v₂ / g),
    by omega, (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm,
    (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm, ?_⟩
  push_cast at hb; linarith

/-- **Lemma 3.4**: if $T$ is an integral $2\times2$ matrix with $T^{2} = I$ and $\det T = -1$, there is an integral $S$ with $\det S = 1$ and $w \in \{0,1\}$ such that $TS = S\begin{pmatrix}1&w\\0&-1\end{pmatrix}$, i.e. $S^{-1}TS = \begin{pmatrix}1&w\\0&-1\end{pmatrix}$ (3.30)–(3.31). (Cassels allows $\det S = \pm1$; here $\det S = 1$.) -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.4, p. 294"]
theorem lemma_3_4 {T : Matrix (Fin 2) (Fin 2) ℤ} (hsq : T * T = 1) (hdet : T.det = -1) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℤ, S.det = 1 ∧ ∃ w : ℤ, (w = 0 ∨ w = 1) ∧
      T * S = S * !![1, w; 0, -1] := by
  have e00 := congrFun (congrFun hsq 0) 0
  have e11 := congrFun (congrFun hsq 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  rw [Matrix.det_fin_two] at hdet
  set l := T 0 0
  set m := T 0 1
  set n := T 1 0
  set r := T 1 1
  have hr : r = -l := by
    have h1 : l * (l + r) = 0 := by linear_combination e00 + hdet
    have h2 : r * (l + r) = 0 := by linear_combination e11 + hdet
    have : (l + r) * (l + r) = 0 := by linear_combination h1 + h2
    have := mul_self_eq_zero.1 this
    linarith
  -- a primitive fixed vector `(p, q)`
  have hfix : ∃ p q x y : ℤ, p * y - q * x = 1 ∧ (l - 1) * p + m * q = 0 ∧ n * p + (r - 1) * q = 0 := by
    by_cases hrow : l - 1 = 0 ∧ m = 0
    · obtain ⟨g, p, q, x, y, hg, h1, h2, hb⟩ := exists_primitive (v₁ := 2) (v₂ := n) (Or.inl two_ne_zero)
      refine ⟨p, q, x, y, hb, ?_, ?_⟩
      · rw [hrow.1, hrow.2]; ring
      · apply mul_left_cancel₀ hg
        have hl : l = 1 := by linarith [hrow.1]
        rw [hr, hl]; linear_combination (-n) * h1 + 2 * h2
    · have hv : m ≠ 0 ∨ 1 - l ≠ 0 := by
        by_contra h; push Not at h; exact hrow ⟨by linarith [h.2], h.1⟩
      obtain ⟨g, p, q, x, y, hg, h1, h2, hb⟩ := exists_primitive hv
      refine ⟨p, q, x, y, hb, ?_, ?_⟩
      · apply mul_left_cancel₀ hg
        linear_combination (-(l - 1)) * h1 - m * h2
      · apply mul_left_cancel₀ hg
        rw [hr]; linear_combination (-n) * h1 + (l + 1) * h2 + e00
  obtain ⟨p, q, x, y, hb, hp1, hp2⟩ := hfix
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = l * x + m * y + x := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = n * x + r * y + y := ⟨_, rfl⟩
  -- `(c₁, c₂) = (T + I) b` is fixed by `T`, hence proportional to `(p, q)`
  have hc1 : (l - 1) * c₁ + m * c₂ = 0 := by
    rw [hc₁, hc₂, hr]; linear_combination x * e00
  have hc2 : n * c₁ + (r - 1) * c₂ = 0 := by
    rw [hc₁, hc₂, hr]; linear_combination y * e00
  have hD : p * c₂ - q * c₁ = 0 := by
    by_cases hrow : l - 1 = 0 ∧ m = 0
    · have hl : l = 1 := by linarith [hrow.1]
      have : (r - 1) * (p * c₂ - q * c₁) = 0 := by linear_combination p * hc2 - c₁ * hp2
      rw [hr, hl] at this
      linarith
    · rcases not_and_or.1 hrow with h | h
      · have : (l - 1) * (p * c₂ - q * c₁) = 0 := by linear_combination c₂ * hp1 - q * hc1
        exact (mul_eq_zero.1 this).resolve_left h
      · have : m * (p * c₂ - q * c₁) = 0 := by linear_combination p * hc1 - c₁ * hp1
        exact (mul_eq_zero.1 this).resolve_left h
  obtain ⟨w₀, hw₀⟩ : ∃ w, w = y * c₁ - x * c₂ := ⟨_, rfl⟩
  have hw1 : p * w₀ = c₁ := by rw [hw₀]; linear_combination c₁ * hb - x * hD
  have hw2 : q * w₀ = c₂ := by rw [hw₀]; linear_combination c₂ * hb - y * hD
  refine ⟨!![p, x - (w₀ / 2) * p; q, y - (w₀ / 2) * q], ?_, w₀ % 2, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hb
  · have := Int.emod_two_eq_zero_or_one w₀; omega
  · have hT : T = !![l, m; n, r] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hT, Matrix.mul_fin_two, Matrix.mul_fin_two, Int.emod_def]
    have hp' : l * p + m * q = p := by linarith
    have hq' : n * p + r * q = q := by linarith
    ext i j; fin_cases i <;> fin_cases j <;> simp
    · linear_combination hp'
    · linear_combination (-(w₀ / 2)) * hp' - hw1 - hc₁
    · linear_combination hq'
    · linear_combination (-(w₀ / 2)) * hq' - hw2 - hc₂


/-- The value $f(\vec{v}) = f(v_0, v_1)$ of $f = ax^{2}+2bxy+cy^{2}$ at a vector $\vec{v}$. -/
def fv {R : Type*} [CommRing R] (a b c : R) (v : Fin 2 → R) : R := binF a b c (v 0) (v 1)

/-- $f(T\vec{v})$ in coordinates. -/
theorem fv_mulVec {R : Type*} [CommRing R] (a b c : R) (T : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) :
    fv a b c (T *ᵥ v) = binF a b c (T 0 0 * v 0 + T 0 1 * v 1) (T 1 0 * v 0 + T 1 1 * v 1) := by
  simp [fv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- $T$ is an automorph of $f$ if and only if $f(T\vec{v}) = f(\vec{v})$ for all vectors $\vec{v}$. -/
theorem isBinAut_iff_mulVec {R : Type*} [CommRing R] (a b c : R) (T : Matrix (Fin 2) (Fin 2) R) :
    IsBinAut a b c T ↔ ∀ v, fv a b c (T *ᵥ v) = fv a b c v := by
  constructor
  · intro h v; rw [fv_mulVec]; exact h _ _
  · intro h x y
    have := h ![x, y]
    rw [fv_mulVec] at this
    simpa [fv] using this

/-- An integral $2\times2$ matrix viewed as a real matrix. -/
abbrev toR (T : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ := T.map (Int.castRingHom ℝ)

/-- The determinant commutes with $\mathbb Z \to \mathbb R$. -/
theorem det_toR (T : Matrix (Fin 2) (Fin 2) ℤ) : (toR T).det = (T.det : ℝ) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]; simp

/-- **Theorem 3.2**: a regular ($ac - b^{2} \ne 0$) real binary form $f = ax^{2}+2bxy+cy^{2}$ has an improper integral automorph if and only if it is integrally equivalent ($\vec{x} \mapsto S\vec{x}$, $S$ integral with $\det S = \pm1$) to a form $a'x^{2} + 2b'xy + c'y^{2}$ with $b' = 0$ (3.27) or $2b' = a'$ (3.28). -/
@[kb "cassels1978" "Ch. 13, §3, Thm. 3.2, p. 294"]
theorem thm_3_2 {a b c : ℝ} (hreg : a * c - b ^ 2 ≠ 0) :
    (∃ T : Matrix (Fin 2) (Fin 2) ℤ, T.det = -1 ∧ IsBinAut a b c (toR T)) ↔
    ∃ S : Matrix (Fin 2) (Fin 2) ℤ, (S.det = 1 ∨ S.det = -1) ∧ ∃ a' b' c' : ℝ,
      (∀ v : Fin 2 → ℝ, fv a b c (toR S *ᵥ v) = fv a' b' c' v) ∧ (b' = 0 ∨ 2 * b' = a') := by
  constructor
  · rintro ⟨T, hdet, hT⟩
    have hdetR : (toR T).det = -1 := by rw [det_toR, hdet]; simp
    obtain ⟨h1, h2, h3⟩ := improper_rel hT hdetR
    have hlr : T 0 0 + T 1 1 = 0 := by
      have : ((T 0 0 + T 1 1 : ℤ) : ℝ) = 0 := by
        push_cast
        by_contra hne
        apply hreg
        have ha : a = 0 := by simpa [hne] using h1
        have hc : c = 0 := by simpa [hne] using h2
        have hb : b = 0 := by simpa [hne] using h3
        rw [ha, hb, hc]; ring
      exact_mod_cast this
    have hdet' := hdet
    rw [Matrix.det_fin_two] at hdet'
    have hsq : T * T = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · have : T 1 1 = -T 0 0 := by linarith
        rw [this] at hdet'; linarith
      · linear_combination T 0 1 * hlr
      · linear_combination T 1 0 * hlr
      · have : T 0 0 = -T 1 1 := by linarith
        rw [this] at hdet'; linarith
    obtain ⟨S, hS, w, hw, hTS⟩ := lemma_3_4 hsq hdet
    set S' := toR S
    obtain ⟨a', ha'⟩ : ∃ x, x = binF a b c (S' 0 0) (S' 1 0) := ⟨_, rfl⟩
    obtain ⟨b', hb'⟩ : ∃ x, x = a * S' 0 0 * S' 0 1 + b * (S' 0 0 * S' 1 1 + S' 0 1 * S' 1 0)
        + c * S' 1 0 * S' 1 1 := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ x, x = binF a b c (S' 0 1) (S' 1 1) := ⟨_, rfl⟩
    have key : ∀ u, fv a b c (S' *ᵥ u) = fv a' b' c' u := by
      intro u; rw [fv_mulVec, binF_subst, ha', hb', hc']; unfold fv binF; ring
    refine ⟨S, Or.inl hS, a', b', c', key, ?_⟩
    -- the matrix `M` is an automorph of `f ∘ S`
    have hM : IsBinAut a' b' c' (toR !![1, w; 0, -1]) := by
      rw [isBinAut_iff_mulVec]
      intro v
      rw [← key, ← key, Matrix.mulVec_mulVec]
      have : S' * toR !![1, w; 0, -1] = toR T * S' := by
        simp only [S', toR, ← Matrix.map_mul, hTS]
      rw [this, ← Matrix.mulVec_mulVec]
      exact (isBinAut_iff_mulVec a b c _).1 hT _
    obtain ⟨-, -, E3⟩ := (isBinAut_iff _ _ _ _).1 hM
    rcases hw with rfl | rfl
    · left; simp at E3; linarith
    · right; simp at E3; linarith
  · rintro ⟨S, hS, a', b', c', hf, hb'⟩
    obtain ⟨w, hw, hM⟩ : ∃ w : ℤ, (w = 0 ∨ w = 1) ∧ IsBinAut a' b' c' (toR !![1, w; 0, -1]) := by
      rcases hb' with h | h
      · refine ⟨0, Or.inl rfl, ?_⟩
        rw [isBinAut_iff]; simp [h]
      · refine ⟨1, Or.inr rfl, ?_⟩
        rw [isBinAut_iff]; simp; constructor <;> linarith
    have hdd : S.det * S.det = 1 := by rcases hS with h | h <;> rw [h] <;> norm_num
    set Si := S.det • S.adjugate
    have hSSi : S * Si = 1 := by
      simp only [Si, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hdd, one_smul]
    have hSiS : Si * S = 1 := by
      simp only [Si, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hdd, one_smul]
    refine ⟨S * !![1, w; 0, -1] * Si, ?_, ?_⟩
    · have : (S * !![1, w; 0, -1] * Si).det = (!![1, w; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ).det * (Si * S).det := by
        simp only [Matrix.det_mul]; ring
      rw [this, hSiS, Matrix.det_one, Matrix.det_fin_two_of]; ring
    · rw [isBinAut_iff_mulVec]
      intro v
      simp only [toR, Matrix.map_mul, ← Matrix.mulVec_mulVec]
      rw [hf, (isBinAut_iff_mulVec _ _ _ _).1 hM, ← hf, Matrix.mulVec_mulVec, ← Matrix.map_mul, hSSi,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]


/-- **Lemma 3.5**: for $d < 0$ there are only finitely many classically integral forms $f = ax^{2}+2bxy+cy^{2}$ ($a,b,c \in \mathbb Z$, $ac - b^{2} = d$) that factor as $f = a(x+\theta y)(x-\varphi y)$ with $\theta, \varphi > 0$ and $\theta + \varphi > 1$. The reduction conditions (3.35) are lost in the machine-read text; the proof uses exactly $\theta, \varphi > 0$ and $\theta + \varphi > 1$, so this statement covers every classically reduced form (3.34)–(3.35). -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.5, p. 295"]
theorem lemma_3_5 {d : ℤ} (hd : d < 0) :
    {f : ℤ × ℤ × ℤ | f.1 * f.2.2 - f.2.1 ^ 2 = d ∧ ∃ θ φ : ℝ, 0 < θ ∧ 0 < φ ∧ 1 < θ + φ ∧
      ∀ x y : ℝ, binF (f.1 : ℝ) f.2.1 f.2.2 x y = f.1 * (x + θ * y) * (x - φ * y)}.Finite := by
  apply (((Set.finite_Icc (4 * d) (-4 * d)).prod (Set.finite_Icc (4 * d) (-4 * d))).image
    (fun p : ℤ × ℤ => (p.1, p.2, (d + p.2 ^ 2) / p.1))).subset
  rintro ⟨a, b, c⟩ ⟨hdet, θ, φ, hθ, hφ, hθφ, hf⟩
  simp only at hdet hf
  have h01 := hf 0 1
  have h11 := hf 1 1
  unfold binF at h01 h11
  have hc : (c : ℝ) = -a * θ * φ := by linear_combination h01
  have hb : 2 * (b : ℝ) = a * (θ - φ) := by linear_combination h11 - h01
  have hdR : ((d : ℤ) : ℝ) = a * c - b ^ 2 := by rw [← hdet]; push_cast; ring
  have key : -4 * (d : ℝ) = (a : ℝ) ^ 2 * (θ + φ) ^ 2 := by
    rw [hdR]; linear_combination (-4 * (a : ℝ)) * hc + (2 * (b : ℝ) + a * (θ - φ)) * hb
  have ha2 : (a : ℝ) ^ 2 ≤ -4 * d := by
    have h1 : 1 ≤ (θ + φ) ^ 2 := by nlinarith
    rw [key]; nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (a : ℝ))]
  have hb2 : (2 * (b : ℝ)) ^ 2 ≤ -4 * d := by
    rw [key, hb]; nlinarith [sq_nonneg (a : ℝ), mul_pos hθ hφ, sq_nonneg (θ - φ)]
  have ha2' : a ^ 2 ≤ -4 * d := by exact_mod_cast ha2
  have hb2' : b ^ 2 ≤ -4 * d := by
    have : (2 * b) ^ 2 ≤ -4 * d := by exact_mod_cast hb2
    nlinarith [sq_nonneg b]
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : -4 * (d : ℝ) = 0 := by rw [key]; simp
    have : (d : ℝ) < 0 := by exact_mod_cast hd
    linarith
  refine ⟨(a, b), ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · nlinarith [Int.le_self_sq (-a)]
  · nlinarith [Int.le_self_sq a]
  · nlinarith [Int.le_self_sq (-b)]
  · nlinarith [Int.le_self_sq b]
  · simp only [Prod.mk.injEq, true_and]
    have : d + b ^ 2 = a * c := by rw [← hdet]; ring
    rw [this, Int.mul_ediv_cancel_left _ ha0]


section Lemma33

/-- The homomorphism $(t,u) \mapsto \eta = t + u\sqrt{D}$ (3.24) from Pell solutions to $\mathbb R^{\times}$ (its inverse is $t - u\sqrt{D}$). -/
noncomputable def etaHom (a b c : ℤ) (hD : 0 < b ^ 2 - a * c) : Pell.Solution₁ (b ^ 2 - a * c) →* ℝˣ where
  toFun s := ⟨s.x + s.y * Real.sqrt ((b ^ 2 - a * c : ℤ) : ℝ), s.x - s.y * Real.sqrt ((b ^ 2 - a * c : ℤ) : ℝ),
    by
      have h := s.prop
      have hr := Real.sq_sqrt (show (0 : ℝ) ≤ ((b ^ 2 - a * c : ℤ) : ℝ) by exact_mod_cast hD.le)
      have h' : ((s.x : ℝ)) ^ 2 - ((b ^ 2 - a * c : ℤ) : ℝ) * (s.y : ℝ) ^ 2 = 1 := by exact_mod_cast h
      linear_combination h' - (s.y : ℝ) ^ 2 * hr,
    by
      have h := s.prop
      have hr := Real.sq_sqrt (show (0 : ℝ) ≤ ((b ^ 2 - a * c : ℤ) : ℝ) by exact_mod_cast hD.le)
      have h' : ((s.x : ℝ)) ^ 2 - ((b ^ 2 - a * c : ℤ) : ℝ) * (s.y : ℝ) ^ 2 = 1 := by exact_mod_cast h
      linear_combination h' - (s.y : ℝ) ^ 2 * hr⟩
  map_one' := by ext; simp
  map_mul' s s' := by
    have hr := Real.sq_sqrt (show (0 : ℝ) ≤ ((b ^ 2 - a * c : ℤ) : ℝ) by exact_mod_cast hD.le)
    ext
    simp only [Units.val_mul, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul, Int.cast_add, Int.cast_mul]
    linear_combination (-(s.y : ℝ) * s'.y) * hr

/-- The linear forms $L = ax + by + \sqrt{D}\,y$ (`sgn = 1`) and $M = ax + by - \sqrt{D}\,y$ (`sgn = -1`) of (3.22), $D = b^{2}-ac$. -/
noncomputable def linLM (a b c : ℤ) (sgn : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  a * v 0 + b * v 1 + sgn * Real.sqrt ((b ^ 2 - a * c : ℤ) : ℝ) * v 1

/-- (3.23): $L(T(t,u)\vec{v}) = (t + u\sqrt{D})L(\vec{v})$ and $M(T(t,u)\vec{v}) = (t - u\sqrt{D})M(\vec{v})$. -/
theorem linLM_autMat {a b c : ℤ} (hD : 0 < b ^ 2 - a * c) (sgn : ℝ) (hsgn : sgn ^ 2 = 1) (t u : ℤ) (v : Fin 2 → ℝ) :
    linLM a b c sgn ((autMat a b c t u).map (Int.cast : ℤ → ℝ) *ᵥ v) =
      (t + sgn * u * Real.sqrt ((b ^ 2 - a * c : ℤ) : ℝ)) * linLM a b c sgn v := by
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ ((b ^ 2 - a * c : ℤ) : ℝ) by exact_mod_cast hD.le)
  push_cast at hr
  simp [linLM, autMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (-((u : ℝ) * v 1)) * hr - ((u : ℝ) * v 1 * Real.sqrt ((b : ℝ) ^ 2 - a * c) ^ 2) * hsgn

/-- (3.22): $L(\vec{v})M(\vec{v}) = a f(\vec{v})$. -/
theorem linLM_mul {a b c : ℤ} (hD : 0 < b ^ 2 - a * c) (v : Fin 2 → ℝ) :
    linLM a b c 1 v * linLM a b c (-1) v = a * binF (a : ℝ) b c (v 0) (v 1) := by
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ ((b ^ 2 - a * c : ℤ) : ℝ) by exact_mod_cast hD.le)
  simp only [linLM, binF]
  push_cast at hr ⊢
  linear_combination (-(v 1) ^ 2) * hr

/-- **Lemma 3.3**: let $f = ax^{2}+2bxy+cy^{2}$ be integral, indefinite and anisotropic ($D = b^{2}-ac > 0$ not a square), $\eta_0 = t_0 + u_0\sqrt{D} > 1$ for the fundamental solution of Pell's equation. For every real $\vec{v}$ with $f(\vec{v}) \ne 0$ there is a proper integral automorph $T$ ($= T_1^{\nu}$) with $L(T\vec{v})^{2} \le \eta_0\,\lvert a f(\vec{v})\rvert$ and $M(T\vec{v})^{2} \le \eta_0\,\lvert a f(\vec{v})\rvert$, i.e. $\lvert L(T\vec{v})\rvert, \lvert M(T\vec{v})\rvert \le \lvert \eta_0 L(\vec{v})M(\vec{v})\rvert^{1/2}$. (Cassels writes $\lvert\eta_0 f(b)\rvert^{1/2}$; with $LM = af$ as in (3.22) the factor $a$ belongs there; it is $1$ for $a = 1$.) -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.3, pp. 292–293"]
theorem lemma_3_3 {a b c : ℤ}
    (hD : 0 < b ^ 2 - a * c) (hsq : ¬ IsSquare (b ^ 2 - a * c)) :
    ∃ a₁ : Pell.Solution₁ (b ^ 2 - a * c), Pell.IsFundamental a₁ ∧
      ∀ v : Fin 2 → ℝ, binF (a : ℝ) b c (v 0) (v 1) ≠ 0 →
        ∃ T : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsBinAut a b c (T : Matrix (Fin 2) (Fin 2) ℤ) ∧
          linLM a b c 1 ((T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) *ᵥ v) ^ 2 ≤
            (etaHom a b c hD a₁ : ℝ) * |a * binF (a : ℝ) b c (v 0) (v 1)| ∧
          linLM a b c (-1) ((T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) *ᵥ v) ^ 2 ≤
            (etaHom a b c hD a₁ : ℝ) * |a * binF (a : ℝ) b c (v 0) (v 1)| := by
  have ha := ne_zero_of_not_isSquare hsq
  obtain ⟨a₁, h₁⟩ := Pell.IsFundamental.exists_of_not_isSquare hD hsq
  refine ⟨a₁, h₁, fun v hv => ?_⟩
  set η := ((etaHom a b c hD a₁ : ℝˣ) : ℝ) with hη
  have hη1 : 1 < η := by
    have hx : (1 : ℝ) < a₁.x := by exact_mod_cast h₁.1
    have hy : (0 : ℝ) < a₁.y := by exact_mod_cast h₁.2.1
    have : η = a₁.x + a₁.y * Real.sqrt ((b ^ 2 - a * c : ℤ) : ℝ) := rfl
    rw [this]; nlinarith [Real.sqrt_nonneg ((b ^ 2 - a * c : ℤ) : ℝ)]
  set Lv := linLM a b c 1 v
  set Mv := linLM a b c (-1) v
  have hLM : Lv * Mv = a * binF (a : ℝ) b c (v 0) (v 1) := linLM_mul hD v
  have hP : 0 < |a * binF (a : ℝ) b c (v 0) (v 1)| :=
    abs_pos.2 (mul_ne_zero (by exact_mod_cast ha) hv)
  set P := |a * binF (a : ℝ) b c (v 0) (v 1)|
  have hL0 : Lv ≠ 0 := by
    intro h; apply hP.ne'; simp only [P]; rw [← hLM, h, zero_mul, abs_zero]
  have hℓ : 0 < Lv ^ 2 := by positivity
  have hPsq : Lv ^ 2 * Mv ^ 2 = P ^ 2 := by rw [← mul_pow, hLM, sq_abs]
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow (show 0 < η * P / Lv ^ 2 by positivity)
    (show 1 < η ^ 2 by nlinarith)
  -- the automorph `T = T₁ ^ n`
  set s := a₁ ^ n
  have hvals : ∀ sgn : ℝ, sgn ^ 2 = 1 → linLM a b c sgn
      (((pellHom a b c s : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.cast : ℤ → ℝ) *ᵥ v) = (s.x + sgn * s.y * Real.sqrt ((b ^ 2 - a * c : ℤ) : ℝ)) *
          linLM a b c sgn v := by
    intro sgn hsgn
    rw [coe_pellHom, linLM_autMat hD sgn hsgn]
  have hplus : (s.x + 1 * s.y * Real.sqrt ((b ^ 2 - a * c : ℤ) : ℝ)) = η ^ n := by
    rw [hη, ← Units.val_zpow_eq_zpow_val, ← map_zpow]; simp [etaHom, s]
  have hminus : (s.x + (-1) * s.y * Real.sqrt ((b ^ 2 - a * c : ℤ) : ℝ)) = (η ^ n)⁻¹ := by
    rw [hη, ← Units.val_zpow_eq_zpow_val, ← map_zpow, ← Units.val_inv_eq_inv_val]
    simp [etaHom, s]; ring
  have hq : (η ^ n) ^ 2 = (η ^ 2) ^ n := by
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  have hqpos : 0 < (η ^ 2) ^ n := zpow_pos (by positivity) n
  refine ⟨pellHom a b c s, isBinAut_autMat s.prop, ?_, ?_⟩
  · rw [hvals 1 (by norm_num), hplus, mul_pow, hq]
    have := (lt_div_iff₀ hℓ).1 hn1
    linarith
  · rw [hvals (-1) (by norm_num), hminus, mul_pow, inv_pow, hq]
    have h2 : η * P / Lv ^ 2 ≤ (η ^ 2) ^ n * η ^ 2 := by rw [← zpow_add_one₀ (by positivity)]; exact hn2
    rw [div_le_iff₀ hℓ] at h2
    rw [inv_mul_le_iff₀ hqpos]
    -- `Mv² ≤ q η P` from `Lv² Mv² = P²` and `P ≤ q η Lv²`
    have h3 : P ≤ (η ^ 2) ^ n * η * Lv ^ 2 := by nlinarith
    have h4 : Lv ^ 2 * Mv ^ 2 ≤ Lv ^ 2 * ((η ^ 2) ^ n * (η * P)) := by
      rw [hPsq]; nlinarith
    nlinarith

end Lemma33

end QuadFormsKB.Cassels.Ch13
