/-
# Cassels, Chapter 13, §3: the classical reduction of indefinite binary forms

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §3, pp. 294–296: classically reduced forms
((3.34)–(3.36)), the finiteness of the classically integral ones of given determinant (Lemma 3.5) and the existence of
a classically reduced form in each class of real indefinite $\mathbb{Q}$-anisotropic forms (Lemma 3.6). Cassels
"sketch[es] the classical theory briefly"; the continuation (the sequence of forms $f_m$, Lemma 3.6, Corollary;
Lemma 3.7 and its Corollary) is not formalized here.

Conventions as in `Ch13/Sec2.lean`: a real binary form is its symmetric matrix $F$, $f(\vec{x}) = $ `val F x`,
$\vec{x} = (x_0, x_1)$ (Cassels' $(x, y)$).
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic

open Matrix

namespace QuadFormsKB.Reduction

/-- The value of a real binary form with symmetric matrix: $f(x) = F_{00}x_0^2 + 2F_{01}x_0x_1 + F_{11}x_1^2$. -/
theorem val_fin2 {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (x : Fin 2 → ℝ) :
    val F x = F 0 0 * x 0 ^ 2 + 2 * F 0 1 * x 0 * x 1 + F 1 1 * x 1 ^ 2 := by
  have h : F 1 0 = F 0 1 := hF.apply 0 1
  simp [val, dotProduct, mulVec, Fin.sum_univ_two, h]
  ring

/-- **Minkowski for a parallelogram:** if $C$ is an invertible real $2 \times 2$ matrix and $s, t > 0$ with
$|\det C| \le st$, there is a nonzero integral $\vec{m}$ with $|(C\vec{m})_0| \le s$, $|(C\vec{m})_1| \le t$. -/
theorem exists_int_mem_box {C : Matrix (Fin 2) (Fin 2) ℝ} (hC : C.det ≠ 0) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : |C.det| ≤ s * t) :
    ∃ m : Fin 2 → ℤ, m ≠ 0 ∧ |(C *ᵥ cast m) 0| ≤ s ∧ |(C *ᵥ cast m) 1| ≤ t := by
  set r : Fin 2 → ℝ := ![s, t] with hr
  set box : Set (Fin 2 → ℝ) := Set.Icc (fun i => -r i) r with hbox
  set f : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' C⁻¹ with hf
  set S : Set (Fin 2 → ℝ) := f '' box with hS
  have hU : IsUnit C.det := isUnit_iff_ne_zero.2 hC
  have hCinv : ∀ y, C *ᵥ (C⁻¹ *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have hvol : (2 : ENNReal) ^ 2 ≤ MeasureTheory.volume S := by
    rw [hS, MeasureTheory.Measure.addHaar_image_linearMap, hbox, Real.volume_Icc_pi]
    have hdf : LinearMap.det f = (C.det)⁻¹ := by
      rw [hf, LinearMap.det_toLin', Matrix.det_nonsing_inv]; simp [Ring.inverse_eq_inv']
    rw [hdf]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by fin_cases i <;> simp [hr] <;> linarith)]
    simp only [Fin.prod_univ_two, hr]
    simp
    rw [← ENNReal.ofReal_mul (by positivity)]
    have : (2 : ENNReal) ^ 2 = ENNReal.ofReal 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ENNReal.ofReal_pow (by norm_num)]; simp
    rw [this]
    apply ENNReal.ofReal_le_ofReal
    have hpos : 0 < |C.det| := abs_pos.2 hC
    have h1 : 1 ≤ |C.det|⁻¹ * (s * t) := by rw [← div_eq_inv_mul]; exact (one_le_div hpos).2 hst
    have : |C.det|⁻¹ * ((s + s) * (t + t)) = 4 * (|C.det|⁻¹ * (s * t)) := by ring
    rw [this]; linarith
  obtain ⟨m, hm0, hmS⟩ := exists_int_mem_of_volume_ge (s := S) (by norm_num)
    (by
      rintro x ⟨y, hy, rfl⟩
      refine ⟨-y, ⟨?_, ?_⟩, by rw [map_neg]⟩ <;> intro i <;> simp <;>
        linarith [(hy.1 i), (hy.2 i), show (-y) i = - y i from rfl])
    ((convex_Icc _ _).linear_image f)
    (isCompact_Icc.image (LinearMap.continuous_of_finiteDimensional f))
    hvol
  refine ⟨m, hm0, ?_⟩
  obtain ⟨y, hy, hyx⟩ := hmS
  have hCm : C *ᵥ cast m = y := by
    rw [← hyx, hf, Matrix.toLin'_apply, hCinv]
  rw [hCm]
  have h0 := hy.1 0
  have h1 := hy.1 1
  have h0' := hy.2 0
  have h1' := hy.2 1
  simp [hr] at h0 h1 h0' h1'
  exact ⟨abs_le.2 ⟨h0, h0'⟩, abs_le.2 ⟨h1, h1'⟩⟩

/-- **Classically reduced binary form** (Cassels, Ch. 13, §3, (3.34)–(3.35), p. 295): a real binary form of the shape
$$f(x, y) = a(x + \theta y)(x - \phi y) \tag{3.34}$$
with $a \ne 0$ and
$$\theta > 1, \qquad 0 < \phi < 1. \tag{3.35}$$
The conditions (3.35) are garbled in the machine-read text; they are reconstructed from their use ($\theta + \phi > 1$
and $\theta, \phi > 0$ in the proof of Lemma 3.5, $\theta_0 > 1 > \phi_0 > 0$ in that of Lemma 3.6) and from the
equivalent sign conditions (3.36) (`isClassicallyReduced_iff`). -/
@[kb "cassels1978" "Ch. 13, §3, (3.34)–(3.35), p. 295 (classically reduced form)"]
def IsClassicallyReduced (F : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ a θ φ : ℝ, a ≠ 0 ∧ 1 < θ ∧ 0 < φ ∧ φ < 1 ∧ ∀ x : Fin 2 → ℝ, val F x = a * (x 0 + θ * x 1) * (x 0 - φ * x 1)

/-- **(3.36)** (Cassels, Ch. 13, §3, p. 295): a real binary form is classically reduced iff
$$f(1, 0)f(0, 1) < 0, \qquad f(1, 0)f(1, 1) > 0, \qquad f(1, 0)f(-1, 1) < 0.$$
(The first two conditions are garbled in the machine-read text; reconstructed from (3.34)–(3.35).) -/
@[kb "cassels1978" "Ch. 13, §3, (3.36), p. 295"]
theorem isClassicallyReduced_iff {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) :
    IsClassicallyReduced F ↔
      val F ![1, 0] * val F ![0, 1] < 0 ∧ 0 < val F ![1, 0] * val F ![1, 1] ∧
        val F ![1, 0] * val F ![-1, 1] < 0 := by
  constructor
  · rintro ⟨A, θ, φ, hA, hθ, hφ0, hφ1, h⟩
    simp only [h]
    simp
    have hA2 : 0 < A ^ 2 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_pos hA2 (mul_pos (by linarith : (0:ℝ) < θ) hφ0)]
    · nlinarith [mul_pos hA2 (mul_pos (by linarith : (0:ℝ) < 1 + θ) (by linarith : (0:ℝ) < 1 - φ))]
    · nlinarith [mul_pos hA2 (mul_pos (by linarith : (0:ℝ) < θ - 1) (by linarith : (0:ℝ) < 1 + φ))]
  · rintro ⟨h1, h2, h3⟩
    simp only [val_fin2 hF] at h1 h2 h3
    simp at h1 h2 h3
    set a := F 0 0
    set b := F 0 1
    set c := F 1 1
    have ha : a ≠ 0 := by rintro h; rw [h] at h2; simp at h2
    have ha2 : 0 < a ^ 2 := by positivity
    set u := b / a with hu
    set k := c / a with hk
    have hb : b = a * u := by rw [hu]; field_simp
    have hc : c = a * k := by rw [hk]; field_simp
    rw [hc] at h1; rw [hb, hc] at h2 h3
    have h1' : k < 0 := by nlinarith
    have h2' : 0 < 1 + 2 * u + k := by nlinarith
    have h3' : 1 - 2 * u + k < 0 := by nlinarith
    have hpos : 0 < u ^ 2 - k := by nlinarith [sq_nonneg u]
    set s := Real.sqrt (u ^ 2 - k) with hs
    have hs2 : s ^ 2 = u ^ 2 - k := Real.sq_sqrt hpos.le
    have hs0 : 0 < s := Real.sqrt_pos.2 hpos
    have hu1 : 0 < 1 + u := by linarith
    have hφ1 : s < 1 + u := by
      rw [hs, Real.sqrt_lt' hu1]; nlinarith
    have hθ1 : 1 < u + s := by
      by_cases hh : 1 - u < 0
      · linarith
      · have : 1 - u < s := by
          rw [hs, Real.lt_sqrt (by linarith)]; nlinarith
        linarith
    have hφ0 : 0 < s - u := by
      by_contra hh
      have : s ≤ u := by linarith
      nlinarith
    refine ⟨a, u + s, s - u, ha, hθ1, hφ0, by linarith, fun x => ?_⟩
    rw [val_fin2 hF]
    linear_combination (2 * x 0 * x 1) * hb + (x 1 ^ 2) * hc + (a * x 1 ^ 2) * hs2

/-- **Lemma 3.5** (Cassels, Ch. 13, §3, p. 295): there are only finitely many classically integral classically
reduced binary forms $ax^2 + 2bxy + cy^2$ ($a, b, c \in \mathbb{Z}$) of given determinant $d = ac - b^2 < 0$.

Superseded by `Cassels.Ch13.lemma_3_5`, which needs only $\theta, \phi > 0$ and $\theta + \phi > 1$ (every classically reduced form satisfies this). -/
theorem finite_isClassicallyReduced {d : ℤ} (hd : d < 0) :
    {p : ℤ × ℤ × ℤ | p.1 * p.2.2 - p.2.1 ^ 2 = d ∧
      IsClassicallyReduced !![(p.1 : ℝ), p.2.1; p.2.1, p.2.2]}.Finite := by
  refine (Set.finite_Icc ((4 * d, 4 * d, 4 * d) : ℤ × ℤ × ℤ) (-4 * d, -4 * d, -4 * d)).subset ?_
  rintro ⟨a, b, c⟩ ⟨hdet, A, θ, φ, hA, hθ, hφ0, hφ1, h⟩
  simp only at hdet
  have hsymm : (!![(a : ℝ), b; b, c]).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h1 := h ![1, 0]
  have h2 := h ![0, 1]
  have h3 := h ![1, 1]
  rw [val_fin2 hsymm] at h1 h2 h3
  simp at h1 h2 h3
  have hdetR : (a : ℝ) * c - (b : ℝ) ^ 2 = d := by exact_mod_cast hdet
  have hAa : A = a := by linarith
  subst hAa
  have hc : (c : ℝ) = -((a : ℝ) * θ * φ) := by linarith
  have hb : 2 * (b : ℝ) = (a : ℝ) * (θ - φ) := by nlinarith
  have hA2 : 0 < (a : ℝ) ^ 2 := by positivity
  have key : (a : ℝ) ^ 2 * (θ + φ) ^ 2 = -4 * d := by
    rw [← hdetR]
    have : (b : ℝ) ^ 2 = ((a : ℝ) * (θ - φ)) ^ 2 / 4 := by rw [← hb]; ring
    rw [this, hc]; ring
  have hsum : 1 < θ + φ := by linarith
  have ha1 : (a : ℝ) ^ 2 < -4 * d := by
    rw [← key]
    nlinarith [mul_pos hA2 (by nlinarith : (0:ℝ) < (θ + φ) ^ 2 - 1)]
  have hb1 : (2 * (b : ℝ)) ^ 2 ≤ -4 * d := by
    rw [← key, hb]
    nlinarith [mul_pos hA2 (mul_pos (by linarith : (0:ℝ) < θ) hφ0)]
  have ha1' : a ^ 2 < -4 * d := by exact_mod_cast ha1
  have hb1' : (2 * b) ^ 2 ≤ -4 * d := by exact_mod_cast hb1
  have ha0 : a ≠ 0 := by exact_mod_cast hA
  have haN : |a| ≤ a ^ 2 := by
    rw [← sq_abs]; nlinarith [Int.one_le_abs ha0]
  have hbN : b ^ 2 ≤ -d := by nlinarith
  have hac : a * c = d + b ^ 2 := by linarith
  have hcN : |c| ≤ |a * c| := by
    rw [abs_mul]; exact le_mul_of_one_le_left (abs_nonneg c) (Int.one_le_abs ha0)
  have hacN : |a * c| ≤ -d := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg b]
  have hb2 : |b| ≤ b ^ 2 := by
    rw [← sq_abs]; rcases eq_or_ne b 0 with h0 | h0
    · simp [h0]
    · nlinarith [Int.one_le_abs h0]
  rw [abs_le] at haN hb2
  have hcN' := abs_le.1 (hcN.trans hacN)
  have hbb := hb2
  have haa := haN
  simp only [Set.mem_Icc, Prod.mk_le_mk]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> nlinarith

/-- The real linear form $\vec{m} \mapsto m_0 - \alpha m_1$ on $\mathbb{Z}^2$. -/
noncomputable def lu (α : ℝ) (m : Fin 2 → ℤ) : ℝ := (m 0 : ℝ) - α * (m 1 : ℝ)

theorem lu_sub (α : ℝ) (m m' : Fin 2 → ℤ) : lu α (m - m') = lu α m - lu α m' := by
  simp [lu]; ring

theorem lu_neg (α : ℝ) (m : Fin 2 → ℤ) : lu α (-m) = - lu α m := by
  simp [lu]; ring

theorem lu_add (α : ℝ) (m m' : Fin 2 → ℤ) : lu α (m + m') = lu α m + lu α m' := by
  simp [lu]; ring

/-- Minkowski's theorem for the pair of forms $m_0 - \alpha m_1$, $m_0 - \beta m_1$. -/
theorem exists_int_lu {α β : ℝ} {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : |α - β| ≤ s * t)
    (h : α ≠ β) : ∃ m : Fin 2 → ℤ, m ≠ 0 ∧ |lu α m| ≤ s ∧ |lu β m| ≤ t := by
  have hdet : (!![1, -α; 1, -β] : Matrix (Fin 2) (Fin 2) ℝ).det = α - β := by
    simp [Matrix.det_fin_two_of]; ring
  obtain ⟨m, hm, h0, h1⟩ := exists_int_mem_box (C := !![1, -α; 1, -β])
    (by rw [hdet]; exact sub_ne_zero.2 h) hs ht (by rw [hdet]; exact hst)
  refine ⟨m, hm, ?_, ?_⟩
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, lu, sub_eq_add_neg] using h0
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, lu, sub_eq_add_neg] using h1

/-- Only finitely many integral points lie in a bounded parallelogram. -/
theorem finite_lu_box {α β : ℝ} (h : α ≠ β) (K L : ℝ) :
    {m : Fin 2 → ℤ | |lu α m| ≤ K ∧ |lu β m| ≤ L}.Finite := by
  have hpos : 0 < |α - β| := abs_pos.2 (sub_ne_zero.2 h)
  set B1 : ℝ := (K + L) / |α - β| with hB1
  set B : ℝ := B1 + (K + |α| * B1) with hB
  refine (Set.finite_Icc (fun _ : Fin 2 => -⌈B⌉) (fun _ => ⌈B⌉)).subset ?_
  intro m ⟨hK, hL⟩
  have hm1 : |(m 1 : ℝ)| ≤ B1 := by
    rw [hB1, le_div_iff₀ hpos]
    have : (α - β) * (m 1 : ℝ) = lu β m - lu α m := by simp [lu]; ring
    calc |(m 1 : ℝ)| * |α - β| = |(α - β) * (m 1 : ℝ)| := by rw [abs_mul]; ring
      _ = |lu β m - lu α m| := by rw [this]
      _ ≤ |lu β m| + |lu α m| := abs_sub _ _
      _ ≤ K + L := by linarith
  have hm0 : |(m 0 : ℝ)| ≤ K + |α| * B1 := by
    have : (m 0 : ℝ) = lu α m + α * m 1 := by simp [lu]
    rw [this]
    calc |lu α m + α * m 1| ≤ |lu α m| + |α * m 1| := abs_add_le _ _
      _ ≤ K + |α| * B1 := by
        rw [abs_mul]; have := mul_le_mul_of_nonneg_left hm1 (abs_nonneg α); linarith
  have hB1nn : 0 ≤ B1 := le_trans (abs_nonneg _) hm1
  have hc : B ≤ ⌈B⌉ := Int.le_ceil B
  simp only [Set.mem_Icc, Pi.le_def]
  have h0 := abs_le.1 hm0
  have h1 := abs_le.1 hm1
  have h0' : ((m 0 : ℤ) : ℝ) ≤ ⌈B⌉ ∧ -(⌈B⌉ : ℝ) ≤ ((m 0 : ℤ) : ℝ) := by
    constructor <;> nlinarith
  have h1' : ((m 1 : ℤ) : ℝ) ≤ ⌈B⌉ ∧ -(⌈B⌉ : ℝ) ≤ ((m 1 : ℤ) : ℝ) := by
    constructor <;> nlinarith
  constructor <;> intro i <;> fin_cases i <;> simp <;> [exact_mod_cast h0'.2; exact_mod_cast h1'.2; exact_mod_cast h0'.1; exact_mod_cast h1'.1]

/-- A function with finite sublevel sets attains its minimum on a nonempty set. -/
theorem exists_argmin {S : Set (Fin 2 → ℤ)} (g : (Fin 2 → ℤ) → ℝ) (hne : S.Nonempty)
    (hfin : ∀ L, {m | m ∈ S ∧ g m ≤ L}.Finite) : ∃ m ∈ S, ∀ m' ∈ S, g m ≤ g m' := by
  obtain ⟨m0, hm0⟩ := hne
  have hF := hfin (g m0)
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image hF.toFinset g ⟨m0, hF.mem_toFinset.2 ⟨hm0, le_rfl⟩⟩
  simp only [Set.Finite.mem_toFinset] at hm hmin
  refine ⟨m, hm.1, fun m' hm' => ?_⟩
  by_cases hle : g m' ≤ g m0
  · exact hmin m' ⟨hm', hle⟩
  · exact hm.2.trans (not_le.1 hle).le

/-- If $xy > 0$ and $|x| < |y|$ then $|y - x| < |y|$. -/
theorem abs_sub_lt_of_same_sign {x y : ℝ} (hxy : 0 < x * y) (h : |x| < |y|) : |y - x| < |y| := by
  have hx : x ≠ 0 := by rintro rfl; simp at hxy
  have hx0 : 0 < |x| := abs_pos.2 hx
  have h1 : |x| * |x| < |x| * |y| := mul_lt_mul_of_pos_left h hx0
  rw [← abs_mul, ← abs_mul, abs_of_pos hxy, abs_mul_self] at h1
  rw [← sq_lt_sq]
  nlinarith

/-- **Reduced basis** for a pair of real linear forms $m_0 - \alpha m_1$, $m_0 - \beta m_1$ without nonzero integral
zeros (the geometry-of-numbers core of Lemma 3.6). -/
theorem exists_reduced_basis {α β : ℝ} (hαβ : α ≠ β) (hu : ∀ m : Fin 2 → ℤ, m ≠ 0 → lu α m ≠ 0)
    (hw : ∀ m : Fin 2 → ℤ, m ≠ 0 → lu β m ≠ 0) :
    ∃ v0 v1 : Fin 2 → ℤ, (v0 0 * v1 1 - v0 1 * v1 0 = 1 ∨ v0 0 * v1 1 - v0 1 * v1 0 = -1) ∧
      0 < lu α v0 * lu α v1 ∧ |lu α v0| < |lu α v1| ∧ lu β v0 * lu β v1 < 0 ∧
        |lu β v1| < |lu β v0| := by
  have hD : 0 < |α - β| := abs_pos.2 (sub_ne_zero.2 hαβ)
  have hu0 : ∀ m, lu α m = 0 → m = 0 := fun m h => by by_contra hm; exact hu m hm h
  -- the point `v0`
  set e : Fin 2 → ℤ := Pi.single 0 1 with he_def
  have he : e ≠ 0 := by intro h; have := congrFun h 0; simp [e] at this
  obtain ⟨v0, hv0S, hv0min⟩ := exists_argmin (S := {m | m ≠ 0 ∧ |lu α m| ≤ |lu α e|})
    (fun m => |lu β m|) ⟨e, he, le_rfl⟩
    (fun L => (finite_lu_box hαβ (|lu α e|) L).subset (fun m hm => ⟨hm.1.2, hm.2⟩))
  have hv0 : v0 ≠ 0 := hv0S.1
  have M0 : ∀ m : Fin 2 → ℤ, m ≠ 0 → |lu α m| < |lu α v0| → |lu β v0| ≤ |lu β m| :=
    fun m hm h => hv0min m ⟨hm, h.le.trans hv0S.2⟩
  have hW0 : 0 < |lu β v0| := abs_pos.2 (hw v0 hv0)
  -- the point `v1`
  have hne1 : ({m | m ≠ 0 ∧ |lu β m| < |lu β v0|} : Set (Fin 2 → ℤ)).Nonempty := by
    set t := |lu β v0| / 2 with ht
    have htpos : 0 < t := by positivity
    obtain ⟨m, hm, h1, h2⟩ := exists_int_lu (α := α) (β := β) (s := |α - β| / t) (t := t)
      (by positivity) htpos (by rw [div_mul_cancel₀ _ htpos.ne']) hαβ
    exact ⟨m, hm, by linarith⟩
  obtain ⟨v1, hv1S, hv1min⟩ := exists_argmin (S := {m | m ≠ 0 ∧ |lu β m| < |lu β v0|})
    (fun m => |lu α m|) hne1
    (fun L => (finite_lu_box hαβ L (|lu β v0|)).subset (fun m hm => ⟨hm.2, hm.1.2.le⟩))
  have hv1 : v1 ≠ 0 := hv1S.1
  have hv1W : |lu β v1| < |lu β v0| := hv1S.2
  have M1 : ∀ m : Fin 2 → ℤ, m ≠ 0 → |lu β m| < |lu β v0| → |lu α v1| ≤ |lu α m| :=
    fun m hm h => hv1min m ⟨hm, h⟩
  have hU1 : 0 < |lu α v1| := abs_pos.2 (hu v1 hv1)
  have hU0 : 0 < |lu α v0| := abs_pos.2 (hu v0 hv0)
  have hW1 : 0 < |lu β v1| := abs_pos.2 (hw v1 hv1)
  -- `|U v0| < |U v1|`
  have h01 : |lu α v0| < |lu α v1| := by
    by_contra hnot
    push Not at hnot
    have heq : |lu α v1| = |lu α v0| := by
      by_contra hne
      have hlt : |lu α v1| < |lu α v0| := lt_of_le_of_ne hnot hne
      have := M0 v1 hv1 hlt
      linarith
    rcases abs_eq_abs.1 heq with h | h
    · have : v1 - v0 = 0 := hu0 _ (by rw [lu_sub]; linarith)
      have := sub_eq_zero.1 this
      rw [this] at hv1W; exact lt_irrefl _ hv1W
    · have : v1 + v0 = 0 := hu0 _ (by rw [lu_add]; linarith)
      have := eq_neg_of_add_eq_zero_left this
      rw [this, lu_neg, abs_neg] at hv1W; exact lt_irrefl _ hv1W
  -- Minkowski: `|U v1| |W v0| ≤ |α - β|`
  have hbound : |lu α v1| * |lu β v0| ≤ |α - β| := by
    by_contra hlt
    push Not at hlt
    set P := |lu α v1| * |lu β v0| with hP
    have hPpos : 0 < P := mul_pos hU1 hW0
    set ρ := |α - β| / P with hρ
    have hρ0 : 0 < ρ := by positivity
    have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hPpos]; exact hlt
    set l := (1 + ρ) / 2 with hl
    have hl0 : 0 < l := by positivity
    have hl1 : l < 1 := by rw [hl]; linarith
    have hρP : |α - β| = ρ * P := by rw [hρ]; field_simp
    obtain ⟨m, hm, h1, h2⟩ := exists_int_lu (α := α) (β := β) (s := l * |lu α v1|) (t := l * |lu β v0|)
      (by positivity) (by positivity)
      (by
        have : l * |lu α v1| * (l * |lu β v0|) = l ^ 2 * P := by rw [hP]; ring
        rw [this, hρP]
        have key : l ^ 2 * P - ρ * P = ((1 - ρ) / 2) ^ 2 * P := by rw [hl]; ring
        linarith [mul_nonneg (sq_nonneg ((1 - ρ) / 2)) hPpos.le])
      hαβ
    have := M1 m hm (by nlinarith)
    nlinarith
  -- the determinant
  set δ : ℤ := v0 0 * v1 1 - v0 1 * v1 0 with hδdef
  have hδ : lu α v0 * lu β v1 - lu α v1 * lu β v0 = (α - β) * δ := by
    simp only [lu, hδdef]; push_cast; ring
  have hlt1 : |lu α v0| * |lu β v1| < |lu α v1| * |lu β v0| :=
    mul_lt_mul'' h01 hv1W (abs_nonneg _) (abs_nonneg _)
  have hlow : 0 < |lu α v0 * lu β v1 - lu α v1 * lu β v0| := by
    have h := abs_sub_abs_le_abs_sub (lu α v1 * lu β v0) (lu α v0 * lu β v1)
    rw [abs_sub_comm (lu α v1 * lu β v0)] at h
    rw [abs_mul, abs_mul] at h
    linarith
  have hup : |(α - β) * δ| < 2 * |α - β| := by
    rw [← hδ]
    have h := abs_sub (lu α v0 * lu β v1) (lu α v1 * lu β v0)
    rw [abs_mul, abs_mul] at h
    linarith
  rw [hδ, abs_mul] at hlow
  rw [abs_mul] at hup
  have hδ0 : 0 < |(δ : ℝ)| := (mul_pos_iff_of_pos_left hD).1 hlow
  have hδ2 : |(δ : ℝ)| < 2 := by
    by_contra hge
    push Not at hge
    nlinarith [mul_le_mul_of_nonneg_left hge hD.le]
  have hδc : δ = 1 ∨ δ = -1 := by
    have h1 : 0 < |δ| := by exact_mod_cast hδ0
    have h2 : |δ| < 2 := by exact_mod_cast hδ2
    rcases abs_cases δ with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  -- normalize the sign of `v1`
  obtain ⟨v1', hv1'c, hpos⟩ : ∃ v1', (v1' = v1 ∨ v1' = -v1) ∧ 0 < lu α v0 * lu α v1' := by
    by_cases h : 0 < lu α v0 * lu α v1
    · exact ⟨v1, Or.inl rfl, h⟩
    · refine ⟨-v1, Or.inr rfl, ?_⟩
      have hne : lu α v0 * lu α v1 ≠ 0 := mul_ne_zero (hu v0 hv0) (hu v1 hv1)
      have := lt_of_le_of_ne (not_lt.1 h) hne
      rw [lu_neg]; linarith
  have hUa : |lu α v1'| = |lu α v1| := by rcases hv1'c with rfl | rfl <;> first | rfl | simp [lu_neg]
  have hWa : |lu β v1'| = |lu β v1| := by rcases hv1'c with rfl | rfl <;> first | rfl | simp [lu_neg]
  have hδ' : v0 0 * v1' 1 - v0 1 * v1' 0 = 1 ∨ v0 0 * v1' 1 - v0 1 * v1' 0 = -1 := by
    rcases hv1'c with rfl | rfl
    · exact hδc
    · have : v0 0 * (-v1) 1 - v0 1 * (-v1) 0 = -δ := by simp [hδdef]; ring
      rw [this]; omega
  have hv1'ne : v1' ≠ 0 := by
    intro h
    have h0 : lu α (0 : Fin 2 → ℤ) = 0 := by simp [lu]
    rw [h, h0, abs_zero] at hUa
    exact hU1.ne' hUa.symm
  refine ⟨v0, v1', hδ', hpos, by rw [hUa]; exact h01, ?_, by rw [hWa]; exact hv1W⟩
  by_contra hnot
  push Not at hnot
  have hWne : lu β v0 * lu β v1' ≠ 0 := mul_ne_zero (hw v0 hv0) (hw v1' hv1'ne)
  have hWpos : 0 < lu β v1' * lu β v0 := by
    rw [mul_comm]; exact lt_of_le_of_ne hnot (Ne.symm hWne)
  have hWlt : |lu β v1'| < |lu β v0| := by rw [hWa]; exact hv1W
  have hUlt := abs_sub_lt_of_same_sign hpos (by rw [hUa]; exact h01 : |lu α v0| < |lu α v1'|)
  have hWlt' := abs_sub_lt_of_same_sign hWpos hWlt
  have hmne : v1' - v0 ≠ 0 := by
    intro h
    have := sub_eq_zero.1 h
    rw [this] at hUa
    linarith
  have := M1 (v1' - v0) hmne (by rw [lu_sub, abs_sub_comm]; exact hWlt')
  rw [lu_sub] at this
  rw [hUa] at hUlt
  linarith

/-- **Lemma 3.6** (Cassels, Ch. 13, §3, pp. 295–297): every real indefinite binary form which is anisotropic over
$\mathbb{Q}$ (no rational $\vec{x} \ne 0$ with $f(\vec{x}) = 0$) is integrally equivalent to a classically reduced form.
Cassels gives a sketch via Minkowski's linear forms theorem. -/
@[kb "cassels1978" "Ch. 13, §3, Lemma 3.6, pp. 295–297"]
theorem exists_act_isClassicallyReduced {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (hdet : F.det < 0)
    (haniso : ∀ x : Fin 2 → ℚ, x ≠ 0 → val F (fun i => (x i : ℝ)) ≠ 0) :
    ∃ T : GL (Fin 2) ℤ, IsClassicallyReduced (act T.val F) := by
  have h10 : F 1 0 = F 0 1 := hF.apply 0 1
  have hdet' : F 0 0 * F 1 1 - F 0 1 * F 0 1 < 0 := by
    rw [Matrix.det_fin_two, h10] at hdet; exact hdet
  have ha : F 0 0 ≠ 0 := by
    have := haniso ![1, 0] (by intro h; have := congrFun h 0; simp at this)
    rw [val_fin2 hF] at this
    simpa using this
  set a := F 0 0 with ha_def
  set b := F 0 1 with hb_def
  set c := F 1 1 with hc_def
  have hΔ : 0 < b ^ 2 - a * c := by nlinarith
  set sd := Real.sqrt (b ^ 2 - a * c) with hsd
  have hsd0 : 0 < sd := Real.sqrt_pos.2 hΔ
  have hsd2 : sd ^ 2 = b ^ 2 - a * c := Real.sq_sqrt hΔ.le
  set α := (-b + sd) / a with hα
  set β := (-b - sd) / a with hβ
  have hαβ : α ≠ β := by
    intro h
    rw [hα, hβ] at h
    have := (div_left_inj' ha).1 h
    linarith
  have hsum : a * (α + β) = -2 * b := by rw [hα, hβ]; field_simp; ring
  have hprod : a * α * β = c := by
    rw [hα, hβ]; field_simp
    have : (-b + sd) * (-b - sd) = a * c := by nlinarith
    rw [this]
  have hfac : ∀ x : Fin 2 → ℝ, val F x = a * (x 0 - α * x 1) * (x 0 - β * x 1) := by
    intro x
    rw [val_fin2 hF]
    linear_combination (x 0 * x 1) * hsum - (x 1) ^ 2 * hprod
  have hne : ∀ m : Fin 2 → ℤ, m ≠ 0 → lu α m ≠ 0 ∧ lu β m ≠ 0 := by
    intro m hm
    have hq := haniso (fun i => (m i : ℚ)) (by
      intro h; apply hm; ext i; have := congrFun h i; simpa using this)
    have hx : (fun i => (((m i : ℚ)) : ℝ)) = (fun i => (m i : ℝ)) := by ext i; simp
    rw [hx, hfac] at hq
    refine ⟨fun h => hq ?_, fun h => hq ?_⟩
    · have : (m 0 : ℝ) - α * (m 1 : ℝ) = 0 := h
      rw [this]; ring
    · have : (m 0 : ℝ) - β * (m 1 : ℝ) = 0 := h
      rw [this]; ring
  obtain ⟨v0, v1, hδ, hpos, hU, hneg, hW⟩ :=
    exists_reduced_basis hαβ (fun m hm => (hne m hm).1) (fun m hm => (hne m hm).2)
  set T : Matrix (Fin 2) (Fin 2) ℤ := !![v0 0, v1 0; v0 1, v1 1] with hT
  have hTdet : T.det = v0 0 * v1 1 - v0 1 * v1 0 := by
    simp [hT, Matrix.det_fin_two_of]; ring
  have hunit : IsUnit T.det := by
    rw [hTdet]; rcases hδ with h | h <;> rw [h]
    · exact isUnit_one
    · exact Int.isUnit_iff.2 (Or.inr rfl)
  refine ⟨Matrix.nonsingInvUnit T hunit, ?_⟩
  show IsClassicallyReduced (act T F)
  have hU0 : lu α v0 ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  have hW0 : lu β v0 ≠ 0 := by
    intro h; rw [h] at hneg; simp at hneg
  have hθ : 1 < lu α v1 / lu α v0 := by
    have h1 : 0 < lu α v1 / lu α v0 := by
      have : lu α v1 / lu α v0 = (lu α v0 * lu α v1) / (lu α v0) ^ 2 := by field_simp
      rw [this]; positivity
    rw [← abs_of_pos h1, abs_div, lt_div_iff₀ (abs_pos.2 hU0)]
    simpa using hU
  have hφ0 : 0 < -(lu β v1 / lu β v0) := by
    have : -(lu β v1 / lu β v0) = -(lu β v0 * lu β v1) / (lu β v0) ^ 2 := by field_simp
    rw [this]
    apply div_pos (by linarith) (by positivity)
  have hφ1 : -(lu β v1 / lu β v0) < 1 := by
    rw [← abs_of_pos hφ0, abs_neg, abs_div, div_lt_one (abs_pos.2 hW0)]
    exact hW
  refine ⟨a * lu α v0 * lu β v0, lu α v1 / lu α v0, -(lu β v1 / lu β v0),
    mul_ne_zero (mul_ne_zero ha hU0) hW0, hθ, hφ0, hφ1, fun x => ?_⟩
  rw [val_act, hfac]
  have e0 : (castM T *ᵥ x) 0 = v0 0 * x 0 + v1 0 * x 1 := by
    simp [castM, hT, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e1 : (castM T *ᵥ x) 1 = v0 1 * x 0 + v1 1 * x 1 := by
    simp [castM, hT, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e0, e1]
  have l1 : (v0 0 : ℝ) * x 0 + v1 0 * x 1 - α * (v0 1 * x 0 + v1 1 * x 1) =
      lu α v0 * x 0 + lu α v1 * x 1 := by simp only [lu]; ring
  have l2 : (v0 0 : ℝ) * x 0 + v1 0 * x 1 - β * (v0 1 * x 0 + v1 1 * x 1) =
      lu β v0 * x 0 + lu β v1 * x 1 := by simp only [lu]; ring
  rw [l1, l2]
  field_simp
  ring

end QuadFormsKB.Reduction
