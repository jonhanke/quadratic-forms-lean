/-
# Kitaoka 1993, Section 5.2: Lemma 5.2.6 (classification of binary unimodular $\mathbb Z_2$-lattices of norm $(2)$)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.2, Lemma 5.2.6, p. 77 (printed page).

**Setting.** $R = \mathbb Z_2$. A binary lattice with a basis is described by its Gram matrix $S = (B(v_i, v_j))$
(indices $0, 1$) for Kitaoka's bilinear form $B$ with $B(x, x) = Q(x)$, so that
$Q(x, y) = S_{00}x^2 + 2S_{01}xy + S_{11}y^2$ (`gramQ`). "Unimodular" means $\det S \in \mathbb Z_2^\times$;
the norm ideal being $(2)$ means (given unimodularity) that the diagonal entries $S_{00}, S_{11}$ are even, whence
$S_{01}$ is a unit. Isometry of lattices is $T = {}^tP\,S\,P$ with $\det P \in \mathbb Z_2^\times$ (`Iso`).

**Proves** `lemma526`, the classification part of Lemma 5.2.6: such a lattice is isometric to the hyperbolic plane
$\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ if it is isotropic over $\mathbb Q_2$, and to
$\begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ if it is anisotropic. The remaining assertions of Lemma 5.2.6
(about $dL$, $S(FL)$ and $Q(L)$) are `lemma526_isotropic` and `lemma526_anisotropic` in `Ch5Lemma526Inv.lean`.

**Proof.** Normalize to $S = \begin{pmatrix} 2a & 1 \\ 1 & 2b \end{pmatrix}$. If $ab$ is even (say $a$), Hensel's
lemma gives a root $t$ of $bt^2 + t + a$, and $v_1 + t v_2$ is an isotropic vector that splits off a hyperbolic plane
(`caseA`). If $a, b$ are both odd, $r = 1 - a - b$ is odd and $a r^2 + r + b \equiv 1 \pmod 8$ is a square (local
square theorem), which produces a vector of norm $2$; a further Hensel step gives a basis with Gram matrix
$\begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ (`caseB`). Isotropy is invariant under isometry (`gramQ_congr`), the
hyperbolic plane is isotropic, and $2x^2 + 2xy + 2y^2$ has no nontrivial zero over $\mathbb Q_2$ (`ani_aniso`), so
the isotropic/anisotropic dichotomy selects the case.
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import QuadFormsKB.Literature.OMeara.Sec91
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Theorem523
import QuadFormsKB.Citation

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Padic

-- Local: a global copy of Mathlib's `Nat.fact_prime_two` changed how headline statements elaborate (`ℚ_[2]`).
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem isUnit_iff_not_dvd (x : ℤ_[2]) : IsUnit x ↔ ¬ (2 : ℤ_[2]) ∣ x := by
  rw [PadicInt.isUnit_iff]
  have h := PadicInt.norm_lt_one_iff_dvd (p := 2) x
  have h2 := x.norm_le_one
  simp only [Nat.cast_ofNat] at h
  rw [← h]
  constructor
  · intro h1; simp [h1]
  · intro h1; exact le_antisymm h2 (not_lt.mp h1)

theorem parity (x : ℤ_[2]) : (∃ m, x = 2 * m) ∨ (∃ m, x = 2 * m + 1) := by
  obtain ⟨n, hn, hx⟩ := PadicInt.exists_mem_range (p := 2) x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
  obtain ⟨m, hm⟩ := hx
  simp only [Nat.cast_ofNat] at hm
  interval_cases n
  · left; exact ⟨m, by simpa using (sub_eq_iff_eq_add.mp hm)⟩
  · right; exact ⟨m, by have := sub_eq_iff_eq_add.mp hm; simpa [add_comm] using this⟩

theorem isUnit_two_mul_add_one (m : ℤ_[2]) : IsUnit (2 * m + 1) := by
  rw [isUnit_iff_not_dvd]
  intro h
  have h1 : (2 : ℤ_[2]) ∣ 1 := (dvd_add_right (dvd_mul_right 2 m)).mp h
  exact (isUnit_iff_not_dvd 1).mp isUnit_one h1

theorem even_mul_succ (k : ℤ_[2]) : (2 : ℤ_[2]) ∣ k * (k + 1) := by
  rcases parity k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨j * (2 * j + 1), by ring⟩
  · exact ⟨(2 * j + 1) * (j + 1), by ring⟩

theorem hensel_quad (A B C : ℤ_[2]) (hB : IsUnit B) (hC : (2 : ℤ_[2]) ∣ C) :
    ∃ x : ℤ_[2], A * x ^ 2 + B * x + C = 0 := by
  open Polynomial in
  have key := hensels_lemma (p := 2) (F := Polynomial.C A * X ^ 2 + Polynomial.C B * X + Polynomial.C C) (a := 0) (by
    simp
    rw [(PadicInt.isUnit_iff).mp hB]
    simpa using (PadicInt.norm_lt_one_iff_dvd (p := 2) C).mpr (by simpa using hC))
  obtain ⟨z, hz, -⟩ := key
  refine ⟨z, ?_⟩
  simpa using hz

theorem not_two_dvd_one : ¬ (2 : ℤ_[2]) ∣ 1 := (isUnit_iff_not_dvd 1).mp isUnit_one

/-! ### Isometry of Gram matrices -/

/-- Two binary Gram matrices over $\mathbb Z_2$ are *isometric*: $T = {}^tP\,S\,P$ with $\det P$ a unit. -/
def Iso (S T : Matrix (Fin 2) (Fin 2) ℤ_[2]) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) ℤ_[2], IsUnit P.det ∧ Pᵀ * S * P = T

theorem Iso.trans {S T U : Matrix (Fin 2) (Fin 2) ℤ_[2]} (h1 : Iso S T) (h2 : Iso T U) : Iso S U := by
  obtain ⟨P, hP, hP'⟩ := h1
  obtain ⟨R, hR, hR'⟩ := h2
  refine ⟨P * R, by rw [det_mul]; exact hP.mul hR, ?_⟩
  rw [transpose_mul, ← hR', ← hP']
  simp only [Matrix.mul_assoc]

theorem Iso.symm {S T : Matrix (Fin 2) (Fin 2) ℤ_[2]} (h : Iso S T) : Iso T S := by
  obtain ⟨P, hP, hP'⟩ := h
  have hP1 : IsUnit P := (isUnit_iff_isUnit_det P).mpr hP
  have hi : IsUnit P⁻¹ := (isUnit_nonsing_inv_iff).mpr hP1
  refine ⟨P⁻¹, (isUnit_iff_isUnit_det _).mp hi, ?_⟩
  rw [← hP']
  have e1 : P * P⁻¹ = 1 := mul_nonsing_inv P hP
  have e2 : (P⁻¹)ᵀ * Pᵀ = 1 := by rw [← transpose_mul, e1, transpose_one]
  calc (P⁻¹)ᵀ * (Pᵀ * S * P) * P⁻¹ = ((P⁻¹)ᵀ * Pᵀ) * S * (P * P⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = S := by rw [e1, e2]; simp

theorem iso_of_entries {p q r α β γ δ p' q' r' : ℤ_[2]} (hdet : IsUnit (α * δ - β * γ))
    (h00 : α * (p * α + q * γ) + γ * (q * α + r * γ) = p')
    (h01 : α * (p * β + q * δ) + γ * (q * β + r * δ) = q')
    (_h10 : β * (p * α + q * γ) + δ * (q * α + r * γ) = q')
    (h11 : β * (p * β + q * δ) + δ * (q * β + r * δ) = r') :
    Iso !![p, q; q, r] !![p', q'; q', r'] := by
  refine ⟨!![α, β; γ, δ], by rwa [det_fin_two_of], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← h00, ← h01, ← h11] <;> ring

theorem iso_swap (p q r : ℤ_[2]) : Iso !![p, q; q, r] !![r, q; q, p] :=
  iso_of_entries (α := 0) (β := 1) (γ := 1) (δ := 0) (by simp) (by ring) (by ring) (by ring) (by ring)

theorem iso_diag (p q r d₁ d₂ : ℤ_[2]) (h₁ : IsUnit d₁) (h₂ : IsUnit d₂) :
    Iso !![p, q; q, r] !![p * d₁ ^ 2, q * (d₁ * d₂); q * (d₁ * d₂), r * d₂ ^ 2] :=
  iso_of_entries (α := d₁) (β := 0) (γ := 0) (δ := d₂) (by simpa using h₁.mul h₂) (by ring) (by ring)
    (by ring) (by ring)

theorem iso_lower (p q r t : ℤ_[2]) :
    Iso !![p, q; q, r] !![p + 2 * q * t + r * t ^ 2, q + r * t; q + r * t, r] :=
  iso_of_entries (α := 1) (β := 0) (γ := t) (δ := 1) (by simp) (by ring) (by ring) (by ring) (by ring)

theorem iso_upper (p q r x : ℤ_[2]) :
    Iso !![p, q; q, r] !![p, p * x + q; p * x + q, p * x ^ 2 + 2 * q * x + r] :=
  iso_of_entries (α := 1) (β := x) (γ := 0) (δ := 1) (by simp) (by ring) (by ring) (by ring) (by ring)

theorem iso_congr {S T T' : Matrix (Fin 2) (Fin 2) ℤ_[2]} (h : Iso S T) (e : T = T') : Iso S T' := e ▸ h

/-- The hyperbolic plane Gram matrix. -/
def hypM : Matrix (Fin 2) (Fin 2) ℤ_[2] := !![0, 1; 1, 0]
/-- The anisotropic dyadic plane Gram matrix. -/
def aniM : Matrix (Fin 2) (Fin 2) ℤ_[2] := !![2, 1; 1, 2]

theorem mat_eq {a b c d a' b' c' d' : ℤ_[2]} (h1 : a = a') (h2 : b = b') (h3 : c = c') (h4 : d = d') :
    !![a, b; c, d] = !![a', b'; c', d'] := by
  subst h1 h2 h3 h4; rfl

theorem caseA (a b : ℤ_[2]) (ha : (2 : ℤ_[2]) ∣ a) : Iso !![2 * a, 1; 1, 2 * b] hypM := by
  obtain ⟨t, ht⟩ := hensel_quad b 1 a isUnit_one ha
  have hu : IsUnit (1 + 2 * b * t) := by
    have := isUnit_two_mul_add_one (b * t)
    rwa [show 2 * (b * t) + 1 = 1 + 2 * b * t by ring] at this
  obtain ⟨ci, hci⟩ := hu.exists_right_inv
  have hci' : IsUnit ci := isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact hci⟩
  have s1 := iso_lower (2 * a) 1 (2 * b) t
  have s2 := iso_diag (2 * a + 2 * 1 * t + 2 * b * t ^ 2) (1 + 2 * b * t) (2 * b) 1 ci isUnit_one hci'
  have s3 := iso_upper (0 : ℤ_[2]) 1 (2 * b * ci ^ 2) (-(b * ci ^ 2))
  have s2' := iso_congr (T' := !![0, 1; 1, 2 * b * ci ^ 2]) s2
    (mat_eq (by linear_combination 2 * ht) (by linear_combination hci) (by linear_combination hci) (by ring))
  have s3' := iso_congr (T' := hypM) s3
    (mat_eq (by ring) (by ring) (by ring) (by ring))
  exact (s1.trans s2').trans s3'

theorem stage3 (c' x : ℤ_[2]) (hx : (4 * c' - 1) * x ^ 2 + (1 - 4 * c') * x + (c' - 1) = 0) :
    Iso !![2, 1; 1, 2 * c'] aniM :=
  iso_of_entries (α := 1) (β := x) (γ := 0) (δ := 1 - 2 * x)
    (by
      rw [show (1 : ℤ_[2]) * (1 - 2 * x) - x * 0 = 2 * (-x) + 1 by ring]
      exact isUnit_two_mul_add_one _)
    (by ring) (by ring) (by ring) (by linear_combination 2 * hx)

theorem caseB (a b m n : ℤ_[2]) (ha : a = 2 * m + 1) (hb : b = 2 * n + 1) :
    Iso !![2 * a, 1; 1, 2 * b] aniM := by
  have : HenselianLocalRing ℤ_[2] := QuadFormsKB.Kitaoka.henselianLocalRing_padicInt 2
  have hau : IsUnit a := ha ▸ isUnit_two_mul_add_one m
  set r := 1 - a - b with hr
  set k : ℤ_[2] := -m - n - 1 with hk
  have hrk : r = 2 * k + 1 := by rw [hr, ha, hb, hk]; ring
  have hmem : a * (k * (k + 1)) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_not_dvd, not_not]
    exact Dvd.dvd.mul_left (even_mul_succ k) a
  obtain ⟨s, hs⟩ := OMeara.isSquare_one_add_four_mul hmem
  have hs2 : s * s = a * r ^ 2 + r + b := by
    rw [← hs, hrk, ha, hb, hk]; ring
  have hsu : IsUnit (s * s) := by
    rw [← hs, show 1 + 4 * (a * (k * (k + 1))) = 2 * (2 * (a * (k * (k + 1)))) + 1 by ring]
    exact isUnit_two_mul_add_one _
  have hsu' : IsUnit s := (IsUnit.mul_iff.mp hsu).1
  obtain ⟨si, hsi⟩ := hsu'.exists_right_inv
  have hsiu : IsUnit si := isUnit_iff_exists_inv.mpr ⟨s, by rw [mul_comm]; exact hsi⟩
  have hcu : IsUnit ((1 + 2 * a * r) * si) := by
    have := isUnit_two_mul_add_one (a * r)
    rw [show 2 * (a * r) + 1 = 1 + 2 * a * r by ring] at this
    exact this.mul hsiu
  obtain ⟨ci, hci⟩ := hcu.exists_right_inv
  have hciu : IsUnit ci := isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact hci⟩
  have s1 := iso_swap (2 * a) 1 (2 * b)
  have s2 := iso_lower (2 * b) 1 (2 * a) r
  have s3 := iso_diag (2 * b + 2 * 1 * r + 2 * a * r ^ 2) (1 + 2 * a * r) (2 * a) si ci hsiu hciu
  have s3' := iso_congr (T' := !![2, 1; 1, 2 * (a * ci ^ 2)]) s3
    (mat_eq (by linear_combination (-2 * si ^ 2) * hs2 + 2 * (s * si + 1) * hsi) (by linear_combination hci)
      (by linear_combination hci) (by ring))
  have hc'u : IsUnit (a * ci ^ 2) := hau.mul (hciu.pow 2)
  have hc'odd : (2 : ℤ_[2]) ∣ a * ci ^ 2 - 1 := by
    rcases parity (a * ci ^ 2) with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact absurd ⟨j, hj⟩ ((isUnit_iff_not_dvd _).mp hc'u)
    · exact ⟨j, by rw [hj]; ring⟩
  obtain ⟨x, hx⟩ := hensel_quad (4 * (a * ci ^ 2) - 1) (1 - 4 * (a * ci ^ 2)) (a * ci ^ 2 - 1)
    (by
      rw [show 1 - 4 * (a * ci ^ 2) = 2 * (-(2 * (a * ci ^ 2))) + 1 by ring]
      exact isUnit_two_mul_add_one _) hc'odd
  exact ((s1.trans s2).trans s3').trans (stage3 _ x hx)

theorem classify (a b : ℤ_[2]) : Iso !![2 * a, 1; 1, 2 * b] hypM ∨ Iso !![2 * a, 1; 1, 2 * b] aniM := by
  rcases parity a with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl (caseA a b ⟨m, hm⟩)
  · rcases parity b with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact Or.inl ((iso_swap (2 * a) 1 (2 * b)).trans (caseA b a ⟨n, hn⟩))
    · exact Or.inr (caseB a b m n hm hn)

/-! ### Isotropy over $\mathbb Q_2$ -/

/-- The quadratic form on $\mathbb Q_2^2$ of the lattice with Gram matrix $S$:
$Q(x, y) = S_{00}x^2 + 2S_{01}xy + S_{11}y^2$ (Kitaoka's $B$ with $B(x,x) = Q(x)$). -/
def gramQ (S : Matrix (Fin 2) (Fin 2) ℤ_[2]) (x y : ℚ_[2]) : ℚ_[2] :=
  (S 0 0 : ℚ_[2]) * x ^ 2 + 2 * (S 0 1 : ℚ_[2]) * x * y + (S 1 1 : ℚ_[2]) * y ^ 2

theorem gramQ_congr (S T P : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hS : S 1 0 = S 0 1) (h : Pᵀ * S * P = T)
    (x y : ℚ_[2]) :
    gramQ T x y = gramQ S ((P 0 0 : ℚ_[2]) * x + (P 0 1 : ℚ_[2]) * y) ((P 1 0 : ℚ_[2]) * x + (P 1 1 : ℚ_[2]) * y) := by
  subst h
  simp only [gramQ, Matrix.mul_apply, Fin.sum_univ_two, transpose_apply, hS]
  push_cast
  ring

theorem isotropic_transfer (S T P : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hS : S 1 0 = S 0 1)
    (hP : IsUnit P.det) (h : Pᵀ * S * P = T)
    (hT : ∃ x y : ℚ_[2], (x, y) ≠ 0 ∧ gramQ T x y = 0) :
    ∃ x y : ℚ_[2], (x, y) ≠ 0 ∧ gramQ S x y = 0 := by
  obtain ⟨x, y, hxy, hq⟩ := hT
  refine ⟨(P 0 0 : ℚ_[2]) * x + (P 0 1 : ℚ_[2]) * y, (P 1 0 : ℚ_[2]) * x + (P 1 1 : ℚ_[2]) * y, ?_, ?_⟩
  · intro h0
    have h1 : (P 0 0 : ℚ_[2]) * x + (P 0 1 : ℚ_[2]) * y = 0 := congrArg Prod.fst h0
    have h2 : (P 1 0 : ℚ_[2]) * x + (P 1 1 : ℚ_[2]) * y = 0 := congrArg Prod.snd h0
    rw [det_fin_two] at hP
    have hd : ((P 0 0 * P 1 1 - P 0 1 * P 1 0 : ℤ_[2]) : ℚ_[2]) ≠ 0 := by
      exact fun h => hP.ne_zero (PadicInt.coe_eq_zero.mp h)
    push_cast at hd
    apply hxy
    have hx : ((P 0 0 : ℚ_[2]) * P 1 1 - P 0 1 * P 1 0) * x = 0 := by
      linear_combination (P 1 1 : ℚ_[2]) * h1 - (P 0 1 : ℚ_[2]) * h2
    have hy : ((P 0 0 : ℚ_[2]) * P 1 1 - P 0 1 * P 1 0) * y = 0 := by
      linear_combination (P 0 0 : ℚ_[2]) * h2 - (P 1 0 : ℚ_[2]) * h1
    rw [Prod.mk_eq_zero]
    exact ⟨(mul_eq_zero.mp hx).resolve_left hd, (mul_eq_zero.mp hy).resolve_left hd⟩
  · rw [← gramQ_congr S T P hS h]; exact hq

theorem ani_core (x y : ℚ_[2]) (hxy : ‖y‖ ≤ ‖x‖) (h : x ^ 2 + x * y + y ^ 2 = 0) : x = 0 := by
  by_contra hx
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hz : ‖y / x‖ ≤ 1 := by rw [norm_div]; exact (div_le_one hxn).mpr hxy
  set z : ℤ_[2] := ⟨y / x, hz⟩ with hzdef
  have hz0 : (z : ℚ_[2]) ^ 2 + z + 1 = 0 := by
    have : (z : ℚ_[2]) = y / x := rfl
    rw [this]
    field_simp
    linear_combination h
  have hz1 : z ^ 2 + z + 1 = 0 := by
    have : ((z ^ 2 + z + 1 : ℤ_[2]) : ℚ_[2]) = 0 := by push_cast; exact hz0
    exact PadicInt.coe_eq_zero.mp this
  rcases parity z with ⟨m, hm⟩ | ⟨m, hm⟩
  · apply not_two_dvd_one
    exact ⟨-(2 * m ^ 2 + m), by rw [hm] at hz1; linear_combination hz1⟩
  · apply not_two_dvd_one
    exact ⟨-(2 * m ^ 2 + 3 * m) - 1, by rw [hm] at hz1; linear_combination hz1⟩

theorem ani_aniso (x y : ℚ_[2]) (h : gramQ aniM x y = 0) : x = 0 ∧ y = 0 := by
  have h' : x ^ 2 + x * y + y ^ 2 = 0 := by
    simp only [gramQ, aniM] at h
    simp at h
    have h2c : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by rfl
    rw [h2c] at h
    have h2 : (2 : ℚ_[2]) * (x ^ 2 + x * y + y ^ 2) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  rcases le_total ‖y‖ ‖x‖ with hle | hle
  · have hx := ani_core x y hle h'
    subst hx
    refine ⟨rfl, ?_⟩
    simpa using h'
  · have hy := ani_core y x hle (by linear_combination h')
    subst hy
    refine ⟨?_, rfl⟩
    simpa using h'

theorem hyp_isotropic : ∃ x y : ℚ_[2], (x, y) ≠ 0 ∧ gramQ hypM x y = 0 :=
  ⟨1, 0, by simp, by simp [gramQ, hypM]⟩

/-! ### The classification -/

/-- **Kitaoka 1993, Lemma 5.2.6** (p. 77), classification part. Let $S$ be a symmetric $2 \times 2$ matrix over
$\mathbb Z_2$ with $\det S$ a unit and even diagonal entries (a unimodular binary lattice with norm ideal $(2)$).
If $Q_S$ has a nontrivial zero over $\mathbb Q_2$, then ${}^tP\,S\,P = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$
for some $P$ with $\det P \in \mathbb Z_2^\times$; otherwise
${}^tP\,S\,P = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ for such a $P$. Unconditional (no inputs). -/
@[kb "kitaoka1993" "§5.2, Lemma 5.2.6, p. 77 (classification)"]
theorem lemma526 (S : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hS : Sᵀ = S) (hu : IsUnit S.det)
    (h0 : 2 ∣ S 0 0) (h1 : 2 ∣ S 1 1) :
    ((∃ x y : ℚ_[2], (x, y) ≠ 0 ∧ gramQ S x y = 0) →
        ∃ P : Matrix (Fin 2) (Fin 2) ℤ_[2], IsUnit P.det ∧ Pᵀ * S * P = !![0, 1; 1, 0]) ∧
    ((¬ ∃ x y : ℚ_[2], (x, y) ≠ 0 ∧ gramQ S x y = 0) →
        ∃ P : Matrix (Fin 2) (Fin 2) ℤ_[2], IsUnit P.det ∧ Pᵀ * S * P = !![2, 1; 1, 2]) := by
  have hsym : S 1 0 = S 0 1 := by
    have := congrFun (congrFun hS 0) 1
    simpa [transpose_apply] using this
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  have huu : IsUnit (S 0 1) := by
    rw [isUnit_iff_not_dvd]
    rintro ⟨w, hw⟩
    rw [det_fin_two, hsym, ha, hb, hw] at hu
    apply (isUnit_iff_not_dvd _).mp hu
    exact ⟨2 * a * b - 2 * w ^ 2, by ring⟩
  obtain ⟨ui, hui⟩ := huu.exists_right_inv
  have huiu : IsUnit ui := isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact hui⟩
  have hSe : S = !![2 * a, S 0 1; S 0 1, 2 * b] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hsym]
  have s0 := iso_congr (T' := !![2 * a, 1; 1, 2 * (b * ui ^ 2)])
    (iso_diag (2 * a) (S 0 1) (2 * b) 1 ui isUnit_one huiu)
    (mat_eq (by ring) (by linear_combination hui) (by linear_combination hui) (by ring))
  rw [← hSe] at s0
  have symH : hypM 1 0 = hypM 0 1 := by simp [hypM]
  have symA : aniM 1 0 = aniM 0 1 := by simp [aniM]
  rcases classify a (b * ui ^ 2) with hc | hc
  · have hI := s0.trans hc
    obtain ⟨P, hP, hP'⟩ := hI
    refine ⟨fun _ => ⟨P, hP, hP'⟩, fun hn => (hn ?_).elim⟩
    exact isotropic_transfer S hypM P hsym hP hP' hyp_isotropic
  · have hI := s0.trans hc
    obtain ⟨P, hP, hP'⟩ := id hI
    refine ⟨fun hi => ?_, fun _ => ⟨P, hP, hP'⟩⟩
    obtain ⟨Q, hQ, hQ'⟩ := hI.symm
    obtain ⟨x, y, hxy, hq⟩ := isotropic_transfer aniM S Q symA hQ hQ' hi
    obtain ⟨rfl, rfl⟩ := ani_aniso x y hq
    exact (hxy rfl).elim


end QuadFormsKB.Kitaoka.Padic
