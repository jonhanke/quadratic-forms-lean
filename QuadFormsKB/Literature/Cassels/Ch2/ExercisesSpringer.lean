/-
# Cassels, Chapter 2: Examples 15, 19, 20 (pp. 32-33)

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, *Examples*, pp. 32-33.

**Setting.** $k$ = `F` is a field. A quadratic form in $n$ variables is a Mathlib `QuadraticForm F (Fin n → F)`
(`[Invertible (2 : F)]`, so that it has a Gram matrix `toMatrix'`); indices are $0$-based. Its extension of
scalars to a commutative $F$-algebra $K$ is `extendForm Q K`, the form on $K^{n}$ with the same Gram matrix.
"Isotropic over $K$" means `¬ (extendForm Q K).Anisotropic`. The rational function field $k(t)$ is Mathlib's
`RatFunc F` with $t$ = `RatFunc.X`.

**Proves.**
* Ex. 15 (p. 32), Springer's theorem: a form isotropic over a finite extension of odd degree is isotropic
  (`ex15`); regularity is not needed (see the docstring).
* Ex. 19 (p. 33), the Aubry-Brumer theorem: $g + t\,h$ is isotropic over $k(t)$ iff $g$ and $h$ have a common
  non-trivial zero over $k$ (`ex19`).
* Ex. 20 (p. 33): two forms with a common non-trivial zero over a finite extension of odd degree have one over
  $k$ (`ex20`).

**Method.** Everything is proved unconditionally, with matrices $M$ and the pairing `mbil M u v`
$= \sum_{i,j} u_i M_{ij} v_j$. Ex. 19 is Aubry's descent on polynomial zeros of least degree (`pencil_core`);
Ex. 15 is the descent of the hint on polynomial vectors modulo an irreducible polynomial of odd degree
(`springer_poly`), assembled along a tower of simple extensions `AdjoinRoot p` (`tower_core`), so no primitive
element theorem is needed and no separability hypothesis arises. Ex. 20 uses the same tower together with
Ex. 19 for the simple step (`pencil_simple`); it does not need $[K(t) : k(t)] = [K : k]$.

**Not formalized here.** Nothing from Ex. 15, 19, 20 is omitted.
-/
import QuadFormsKB.Literature.OMeara.Sec43CD
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field

open Polynomial Module

noncomputable section

namespace QuadFormsKB.Cassels.Ch2Ex

section Prelim

variable {F : Type*} [Field F] {n : ℕ}

/-- The pairing $u^{T} M v = \sum_{i,j} u_i M_{ij} v_j$ of two vectors through a matrix. -/
def mbil {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R :=
  ∑ i, ∑ j, u i * (M i j * v j)

/-- The pairing $u^{T} M v$ of two polynomial vectors through a constant matrix $M$. -/
def polyBil (M : Matrix (Fin n) (Fin n) F) (u v : Fin n → F[X]) : F[X] :=
  mbil (M.map C) u v

lemma polyBil_top (M : Matrix (Fin n) (Fin n) F) (u v : Fin n → F[X]) (a b : ℕ)
    (hu : ∀ i, (u i).natDegree ≤ a) (hv : ∀ i, (v i).natDegree ≤ b) :
    (polyBil M u v).natDegree ≤ a + b ∧
      (polyBil M u v).coeff (a + b) = mbil M (fun i => (u i).coeff a) (fun j => (v j).coeff b) := by
  simp only [polyBil, mbil, Matrix.map_apply]
  refine ⟨?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i _ => natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine (natDegree_mul_le).trans (Nat.add_le_add (hu i) ?_)
    exact (natDegree_C_mul_le _ _).trans (hv j)
  · simp only [finsetSum_coeff]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_mul_add_eq_of_natDegree_le (hu i) ((natDegree_C_mul_le _ _).trans (hv j)), coeff_C_mul]

lemma map_mbil {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R)
    (u v : Fin n → R) :
    φ (mbil M u v) = mbil (M.map φ) (fun i => φ (u i)) (fun i => φ (v i)) := by
  simp [mbil, map_sum]

lemma mbil_add_left {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) :
    mbil M (u + u') v = mbil M u v + mbil M u' v := by
  simp only [mbil, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma mbil_add_right {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) :
    mbil M u (v + v') = mbil M u v + mbil M u v' := by
  simp only [mbil, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma mbil_smul_left {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (c : R) (u v : Fin n → R) :
    mbil M (c • u) v = c * mbil M u v := by
  simp only [mbil, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma mbil_smul_right {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (c : R) (u v : Fin n → R) :
    mbil M u (c • v) = c * mbil M u v := by
  simp only [mbil, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma mbil_comm {R : Type*} [CommRing R] {M : Matrix (Fin n) (Fin n) R} (hM : M.IsSymm)
    (u v : Fin n → R) : mbil M u v = mbil M v u := by
  unfold mbil
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hM.apply i j]
  ring

/-- Expansion of the quadratic form of a symmetric matrix at $u + s v$. -/
lemma mbil_add_smul_self {R : Type*} [CommRing R] {M : Matrix (Fin n) (Fin n) R} (hM : M.IsSymm)
    (u v : Fin n → R) (s : R) :
    mbil M (u + s • v) (u + s • v) =
      mbil M u u + s ^ 2 * mbil M v v + 2 * s * mbil M u v := by
  rw [mbil_add_left, mbil_add_right, mbil_add_right, mbil_smul_left, mbil_smul_right,
    mbil_smul_right, mbil_smul_left, mbil_comm hM v u]
  ring

lemma mbil_map_C (M : Matrix (Fin n) (Fin n) F) (u v : Fin n → F) :
    mbil (M.map C) (fun i => C (u i)) (fun j => C (v j)) = C (mbil M u v) := by
  simp [mbil, map_sum]

lemma polyBil_const (M : Matrix (Fin n) (Fin n) F) (u v : Fin n → F) :
    polyBil M (fun i => C (u i)) (fun j => C (v j)) = C (mbil M u v) :=
  mbil_map_C M u v

lemma key_coeffs {P0 P1 : F[X]} {m : ℕ} (hP0 : ∀ N, 2 * m ≤ N → P0.coeff N = 0)
    (hP1 : ∀ N, m < N → P1.coeff N = 0) (g0 h0 : F)
    (h : P0 + X ^ m * P1 + X ^ (2 * m) * (C g0 + X * C h0) = 0) :
    h0 = 0 ∧ g0 + P1.coeff m = 0 := by
  have h1 := congrArg (fun p => p.coeff (2 * m + 1)) h
  have h2 := congrArg (fun p => p.coeff (2 * m)) h
  simp only [mul_add, coeff_add, coeff_X_pow_mul', coeff_zero] at h1 h2
  have e1 : 2 * m + 1 - m = m + 1 := by omega
  have e2 : 2 * m + 1 - 2 * m = 1 := by omega
  have e3 : 2 * m - m = m := by omega
  have e4 : 2 * m - 2 * m = 0 := by omega
  have c1 : m ≤ 2 * m + 1 := by omega
  have c2 : 2 * m ≤ 2 * m + 1 := by omega
  have c3 : m ≤ 2 * m := by omega
  rw [e1, e2, hP0 _ (by omega), hP1 _ (by omega)] at h1
  rw [e3, e4, hP0 _ (by omega)] at h2
  simp only [c1, c2, c3, le_refl, ↓reduceIte, coeff_C, coeff_X_mul] at h1 h2
  simp at h1 h2
  exact ⟨h1, by linear_combination h2⟩

lemma mbil_zero_left {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    mbil M 0 v = 0 := by
  simp [mbil]

lemma polyBil_add_smul {M : Matrix (Fin n) (Fin n) F} (hM : M.IsSymm) (c : Fin n → F[X])
    (d : Fin n → F) (s : F[X]) :
    polyBil M (c + s • fun i => C (d i)) (c + s • fun i => C (d i)) =
      polyBil M c c + s ^ 2 * C (mbil M d d) + 2 * s * polyBil M c (fun i => C (d i)) := by
  unfold polyBil
  rw [mbil_add_smul_self (hM.map C), mbil_map_C]

lemma polyBil_add_smul_right (M : Matrix (Fin n) (Fin n) F) (c : Fin n → F[X])
    (d : Fin n → F) (s : F[X]) :
    polyBil M (c + s • fun i => C (d i)) (fun i => C (d i)) =
      polyBil M c (fun i => C (d i)) + s * C (mbil M d d) := by
  unfold polyBil
  rw [mbil_add_left, mbil_smul_left, mbil_map_C]

lemma polyBil_smul_self {M : Matrix (Fin n) (Fin n) F} (hM : M.IsSymm) (d : Fin n → F) (s : F[X]) :
    polyBil M (s • fun i => C (d i)) (s • fun i => C (d i)) = s ^ 2 * C (mbil M d d) := by
  have := polyBil_add_smul hM 0 d s
  rw [zero_add] at this
  unfold polyBil at this ⊢
  rw [this, mbil_zero_left, mbil_zero_left]
  ring

end Prelim

section Pencil

variable {F : Type*} [Field F] {n : ℕ}

/-- The core of Aubry's descent for Ex. 19. -/
lemma pencil_core {G H : Matrix (Fin n) (Fin n) F} (hG : G.IsSymm) (hH : H.IsSymm)
    (hno : ∀ a : Fin n → F, a ≠ 0 → mbil G a a = 0 → mbil H a a = 0 → False) :
    ∀ (m : ℕ) (b : Fin n → F[X]), b ≠ 0 → (∀ i, (b i).natDegree ≤ m) →
      polyBil G b b + X * polyBil H b b = 0 → False := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro b hb0 hbd hf
  rcases m with _ | m'
  · have hb' : (fun i => C ((b i).coeff 0)) = b := by
      funext i; exact (eq_C_of_natDegree_le_zero (hbd i)).symm
    have hcne : (fun i => (b i).coeff 0) ≠ 0 := by
      intro h
      apply hb0
      rw [← hb']
      funext i
      simp [congrFun h i]
    rw [← hb', polyBil_const, polyBil_const] at hf
    have h0 := congrArg (fun p => p.coeff 0) hf
    have h1 := congrArg (fun p => p.coeff 1) hf
    simp [coeff_C] at h0 h1
    exact hno _ hcne h0 h1
  · set d : Fin n → F := fun i => (b i).coeff (m' + 1) with hd_def
    set c : Fin n → F[X] := fun i => b i - C (d i) * X ^ (m' + 1) with hc_def
    have hcd : ∀ i, (c i).natDegree ≤ m' := by
      intro i
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      simp only [hc_def, coeff_sub, coeff_C_mul_X_pow]
      by_cases h : N = m' + 1
      · subst h; simp [hd_def]
      · simp only [h, ↓reduceIte]; rw [coeff_eq_zero_of_natDegree_lt (by have := hbd i; omega)]; simp
    have hbi : ∀ i, b i = c i + X ^ (m' + 1) * C (d i) := fun i => by simp only [hc_def]; ring
    have hbdec : b = c + (X ^ (m' + 1) : F[X]) • (fun i => C (d i)) := by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hbi i
    by_cases hd0 : d = 0
    · refine ih m' (by omega) b hb0 (fun i => ?_) hf
      have : b i = c i := by rw [hbi i]; simp [congrFun hd0 i]
      rw [this]; exact hcd i
    have hEG := polyBil_add_smul hG c d (X ^ (m' + 1))
    have hEH := polyBil_add_smul hH c d (X ^ (m' + 1))
    rw [← hbdec] at hEG hEH
    have hRG := polyBil_add_smul_right G c d (X ^ (m' + 1))
    have hRH := polyBil_add_smul_right H c d (X ^ (m' + 1))
    rw [← hbdec] at hRG hRH
    have hCd : ∀ i : Fin n, ((fun i => C (d i)) i).natDegree ≤ 0 := fun i => by simp
    obtain ⟨hT1deg, -⟩ := polyBil_top G c c m' m' hcd hcd
    obtain ⟨hT3deg, -⟩ := polyBil_top H c c m' m' hcd hcd
    obtain ⟨hT2deg, -⟩ := polyBil_top G c (fun i => C (d i)) m' 0 hcd hCd
    obtain ⟨hT4deg, hT4c⟩ := polyBil_top H c (fun i => C (d i)) m' 0 hcd hCd
    simp only [add_zero, coeff_C_zero] at hT2deg hT4deg hT4c
    generalize hT2 : polyBil G c (fun i => C (d i)) = T2 at *
    generalize hT4 : polyBil H c (fun i => C (d i)) = T4 at *
    generalize hP0 : polyBil G c c + X * polyBil H c c = P0 at *
    generalize hbeta : mbil H (fun i => (c i).coeff m') d = β at *
    have hP0deg : P0.natDegree ≤ m' + m' + 1 := by
      rw [← hP0]
      refine (natDegree_add_le _ _).trans (max_le (hT1deg.trans (by omega)) ?_)
      exact (natDegree_mul_le_of_le natDegree_X_le hT3deg).trans (by omega)
    have hP1deg : ∀ N, m' + 1 < N → (2 * (T2 + X * T4)).coeff N = 0 := by
      intro N hN
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      rw [coeff_ofNat_mul, coeff_add, coeff_X_mul,
        coeff_eq_zero_of_natDegree_lt (by omega : T2.natDegree < N' + 1),
        coeff_eq_zero_of_natDegree_lt (by omega : T4.natDegree < N')]
      simp
    have hP1c : (2 * (T2 + X * T4)).coeff (m' + 1) = 2 * β := by
      rw [coeff_ofNat_mul, coeff_add, coeff_X_mul,
        coeff_eq_zero_of_natDegree_lt (by omega : T2.natDegree < m' + 1), hT4c]
      simp
    have hkey : P0 + X ^ (m' + 1) * (2 * (T2 + X * T4)) +
        X ^ (2 * (m' + 1)) * (C (mbil G d d) + X * C (mbil H d d)) = 0 := by
      rw [hEG, hEH] at hf
      rw [← hP0]
      linear_combination hf
    obtain ⟨hhd0, hgb⟩ := key_coeffs (m := m' + 1)
      (fun N hN => coeff_eq_zero_of_natDegree_lt (by omega)) hP1deg _ _ hkey
    rw [hP1c] at hgb
    have hgd0 : mbil G d d ≠ 0 := fun h => hno d hd0 h hhd0
    generalize hgd : mbil G d d = gd at *
    obtain ⟨k, hk⟩ : ∃ k : F, k = 2 * gd⁻¹ := ⟨_, rfl⟩
    obtain ⟨Bb, hBb⟩ : ∃ Bb : F[X],
        Bb = polyBil G b (fun i => C (d i)) + X * polyBil H b (fun i => C (d i)) := ⟨_, rfl⟩
    obtain ⟨lam, hlam⟩ : ∃ lam : F[X], lam = C k * Bb := ⟨_, rfl⟩
    have hEG2 := polyBil_add_smul hG b d (-lam)
    have hEH2 := polyBil_add_smul hH b d (-lam)
    have hkg : k * gd = 2 := by rw [hk]; field_simp
    have hkb : k * β = -1 := by
      rw [hk]; field_simp; linear_combination hgb
    have hkgd : C k * C gd = 2 := by
      rw [← C_mul, hkg]; exact map_ofNat C 2
    have hfbs : polyBil G (b + (-lam) • fun i => C (d i)) (b + (-lam) • fun i => C (d i)) +
        X * polyBil H (b + (-lam) • fun i => C (d i)) (b + (-lam) • fun i => C (d i)) = 0 := by
      rw [hEG2, hEH2, hgd, hhd0]
      simp only [map_zero, mul_zero, add_zero]
      linear_combination hf + lam * C gd * hlam + lam * Bb * hkgd + 2 * lam * hBb
    have hr : ∀ N, m' + 1 ≤ N → (X ^ (m' + 1) - lam).coeff N = 0 := by
      intro N hN
      have hlam' : lam = C k * (T2 + X ^ (m' + 1) * C gd + X * T4) := by
        rw [hlam, hBb, hRG, hRH, hhd0]
        simp only [map_zero, mul_zero, add_zero]
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      rw [hlam', coeff_sub, coeff_C_mul, coeff_add, coeff_add, coeff_X_mul,
        coeff_eq_zero_of_natDegree_lt (by omega : T2.natDegree < N' + 1), coeff_X_pow,
        coeff_X_pow_mul']
      rcases Nat.eq_or_lt_of_le (show m' ≤ N' by omega) with h | h
      · subst h
        simp only [hT4c, coeff_C, le_refl, Nat.sub_self]
        simp
        linear_combination -hkg - hkb
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : T4.natDegree < N')]
        simp [coeff_C, show N' ≠ m' by omega, show N' - m' ≠ 0 by omega]
    have hrdeg : (X ^ (m' + 1) - lam).natDegree ≤ m' :=
      natDegree_le_iff_coeff_eq_zero.mpr fun N hN => hr N hN
    have hbsdeg : ∀ i, ((b + (-lam) • fun i => C (d i)) i).natDegree ≤ m' := by
      intro i
      have : (b + (-lam) • fun i => C (d i)) i = c i + (X ^ (m' + 1) - lam) * C (d i) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [hbi i]; ring
      rw [this]
      exact (natDegree_add_le _ _).trans
        (max_le (hcd i) ((natDegree_mul_le_of_le hrdeg (natDegree_C _).le).trans (by omega)))
    have hbs0 : (b + (-lam) • fun i => C (d i)) ≠ 0 := by
      intro h0
      have hb_eq : b = lam • fun i => C (d i) := by
        have := eq_neg_of_add_eq_zero_left h0
        rw [this, neg_smul, neg_neg]
      rw [hb_eq, polyBil_smul_self hG, polyBil_smul_self hH, hgd, hhd0] at hf
      simp only [map_zero, mul_zero, add_zero] at hf
      have hC : (C gd : F[X]) ≠ 0 := by simpa using hgd0
      have hl : lam = 0 := by
        rcases mul_eq_zero.mp hf with h | h
        · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
        · exact absurd h hC
      apply hb0
      rw [hb_eq, hl]; simp
    exact ih m' (by omega) _ hbs0 hbsdeg hfbs

end Pencil


section SpringerPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- A polynomial of odd degree has an irreducible factor of odd degree. -/
lemma exists_odd_irreducible_factor : ∀ (d : ℕ) (q : F[X]), q.natDegree = d → Odd d →
    ∃ G : F[X], Irreducible G ∧ G ∣ q ∧ Odd G.natDegree := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro q hqd hodd
  by_cases hirr : Irreducible q
  · exact ⟨q, hirr, dvd_rfl, hqd ▸ hodd⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hqd
    subst hqd
    simp at hodd
  rw [irreducible_iff] at hirr
  push Not at hirr
  obtain ⟨a, b, hab, ha, hb⟩ := hirr (by
    intro hu
    have := natDegree_eq_zero_of_isUnit hu
    rw [this] at hqd; subst hqd; simp at hodd)
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hq0 hab
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; exact hq0 hab
  have hapos : 0 < a.natDegree := by
    rw [natDegree_pos_iff_degree_pos]; exact degree_pos_of_ne_zero_of_nonunit ha0 ha
  have hbpos : 0 < b.natDegree := by
    rw [natDegree_pos_iff_degree_pos]; exact degree_pos_of_ne_zero_of_nonunit hb0 hb
  have hsum : a.natDegree + b.natDegree = d := by
    rw [← hqd, hab, natDegree_mul ha0 hb0]
  have hodd' := hodd
  rw [← hsum, Nat.odd_add] at hodd'
  by_cases hao : Odd a.natDegree
  · obtain ⟨G, hG, hGa, hGo⟩ := ih a.natDegree (by omega) a rfl hao
    exact ⟨G, hG, hGa.trans ⟨b, hab⟩, hGo⟩
  · have hbo : Odd b.natDegree := Nat.not_even_iff_odd.mp fun h => hao (hodd'.mpr h)
    obtain ⟨G, hG, hGb, hGo⟩ := ih b.natDegree (by omega) b rfl hbo
    exact ⟨G, hG, hGb.trans ⟨a, by rw [hab, mul_comm]⟩, hGo⟩

lemma mbil_congr_dvd {R : Type*} [CommRing R] (p : R) (N : Matrix (Fin n) (Fin n) R)
    (u u' v v' : Fin n → R) (hu : ∀ i, p ∣ u i - u' i) (hv : ∀ i, p ∣ v i - v' i) :
    p ∣ mbil N u v - mbil N u' v' := by
  rw [← Ideal.Quotient.eq_zero_iff_dvd, map_sub, sub_eq_zero]
  have hu' : ∀ i, Ideal.Quotient.mk (Ideal.span {p}) (u i) = Ideal.Quotient.mk (Ideal.span {p}) (u' i) :=
    fun i => by rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_dvd]; exact hu i
  have hv' : ∀ i, Ideal.Quotient.mk (Ideal.span {p}) (v i) = Ideal.Quotient.mk (Ideal.span {p}) (v' i) :=
    fun i => by rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_dvd]; exact hv i
  rw [map_mbil, map_mbil]
  simp only [hu', hv']

lemma polyBil_mul_self (M : Matrix (Fin n) (Fin n) F) (c : F[X]) (u : Fin n → F[X]) :
    polyBil M (fun i => c * u i) (fun i => c * u i) = c ^ 2 * polyBil M u u := by
  simp only [polyBil, mbil, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Springer's descent on polynomial vectors: if the form $x^{T} M x$ is anisotropic over $F$, there is no
irreducible polynomial $p$ of odd degree and vector $A$ of polynomials, not all divisible by $p$, with
$p \mid A^{T} M A$. -/
lemma springer_poly (M : Matrix (Fin n) (Fin n) F) (hani : ∀ a : Fin n → F, a ≠ 0 → mbil M a a ≠ 0) :
    ∀ (m : ℕ) (p : F[X]), Irreducible p → p.natDegree = m → Odd m →
      ∀ A : Fin n → F[X], p ∣ polyBil M A A → ¬ (∀ i, p ∣ A i) → False := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p hp hpm hodd
  have hp0 : p ≠ 0 := hp.ne_zero
  have hm0 : m ≠ 0 := by rintro rfl; simp at hodd
  have inner : ∀ k, ∀ A : Fin n → F[X], (∀ i, (A i).natDegree ≤ k) → p ∣ polyBil M A A →
      ¬ (∀ i, p ∣ A i) → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
    intro A hA hdvd hnd
    by_cases hk : m ≤ k
    · -- reduce modulo p
      have hmod : ∀ i, p ∣ A i - A i % p := fun i => by
        rw [EuclideanDomain.mod_eq_sub_mul_div, sub_sub_cancel]; exact dvd_mul_right _ _
      refine ihk (m - 1) (by omega) (fun i => A i % p) (fun i => ?_) ?_ ?_
      · have := natDegree_mod_lt (A i) (q := p) (by omega)
        omega
      · have h1 := mbil_congr_dvd p ((0 : Matrix (Fin n) (Fin n) F).map C + 0 + M.map C) A (fun i => A i % p)
          A (fun i => A i % p) hmod hmod
        have h2 : p ∣ polyBil M A A - polyBil M (fun i => A i % p) (fun i => A i % p) := by
          simpa [polyBil] using h1
        have := dvd_sub hdvd h2
        simpa using this
      · intro h
        apply hnd
        intro i
        have := dvd_add (hmod i) (h i)
        simpa using this
    · by_cases ha : (fun i => (A i).coeff k) = 0
      · -- the degree drops
        by_cases hk0 : k = 0
        · apply hnd
          intro i
          subst hk0
          have : A i = C ((A i).coeff 0) := eq_C_of_natDegree_le_zero (hA i)
          rw [this, show (A i).coeff 0 = 0 from congrFun ha i]
          simp
        · refine ihk (k - 1) (by omega) A (fun i => ?_) hdvd hnd
          rw [natDegree_le_iff_coeff_eq_zero]
          intro N hN
          by_cases hNk : N = k
          · subst hNk; exact congrFun ha i
          · exact coeff_eq_zero_of_natDegree_lt (by have := hA i; omega)
      · -- the main case: the leading coefficient vector is nonzero
        obtain ⟨hEdeg, hEc⟩ := polyBil_top M A A k k hA hA
        have hlead := hani _ ha
        have hE0 : polyBil M A A ≠ 0 := fun h => hlead (by rw [h, coeff_zero] at hEc; exact hEc.symm)
        have hEnat : (polyBil M A A).natDegree = k + k :=
          le_antisymm hEdeg (le_natDegree_of_ne_zero (by rw [hEc]; exact hlead))
        obtain ⟨q, hq⟩ := hdvd
        have hq0 : q ≠ 0 := by rintro rfl; apply hE0; rw [hq, mul_zero]
        have hdq : p.natDegree + q.natDegree = k + k := by
          rw [← hEnat, hq, natDegree_mul hp0 hq0]
        have hqodd : Odd q.natDegree := by
          rw [hpm] at hdq
          rw [Nat.odd_iff] at hodd ⊢
          omega
        obtain ⟨G, hG, hGq, hGodd⟩ := exists_odd_irreducible_factor _ q rfl hqodd
        have hG0 : G ≠ 0 := hG.ne_zero
        have hGdeg : G.natDegree < m := by
          have := natDegree_le_of_dvd hGq hq0
          omega
        have hGE : G ∣ polyBil M A A := hq ▸ (hGq.trans (dvd_mul_left _ _))
        by_cases hGA : ∀ i, G ∣ A i
        · choose A' hA' using hGA
          have hpG : ¬ p ∣ G := fun h => by
            have := natDegree_le_of_dvd h hG0
            omega
          have hcop : IsCoprime p (G ^ 2) :=
            ((Irreducible.coprime_iff_not_dvd hp).2 hpG).pow_right
          have hE' : polyBil M A A = G ^ 2 * polyBil M A' A' := by
            have : A = fun i => G * A' i := funext hA'
            rw [this, polyBil_mul_self]
          have hpE' : p ∣ polyBil M A' A' := by
            refine hcop.dvd_of_dvd_mul_left ⟨q, ?_⟩
            linear_combination hq - hE'
          have hnd' : ¬ ∀ i, p ∣ A' i := fun h =>
            hnd fun i => by rw [hA' i]; exact dvd_mul_of_dvd_right (h i) _
          obtain ⟨j, hj⟩ := not_forall.mp hnd'
          have hj0 : A' j ≠ 0 := fun h => hj (by rw [h]; exact dvd_zero _)
          have hGpos : 1 ≤ G.natDegree := by rw [Nat.odd_iff] at hGodd; omega
          have hAj := hA j
          rw [hA' j, natDegree_mul hG0 hj0] at hAj
          refine ihk (k - 1) (by omega) A' (fun i => ?_) hpE' hnd'
          by_cases hi : A' i = 0
          · rw [hi]; simp
          · have := hA i
            rw [hA' i, natDegree_mul hG0 hi] at this
            omega
        · exact ih G.natDegree hGdeg G hG rfl hGodd A hGE hGA
  intro A hdvd hnd
  exact inner (Finset.univ.sup fun i => (A i).natDegree) A
    (fun i => Finset.le_sup (f := fun i => (A i).natDegree) (Finset.mem_univ i)) hdvd hnd

end SpringerPoly

section PencilField

variable {F : Type*} [Field F] {n : ℕ}

lemma mbil_matrix_add {R : Type*} [CommRing R] (M N : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) :
    mbil (M + N) u v = mbil M u v + mbil N u v := by
  simp only [mbil, Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

lemma mbil_matrix_smul {R : Type*} [CommRing R] (c : R) (M : Matrix (Fin n) (Fin n) R)
    (u v : Fin n → R) : mbil (c • M) u v = c * mbil M u v := by
  simp only [mbil, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Evaluation of the pencil $G + tH$ on a vector of polynomials. -/
lemma pencil_poly_eval (G H : Matrix (Fin n) (Fin n) F) (y : Fin n → F[X]) :
    mbil (G.map (algebraMap F (RatFunc F)) +
        (RatFunc.X : RatFunc F) • H.map (algebraMap F (RatFunc F)))
      (fun i => algebraMap F[X] (RatFunc F) (y i)) (fun i => algebraMap F[X] (RatFunc F) (y i)) =
      algebraMap F[X] (RatFunc F) (polyBil G y y + X * polyBil H y y) := by
  have key : ∀ M : Matrix (Fin n) (Fin n) F, mbil (M.map (algebraMap F (RatFunc F)))
      (fun i => algebraMap F[X] (RatFunc F) (y i)) (fun i => algebraMap F[X] (RatFunc F) (y i)) =
      algebraMap F[X] (RatFunc F) (polyBil M y y) := fun M => by
    rw [polyBil, map_mbil, Matrix.map_map]
    congr 2
  rw [mbil_matrix_add, mbil_matrix_smul, key, key, map_add, map_mul, RatFunc.algebraMap_X]

/-- **Aubry-Brumer, matrix form.** If symmetric $G, H$ have no common nontrivial zero over $F$, then the
pencil $G + tH$ has no nontrivial zero over $F(t)$. -/
lemma pencil_aniso {G H : Matrix (Fin n) (Fin n) F} (hG : G.IsSymm) (hH : H.IsSymm)
    (hno : ∀ a : Fin n → F, a ≠ 0 → mbil G a a = 0 → mbil H a a = 0 → False)
    (x : Fin n → RatFunc F) (hx0 : x ≠ 0)
    (hfx : mbil (G.map (algebraMap F (RatFunc F)) +
      (RatFunc.X : RatFunc F) • H.map (algebraMap F (RatFunc F))) x x = 0) : False := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors F[X]) Finset.univ x
  have hb' : ∀ i, ∃ a, algebraMap F[X] (RatFunc F) a = (b : F[X]) • x i :=
    fun i => hb i (Finset.mem_univ i)
  choose y hy using hb'
  have hbne : algebraMap F[X] (RatFunc F) (b : F[X]) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero b (RatFunc.algebraMap_injective F (by simp at h0))
  have hyx : (fun i => algebraMap F[X] (RatFunc F) (y i)) =
      algebraMap F[X] (RatFunc F) (b : F[X]) • x := by
    funext i; rw [hy i, Algebra.smul_def]; rfl
  have hy0 : y ≠ 0 := by
    intro h0
    apply hx0
    have : algebraMap F[X] (RatFunc F) (b : F[X]) • x = 0 := by
      rw [← hyx]; funext i; simp [h0]
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h hbne
    · exact h
  have hpoly : algebraMap F[X] (RatFunc F) (polyBil G y y + X * polyBil H y y) = 0 := by
    rw [← pencil_poly_eval, hyx, mbil_smul_left, mbil_smul_right, hfx]
    simp
  have hpoly' : polyBil G y y + X * polyBil H y y = 0 :=
    (RatFunc.algebraMap_injective F) (by rw [hpoly, map_zero])
  exact pencil_core hG hH hno (Finset.univ.sup fun i => (y i).natDegree) y hy0
    (fun i => Finset.le_sup (f := fun i => (y i).natDegree) (Finset.mem_univ i)) hpoly'

lemma map_polyBil {B C' : Type*} [Field B] [Field C'] (ι : B →+* C') (M : Matrix (Fin n) (Fin n) B)
    (u v : Fin n → B[X]) :
    (polyBil M u v).map ι = polyBil (M.map ι) (fun i => (u i).map ι) (fun i => (v i).map ι) := by
  have := map_mbil (Polynomial.mapRingHom ι) (M.map C) u v
  simp only [coe_mapRingHom] at this
  rw [polyBil, polyBil]
  convert this using 2
  ext i j
  simp

lemma polyBil_pencil {B : Type*} [Field B] (G H : Matrix (Fin n) (Fin n) B) (t : B)
    (u v : Fin n → B[X]) :
    polyBil (G + t • H) u v = polyBil G u v + C t * polyBil H u v := by
  have : (G + t • H).map C = G.map C + C t • H.map C := by
    ext i j; simp
  rw [polyBil, polyBil, polyBil, this, mbil_matrix_add, mbil_matrix_smul]

/-- The simple case of the Aubry-Brumer-Springer descent for two forms: a common nontrivial zero over
$B[s]/(p)$, $p$ irreducible of odd degree, gives a common nontrivial zero over $B$. -/
lemma pencil_simple (B : Type u_1) [Field B] (p : B[X]) [Fact (Irreducible p)] (hodd : Odd p.natDegree)
    (M : Fin 2 → Matrix (Fin n) (Fin n) B) (hM : ∀ j, (M j).IsSymm)
    (h : ∃ y' : Fin n → AdjoinRoot p, y' ≠ 0 ∧
      ∀ j, mbil ((M j).map (algebraMap B (AdjoinRoot p))) y' y' = 0) :
    ∃ y : Fin n → B, y ≠ 0 ∧ ∀ j, mbil (M j) y y = 0 := by
  by_contra hcon
  push Not at hcon
  have hno : ∀ a : Fin n → B, a ≠ 0 → mbil (M 0) a a = 0 → mbil (M 1) a a = 0 → False := by
    intro a ha h0 h1
    obtain ⟨j, hj⟩ := hcon a ha
    fin_cases j
    · exact hj h0
    · exact hj h1
  obtain ⟨y', hy0, hy⟩ := h
  have hirr : Irreducible p := Fact.out
  choose A hA using fun i => AdjoinRoot.mk_surjective (g := p) (y' i)
  have hdvd : ∀ j, p ∣ polyBil (M j) A A := fun j => by
    rw [← AdjoinRoot.mk_eq_zero, polyBil, map_mbil]
    have : ((M j).map C).map (AdjoinRoot.mk p) = (M j).map (algebraMap B (AdjoinRoot p)) := by
      rw [Matrix.map_map]
      congr 1
    rw [this]
    simpa [hA] using hy j
  have hnd : ¬ ∀ i, p ∣ A i := by
    intro h
    apply hy0
    funext i
    rw [← hA i, (AdjoinRoot.mk_eq_zero).mpr (h i)]
    rfl
  obtain ⟨j, hj⟩ := not_forall.mp hnd
  have hq0 : p.map (algebraMap B (RatFunc B)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap B (RatFunc B)).injective).mpr hirr.ne_zero
  have hqodd : Odd (p.map (algebraMap B (RatFunc B))).natDegree := by
    rw [natDegree_map]; exact hodd
  obtain ⟨p₁, hp₁, hp₁q, hp₁odd⟩ := exists_odd_irreducible_factor _ _ rfl hqodd
  have hdvd₁ : p₁ ∣ polyBil ((M 0).map (algebraMap B (RatFunc B)) +
      (RatFunc.X : RatFunc B) • (M 1).map (algebraMap B (RatFunc B)))
      (fun i => (A i).map (algebraMap B (RatFunc B)))
      (fun i => (A i).map (algebraMap B (RatFunc B))) := by
    rw [polyBil_pencil, ← map_polyBil, ← map_polyBil]
    exact dvd_add (hp₁q.trans (Polynomial.map_dvd _ (hdvd 0)))
      (dvd_mul_of_dvd_right (hp₁q.trans (Polynomial.map_dvd _ (hdvd 1))) _)
  have hnd₁ : ¬ ∀ i, p₁ ∣ (A i).map (algebraMap B (RatFunc B)) := by
    intro hall
    obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hirr).2 hj
    have := congrArg (Polynomial.map (algebraMap B (RatFunc B))) huv
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one] at this
    refine hp₁.not_isUnit (isUnit_of_dvd_one ?_)
    rw [← this]
    exact dvd_add (dvd_mul_of_dvd_right hp₁q _) (dvd_mul_of_dvd_right (hall j) _)
  exact springer_poly _ (fun a ha h0 => pencil_aniso (hM 0) (hM 1) hno a ha h0) p₁.natDegree p₁ hp₁
    rfl hp₁odd _ hdvd₁ hnd₁

end PencilField

section Tower

universe u v

/-- The tower induction behind Springer's theorem: a family of symmetric matrices has a common nontrivial
isotropic vector over a finite extension $E$ of odd degree as soon as the simple case (extensions
$B[s]/(p)$ with $p$ irreducible of odd degree) is known. -/
theorem tower_core {n r : ℕ}
    (hsimple : ∀ (B : Type u) [Field B] (p : B[X]) [Fact (Irreducible p)], Odd p.natDegree →
      ∀ M : Fin r → Matrix (Fin n) (Fin n) B, (∀ j, (M j).IsSymm) →
      (∃ y' : Fin n → AdjoinRoot p, y' ≠ 0 ∧
        ∀ j, mbil ((M j).map (algebraMap B (AdjoinRoot p))) y' y' = 0) →
      ∃ y : Fin n → B, y ≠ 0 ∧ ∀ j, mbil (M j) y y = 0) :
    ∀ (d : ℕ) (B : Type u) (E : Type v) [Field B] [Field E] [Algebra B E] [FiniteDimensional B E],
      finrank B E = d → Odd d → ∀ M : Fin r → Matrix (Fin n) (Fin n) B, (∀ j, (M j).IsSymm) →
      (∃ x : Fin n → E, x ≠ 0 ∧ ∀ j, mbil ((M j).map (algebraMap B E)) x x = 0) →
      ∃ y : Fin n → B, y ≠ 0 ∧ ∀ j, mbil (M j) y y = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro B E _ _ _ _ hd hodd M hM ⟨x, hx0, hx⟩
  by_cases hrange : ∀ θ : E, ∃ b : B, algebraMap B E b = θ
  · choose y hy using hrange
    refine ⟨fun i => y (x i), ?_, fun j => ?_⟩
    · intro h0
      apply hx0
      funext i
      rw [← hy (x i)]
      simp [congrFun h0 i]
    · apply (algebraMap B E).injective
      rw [map_mbil, map_zero, ← hx j]
      simp only [hy]
  · push Not at hrange
    obtain ⟨θ, hθ⟩ := hrange
    have hint : IsIntegral B θ := Algebra.IsIntegral.isIntegral θ
    set p := minpoly B θ with hp_def
    have hirr : Irreducible p := minpoly.irreducible hint
    have hp0 : p ≠ 0 := hirr.ne_zero
    have : Fact (Irreducible p) := ⟨hirr⟩
    have hdvd : p.natDegree ∣ d := hd ▸ minpoly.degree_dvd hint
    have hne1 : p.natDegree ≠ 1 := by
      intro h1
      obtain ⟨b, hb⟩ := (minpoly.natDegree_eq_one_iff).mp h1
      exact hθ b hb
    have hpos : 0 < p.natDegree := hirr.natDegree_pos
    let ψ : AdjoinRoot p →ₐ[B] E := AdjoinRoot.liftAlgHom p (Algebra.ofId B E) θ (by
      simpa [Polynomial.aeval_def] using minpoly.aeval B θ)
    let _ : Algebra (AdjoinRoot p) E := ψ.toRingHom.toAlgebra
    have : IsScalarTower B (AdjoinRoot p) E :=
      IsScalarTower.of_algebraMap_eq fun b => (ψ.commutes b).symm
    let pb := AdjoinRoot.powerBasis hp0
    have : FiniteDimensional B (AdjoinRoot p) := pb.finite
    have : FiniteDimensional (AdjoinRoot p) E := FiniteDimensional.right B (AdjoinRoot p) E
    have hfin : finrank B (AdjoinRoot p) = p.natDegree := by
      rw [pb.finrank]; exact AdjoinRoot.powerBasis_dim hp0
    have htower := Module.finrank_mul_finrank B (AdjoinRoot p) E
    rw [hfin, hd] at htower
    have hodd' : Odd (p.natDegree * finrank (AdjoinRoot p) E) := htower ▸ hodd
    rw [Nat.odd_mul] at hodd'
    have hd'pos : 0 < finrank (AdjoinRoot p) E := by
      rcases Nat.eq_zero_or_pos (finrank (AdjoinRoot p) E) with h | h
      · rw [h] at hodd'; simp at hodd'
      · exact h
    have hlt : finrank (AdjoinRoot p) E < d := by
      rw [← htower]
      have : 2 ≤ p.natDegree := by omega
      nlinarith
    have hmap : ∀ j, ((M j).map (algebraMap B (AdjoinRoot p))).map (algebraMap (AdjoinRoot p) E) =
        (M j).map (algebraMap B E) := fun j => by
      rw [Matrix.map_map]
      congr 1
      funext a
      exact (IsScalarTower.algebraMap_apply B (AdjoinRoot p) E a).symm
    obtain ⟨y', hy0, hy⟩ := ih _ hlt (AdjoinRoot p) E rfl hodd'.2
      (fun j => (M j).map (algebraMap B (AdjoinRoot p))) (fun j => (hM j).map _)
      ⟨x, hx0, fun j => by rw [hmap]; exact hx j⟩
    exact hsimple B p hodd'.1 M hM ⟨y', hy0, hy⟩

/-- **Springer's theorem for matrices.** If $x^{T} M x$ ($M$ symmetric) has a nontrivial zero over a finite
extension $E$ of $B$ of odd degree, it has one over $B$. -/
theorem springer_core {n : ℕ} (B : Type u) (E : Type v) [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] (hodd : Odd (finrank B E)) (M : Matrix (Fin n) (Fin n) B)
    (hM : M.IsSymm) (h : ∃ x : Fin n → E, x ≠ 0 ∧ mbil (M.map (algebraMap B E)) x x = 0) :
    ∃ y : Fin n → B, y ≠ 0 ∧ mbil M y y = 0 := by
  have key := tower_core (n := n) (r := 1) (fun B _ p _ hodd M _ ⟨y', hy0, hy⟩ => by
    by_contra hcon
    push Not at hcon
    have hani : ∀ a : Fin n → B, a ≠ 0 → mbil (M 0) a a ≠ 0 := fun a ha h0 => by
      obtain ⟨j, hj⟩ := hcon a ha
      rw [Subsingleton.elim j 0] at hj
      exact hj h0
    choose A hA using fun i => AdjoinRoot.mk_surjective (g := p) (y' i)
    refine springer_poly (M 0) hani p.natDegree p (Fact.out) rfl hodd A ?_ ?_
    · rw [← AdjoinRoot.mk_eq_zero, polyBil, map_mbil]
      have : ((M 0).map C).map (AdjoinRoot.mk p) = (M 0).map (algebraMap B (AdjoinRoot p)) := by
        rw [Matrix.map_map]
        congr 1
      rw [this]
      simpa [hA] using hy 0
    · intro h
      apply hy0
      funext i
      rw [← hA i, (AdjoinRoot.mk_eq_zero).mpr (h i)]
      rfl) (finrank B E) B E rfl hodd (fun _ => M) (fun _ => hM)
    (by obtain ⟨x, hx0, hx⟩ := h; exact ⟨x, hx0, fun _ => hx⟩)
  obtain ⟨y, hy0, hy⟩ := key
  exact ⟨y, hy0, hy 0⟩

end Tower

section Forms

variable {F : Type*} [Field F] [Invertible (2 : F)] {n : ℕ}

/-- The extension of scalars of a quadratic form $Q$ on $F^{n}$ to a commutative $F$-algebra $K$: the
quadratic form on $K^{n}$ with the same Gram matrix. -/
def extendForm (Q : QuadraticForm F (Fin n → F)) (K : Type*) [CommRing K] [Algebra F K] :
    QuadraticForm K (Fin n → K) :=
  (Q.toMatrix'.map (algebraMap F K)).toQuadraticForm'

lemma extendForm_apply (Q : QuadraticForm F (Fin n → F)) (K : Type*) [CommRing K] [Algebra F K]
    (x : Fin n → K) : extendForm Q K x = mbil (Q.toMatrix'.map (algebraMap F K)) x x := by
  simp only [extendForm, Matrix.toQuadraticForm', mbil, Matrix.toLinearMap₂'_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma form_eq_mbil (Q : QuadraticForm F (Fin n → F)) (x : Fin n → F) :
    Q x = mbil Q.toMatrix' x x := by
  have h : Matrix.toLinearMap₂' F (LinearMap.toMatrix₂' F (QuadraticMap.associated Q)) =
      QuadraticMap.associated Q := by simp
  have h2 := QuadraticMap.associated_eq_self_apply F Q x
  rw [← h2]
  conv_lhs => rw [← h]
  simp only [Matrix.toLinearMap₂'_apply, mbil, QuadraticForm.toMatrix']
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma extendForm_algebraMap (Q : QuadraticForm F (Fin n → F)) (K : Type*) [CommRing K] [Algebra F K]
    (x : Fin n → F) : extendForm Q K (fun i => algebraMap F K (x i)) = algebraMap F K (Q x) := by
  rw [extendForm_apply, form_eq_mbil, map_mbil]

/-- The form $f = g + t\,h$ over the rational function field $F(t)$, where $t$ = `RatFunc.X`, for forms
$g, h$ over $F$ in $n$ variables. -/
def pencilForm (g h : QuadraticForm F (Fin n → F)) :
    QuadraticForm (RatFunc F) (Fin n → RatFunc F) :=
  extendForm g (RatFunc F) + (RatFunc.X : RatFunc F) • extendForm h (RatFunc F)

lemma pencilForm_apply (g h : QuadraticForm F (Fin n → F)) (x : Fin n → RatFunc F) :
    pencilForm g h x = extendForm g (RatFunc F) x + RatFunc.X * extendForm h (RatFunc F) x := by
  simp [pencilForm]

/-- **Cassels, Ch. 2, Ex. 19 (p. 33).** Let $t$ be transcendental over $k$ (here: the variable of the rational
function field $k(t)$) and $f(x) = g(x) + t\,h(x)$ with $g, h$ quadratic forms over $k$ in $n$ variables. Then
$f$ is isotropic over $k(t)$ if and only if there is $a \ne 0$ in $k^{n}$ with $g(a) = h(a) = 0$. The proof follows
the hint (Aubry's descent): a zero with polynomial entries of least degree $m$ is reflected in the vector of
leading coefficients to lower the degree. *Any characteristic* is fine for the argument; `Invertible (2 : F)` is
only used to write the forms by Gram matrices. -/
@[kb "cassels1978" "Ch. 2, Ex. 19, p. 33"]
theorem ex19 (g h : QuadraticForm F (Fin n → F)) :
    ¬ (pencilForm g h).Anisotropic ↔ ∃ a : Fin n → F, a ≠ 0 ∧ g a = 0 ∧ h a = 0 := by
  constructor
  · intro hni
    by_contra hno
    push Not at hno
    apply hni
    intro x hfx
    by_contra hx0
    refine pencil_aniso (QuadraticForm.isSymm_toMatrix' g) (QuadraticForm.isSymm_toMatrix' h)
      (fun a ha h1 h2 => ?_) x hx0 ?_
    · rw [← form_eq_mbil] at h1 h2
      exact hno a ha h1 h2
    · rw [mbil_matrix_add, mbil_matrix_smul, ← extendForm_apply, ← extendForm_apply,
        ← pencilForm_apply]
      exact hfx
  · rintro ⟨a, ha0, hga, hha⟩ hani
    have := hani (fun i => algebraMap F (RatFunc F) (a i)) (by
      rw [pencilForm_apply, extendForm_algebraMap, extendForm_algebraMap, hga, hha]; simp)
    apply ha0
    funext i
    exact (algebraMap F (RatFunc F)).injective (by simpa using congrFun this i)

/-- **Cassels, Ch. 2, Ex. 15 (p. 32) (Springer's theorem).** Let $f$ be a quadratic form over a field $k$ and $K$ a
finite extension of $k$ of odd degree. If $f$ is isotropic over $K$ then $f$ is isotropic over $k$. The proof follows
the hint (minimal counterexample, reduction of $f(A(\theta))$ modulo the minimal polynomial and passage to an
irreducible factor of odd degree), organised as an induction along a tower of simple extensions so that no primitive
element theorem is needed. *Update:* regularity of $f$ is not needed (a degenerate form is isotropic over $k$ by its
radical), and no hypothesis on the characteristic is used beyond `Invertible (2 : F)`, which is only used to write
the form by a Gram matrix. -/
@[kb "cassels1978" "Ch. 2, Ex. 15, p. 32"]
theorem ex15 {K : Type*} [Field K] [Algebra F K] [Module.Finite F K] (hodd : Odd (finrank F K))
    (Q : QuadraticForm F (Fin n → F)) (hK : ¬ (extendForm Q K).Anisotropic) : ¬ Q.Anisotropic := by
  unfold QuadraticMap.Anisotropic at hK ⊢
  push Not at hK ⊢
  obtain ⟨x, hx, hx0⟩ := hK
  obtain ⟨y, hy0, hy⟩ := springer_core F K hodd Q.toMatrix' (QuadraticForm.isSymm_toMatrix' Q)
    ⟨x, hx0, by rw [← extendForm_apply]; exact hx⟩
  exact ⟨y, by rw [form_eq_mbil]; exact hy, hy0⟩

/-- **Cassels, Ch. 2, Ex. 20 (p. 33).** Let $g, h$ be quadratic forms over $k$ in $n$ variables and $K$ a finite
extension of $k$ of odd degree. If there is $A \ne 0$ in $K^{n}$ with $g(A) = h(A) = 0$, then there is $a \ne 0$ in
$k^{n}$ with $g(a) = h(a) = 0$. The proof runs the argument of the hint (Ex. 15 and Ex. 19) inside a single descent
along a tower of simple extensions: at each simple step $k[s]/(p)$, $p$ of odd degree, an irreducible factor of odd
degree of $p$ over $k(t)$ is used instead of the (equivalent) statement that $[K(t) : k(t)] = [K : k]$, which is not
needed. -/
@[kb "cassels1978" "Ch. 2, Ex. 20, p. 33"]
theorem ex20 {K : Type*} [Field K] [Algebra F K] [Module.Finite F K] (hodd : Odd (finrank F K))
    (g h : QuadraticForm F (Fin n → F))
    (hA : ∃ A : Fin n → K, A ≠ 0 ∧ extendForm g K A = 0 ∧ extendForm h K A = 0) :
    ∃ a : Fin n → F, a ≠ 0 ∧ g a = 0 ∧ h a = 0 := by
  obtain ⟨A, hA0, hAg, hAh⟩ := hA
  have key := tower_core (n := n) (r := 2) (fun B _ p _ hodd M hM hz => pencil_simple B p hodd M hM hz)
    (finrank F K) F K rfl hodd ![g.toMatrix', h.toMatrix']
    (fun j => by fin_cases j <;> exact QuadraticForm.isSymm_toMatrix' _)
    ⟨A, hA0, fun j => by
      fin_cases j
      · exact (extendForm_apply g K A).symm.trans hAg
      · exact (extendForm_apply h K A).symm.trans hAh⟩
  obtain ⟨a, ha0, ha⟩ := key
  exact ⟨a, ha0, by rw [form_eq_mbil]; exact ha 0, by rw [form_eq_mbil]; exact ha 1⟩

end Forms

end QuadFormsKB.Cassels.Ch2Ex
