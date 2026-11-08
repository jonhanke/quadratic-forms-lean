/-
# Watson (1963), §4: the local probes at an odd prime

Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963), Lemma 2, local part
((4.12), p. 555), for odd primes $p$. By `exists_diag_of_minimal_odd` a Watson-minimal positive definite $f$ is
$\mathbb Z_p$-equivalent to $\langle u_0, \dots, u_{r-1}, p u_r, \dots, p u_{n-1}\rangle$ with $r = r_p(f)$. A probe
$\varphi$ in $v$ variables with $p \nmid \det H_\varphi$ is $\cong \langle w_0, \dots, w_{v-1}\rangle$ with units $w_i$, and
$v + 1$ unit coordinates represent it (`RepD.of_units`: add a last coordinate to match the determinant and use the
classification of unimodular forms). The two remaining cases $p \mid \det H_{A_v}$ ($A_5$ at $3$, $A_6$ at $7$) have
$A_v \cong \langle w_0, \dots, w_{v-2}, p w'\rangle$ over $\mathbb Z_p$ and are treated separately.

*Notation.* `RepD a a'` says that the diagonal form $\sum a_i x_i^2$ represents $\sum a'_j y_j^2$ over a commutative
ring: $\sum_i a_i (H\vec y)_i^2 = \sum_j a'_j y_j^2$ for an $n \times v$ matrix $H$.
-/
import QuadFormsKB.Literature.Watson1963.LocalOdd
import QuadFormsKB.Literature.Watson1963.ProbeFacts
import QuadFormsKB.Siegel.UnimodularPadic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

/-! ### Representation between diagonal forms -/

section RepD

variable {K : Type*} [CommRing K]

/-- **Representation between diagonal forms:** $\langle a_0, \dots, a_{k-1}\rangle$ represents
$\langle a'_0, \dots, a'_{k'-1}\rangle$ over $K$ if $\sum_i a_i (H\vec y)_i^2 = \sum_j a'_j y_j^2$ for all
$\vec y \in K^{k'}$, for a $k \times k'$ matrix $H$ over $K$. -/
def RepD {k k' : ℕ} (a : Fin k → K) (a' : Fin k' → K) : Prop :=
  ∃ H : Matrix (Fin k) (Fin k') K, ∀ y : Fin k' → K, ∑ i, a i * (H *ᵥ y) i ^ 2 = ∑ j, a' j * y j ^ 2

theorem RepD.refl {k : ℕ} (a : Fin k → K) : RepD a a := ⟨1, fun y => by simp⟩

theorem RepD.trans {k k' k'' : ℕ} {a : Fin k → K} {a' : Fin k' → K} {a'' : Fin k'' → K}
    (h₁ : RepD a a') (h₂ : RepD a' a'') : RepD a a'' := by
  obtain ⟨H₁, hH₁⟩ := h₁
  obtain ⟨H₂, hH₂⟩ := h₂
  exact ⟨H₁ * H₂, fun y => by rw [← mulVec_mulVec] at *; rw [hH₁, hH₂]⟩

/-- Restriction to injectively chosen coordinates: $\langle a_i\rangle$ represents $\langle a_{e(j)}\rangle$. -/
theorem RepD.of_injective {k k' : ℕ} (a : Fin k → K) (e : Fin k' → Fin k) (he : Function.Injective e) :
    RepD a (fun j => a (e j)) := by
  classical
  refine ⟨Matrix.of fun i j => if i = e j then 1 else 0, fun y => ?_⟩
  set z : Fin k → K := (Matrix.of fun i j => if i = e j then (1 : K) else 0) *ᵥ y with hz
  have hz1 : ∀ j, z (e j) = y j := by
    intro j
    simp [hz, mulVec, dotProduct, he.eq_iff]
  have hz0 : ∀ i, i ∉ Finset.univ.image e → z i = 0 := by
    intro i hi
    have : ∀ j, i ≠ e j := fun j h => hi (Finset.mem_image.2 ⟨j, Finset.mem_univ _, h.symm⟩)
    simp [hz, mulVec, dotProduct, this]
  have h1 : ∑ i, a i * z i ^ 2 = ∑ i ∈ Finset.univ.image e, a i * z i ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    rw [hz0 i hi]; ring
  rw [h1, Finset.sum_image (fun i _ j _ h => he h)]
  exact Finset.sum_congr rfl fun j _ => by rw [hz1]

/-- Scaling both diagonal forms by a constant. -/
theorem RepD.smul {k k' : ℕ} {a : Fin k → K} {a' : Fin k' → K} (h : RepD a a') (c : K) :
    RepD (fun i => c * a i) (fun j => c * a' j) := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H, fun y => ?_⟩
  simp only [mul_assoc, ← Finset.mul_sum, hH y]

/-- An isometry of diagonal forms is a representation. -/
theorem RepD.of_isometricGL {k : ℕ} {a a' : Fin k → K} (h : IsometricGL (QuadForm.diag a) (QuadForm.diag a')) :
    RepD a a' := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g.val, fun y => by have := hg y; rwa [eval_diag', eval_diag'] at this⟩

/-- **Orthogonal sums of representations:** if $a$ represents $a'$ and $b$ represents $b'$ then the concatenation of
$a, b$ represents the concatenation of $a', b'$. -/
theorem RepD.append {k k' m m' : ℕ} {a : Fin k → K} {a' : Fin k' → K} {b : Fin m → K} {b' : Fin m' → K}
    (h₁ : RepD a a') (h₂ : RepD b b') : RepD (Fin.append a b) (Fin.append a' b') := by
  obtain ⟨H₁, hH₁⟩ := h₁
  obtain ⟨H₂, hH₂⟩ := h₂
  let H : Matrix (Fin (k + m)) (Fin (k' + m')) K := Matrix.of fun i j =>
    Fin.addCases (motive := fun _ => K)
      (fun i₁ => Fin.addCases (motive := fun _ => K) (fun j₁ => H₁ i₁ j₁) (fun _ => 0) j)
      (fun i₂ => Fin.addCases (motive := fun _ => K) (fun _ => 0) (fun j₂ => H₂ i₂ j₂) j) i
  refine ⟨H, fun y => ?_⟩
  have hL : ∀ i₁, (H *ᵥ y) (Fin.castAdd m i₁) = (H₁ *ᵥ fun j => y (Fin.castAdd m' j)) i₁ := by
    intro i₁
    simp [H, mulVec, dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
  have hR : ∀ i₂, (H *ᵥ y) (Fin.natAdd k i₂) = (H₂ *ᵥ fun j => y (Fin.natAdd k' j)) i₂ := by
    intro i₂
    simp [H, mulVec, dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, hL, hR]
  rw [hH₁, hH₂]

/-- A function on `Fin (m + 1)` is the concatenation of its restriction to the first $m$ coordinates and its last
value. -/
theorem eq_append_snoc {m : ℕ} (t : Fin (m + 1) → K) :
    t = Fin.append (fun j : Fin m => t (Fin.castSucc j)) (fun _ : Fin 1 => t (Fin.last m)) := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · exact (Fin.append_left (fun j : Fin m => t (Fin.castSucc j)) (fun _ : Fin 1 => t (Fin.last m)) i).symm
  · exact (Fin.append_right (fun j : Fin m => t (Fin.castSucc j)) (fun _ : Fin 1 => t (Fin.last m))
      (0 : Fin 1)).symm

end RepD

/-! ### Unit coordinates over $\mathbb Z_p$ -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- In $\mathbb Z_p$, an element is a unit iff it is not divisible by $p$. -/
theorem isUnit_iff_not_dvd (x : ℤ_[p]) : IsUnit x ↔ ¬ (p : ℤ_[p]) ∣ x := by
  rw [PadicInt.isUnit_iff, ← PadicInt.norm_lt_one_iff_dvd, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (PadicInt.norm_le_one x) h⟩

theorem isUnit_two_padic (hp : p ≠ 2) : IsUnit (2 : ℤ_[p]) :=
  (isUnit_iff_not_dvd p _).2 (Siegel.Kneser.not_p_dvd_two hp)

theorem isUnit_prod_padic {m : ℕ} (a : Fin m → ℤ_[p]) (ha : ∀ i, IsUnit (a i)) : IsUnit (∏ i, a i) :=
  Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => ha i)

/-- The Hessian determinant of the base change to $\mathbb Z_p$ is the base change of the determinant. -/
theorem hessian_map_det_padic {n : ℕ} (Q : QuadForm ℤ n) :
    (Q.map (Int.castRingHom ℤ_[p])).hessian.det = ((Q.hessian.det : ℤ) : ℤ_[p]) := by
  have : (Q.map (Int.castRingHom ℤ_[p])).hessian = Q.hessian.map (Int.castRingHom ℤ_[p]) := by
    simp [QuadForm.hessian, QuadForm.map, Matrix.map_add, Matrix.transpose_map]
  rw [this]
  exact (RingHom.map_det (Int.castRingHom ℤ_[p]) Q.hessian).symm

theorem eval_map_padic {n : ℕ} (Q : QuadForm ℤ n) (x : Fin n → ℤ_[p]) :
    (Q.map (Int.castRingHom ℤ_[p])).eval x = Q.evalIn ℤ_[p] x := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- **$k+1$ unit coordinates represent $k$ unit coordinates** ($p$ odd): $\langle a_0, \dots, a_k\rangle$ with all
$a_i$ units represents $\langle b_0, \dots, b_{k-1}\rangle$ with all $b_i$ units. *Proof:* $\langle b, c\rangle$ with the
unit $c = \prod a / \prod b$ has the same Hessian determinant as $\langle a\rangle$, so the two are isometric by the
classification of unimodular forms (`isometricGL_of_unimodular`); restrict to the first $k$ coordinates. -/
theorem RepD.of_units (hp : p ≠ 2) {m : ℕ} (a : Fin (m + 1) → ℤ_[p]) (b : Fin m → ℤ_[p])
    (ha : ∀ i, IsUnit (a i)) (hb : ∀ i, IsUnit (b i)) : RepD a b := by
  have hPa := isUnit_prod_padic p a ha
  have hPb := isUnit_prod_padic p b hb
  set c : ℤ_[p] := (∏ i, a i) * ↑(hPb.unit⁻¹) with hc
  set a' : Fin (m + 1) → ℤ_[p] := Fin.snoc (α := fun _ => ℤ_[p]) b c with ha'
  have hprod : ∏ i, a' i = ∏ i, a i := by
    rw [Fin.prod_univ_castSucc]
    simp only [ha', Fin.snoc_castSucc, Fin.snoc_last]
    calc (∏ i, b i) * ((∏ i, a i) * ↑(hPb.unit⁻¹)) = (∏ i, a i) * ((∏ i, b i) * ↑(hPb.unit⁻¹)) := by ring
      _ = ∏ i, a i := by rw [hPb.mul_val_inv, mul_one]
  have hnd : ¬ (p : ℤ_[p]) ∣ (QuadForm.diag a').hessian.det := by
    rw [LocalDensity.DVR.det_hessian_diag, hprod]
    exact (isUnit_iff_not_dvd p _).1 (((isUnit_two_padic p hp).pow _).mul hPa)
  have hdet : (QuadForm.diag a).hessian.det = (QuadForm.diag a').hessian.det := by
    rw [LocalDensity.DVR.det_hessian_diag, LocalDensity.DVR.det_hessian_diag, hprod]
  have hiso := Siegel.Kneser.isometricGL_of_unimodular hp (QuadForm.diag a') (QuadForm.diag a) hnd hdet
  have h1 : RepD a a' := RepD.of_isometricGL hiso.symm
  have h2 := RepD.of_injective a' Fin.castSucc (Fin.castSucc_injective _)
  have e : (fun j : Fin m => a' (Fin.castSucc j)) = b := by funext j; simp [ha']
  rw [e] at h2
  exact h1.trans h2

/-- **More unit coordinates than needed:** $k$ unit coordinates represent $m < k$ unit coordinates. -/
theorem RepD.of_units_lt (hp : p ≠ 2) {k m : ℕ} (hmk : m < k) (a : Fin k → ℤ_[p]) (b : Fin m → ℤ_[p])
    (ha : ∀ i, IsUnit (a i)) (hb : ∀ i, IsUnit (b i)) : RepD a b := by
  have h1 := RepD.of_injective a (Fin.castLE (show m + 1 ≤ k from hmk)) (Fin.castLE_injective _)
  exact h1.trans (RepD.of_units p hp _ b (fun j => ha _) hb)

/-- **Chains:** if $f \cong \langle c\rangle$, $\langle c \rangle$ represents $\langle t\rangle$ and $\langle t\rangle \cong \varphi$
over $\mathbb Z_p$, then $f$ represents $\varphi$ over $\mathbb Z_p$. -/
theorem RepOver.of_chain {n v : ℕ} {f : QuadForm ℤ n} {φ : QuadForm ℤ v} {c : Fin n → ℤ_[p]} {t : Fin v → ℤ_[p]}
    (h1 : IsometricGL (f.map (Int.castRingHom ℤ_[p])) (QuadForm.diag c)) (h2 : RepD c t)
    (h3 : IsometricGL (QuadForm.diag t) (φ.map (Int.castRingHom ℤ_[p]))) : RepOver ℤ_[p] f φ := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨H2, hH2⟩ := h2
  obtain ⟨g3, hg3⟩ := h3
  refine ⟨g1.val * (H2 * g3.val), fun y => ?_⟩
  rw [← eval_map_padic p f, ← eval_map_padic p φ, ← mulVec_mulVec, ← mulVec_mulVec, hg1, eval_diag', hH2,
    ← eval_diag', hg3]

/-- **Unimodular probes** ($p$ odd): if $f$ is Watson-minimal positive definite, $p \nmid \det H_\varphi$ and
$v + 1 \le r_p(f)$, then $f$ represents $\varphi$ ($v$ variables) over $\mathbb Z_p$. *Proof:* $f \cong \langle u_0, \dots,
u_{r-1}, p u_r, \dots\rangle$; $\varphi \cong \langle w_0, \dots, w_{v-1}\rangle$ with units; the first $v+1$ unit
coordinates represent it (`RepD.of_units`). -/
theorem repOver_of_unimodular {n v : ℕ} {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f)
    (hp : p ≠ 2) (φ : QuadForm ℤ v) (hφ : ¬ (p : ℤ) ∣ φ.hessian.det) (hv : v + 1 ≤ rankModP p f) :
    RepOver ℤ_[p] f φ := by
  obtain ⟨u, hu, hiso⟩ := exists_diag_of_minimal_odd hf hmin p hp
  have hrn : rankModP p f ≤ n := rankModP_le p f
  set c : Fin n → ℤ_[p] := fun i => if (i : ℕ) < rankModP p f then u i else (p : ℤ_[p]) * u i with hc
  have hunimod : ¬ (p : ℤ_[p]) ∣ (φ.map (Int.castRingHom ℤ_[p])).hessian.det := by
    rw [hessian_map_det_padic]
    intro h
    apply hφ
    have := (toZMod_eq_zero_iff_dvd p _).2 h
    rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact this
  obtain ⟨w, hw, hE, -⟩ := LocalDensity.DVR.exists_diag_of_unimodular (φ.map (Int.castRingHom ℤ_[p]))
    (p : ℤ_[p]) PadicInt.irreducible_p (Siegel.Kneser.not_p_dvd_two hp) hunimod
  have hwu : ∀ i, IsUnit (w i) := fun i => (isUnit_iff_not_dvd p _).2 (hw i)
  have h3 : IsometricGL (QuadForm.diag w) (φ.map (Int.castRingHom ℤ_[p])) := by
    obtain ⟨U, hU, hUe⟩ := hE
    exact ((isometricGL_iff_isometricIn _ _).2 ⟨U, hU, fun x => (hUe x).symm⟩).symm
  have hrep : RepD c w := by
    have h1 := RepD.of_injective c (Fin.castLE (show v + 1 ≤ n by omega)) (Fin.castLE_injective _)
    have e : (fun j : Fin (v + 1) => c (Fin.castLE (show v + 1 ≤ n by omega) j)) =
        fun j => u (Fin.castLE (show v + 1 ≤ n by omega) j) := by
      funext j
      have hj := j.2
      have : ((Fin.castLE (show v + 1 ≤ n by omega) j : Fin n) : ℕ) < rankModP p f := by
        simp only [Fin.val_castLE]; omega
      rw [hc]
      simp only [this, ↓reduceIte]
    rw [e] at h1
    exact h1.trans (RepD.of_units p hp _ w (fun j => hu _) hwu)
  exact RepOver.of_chain p hiso hrep h3

/-- **The hyperbolic plane represents every element** ($p$ odd): $\langle 1, -1\rangle$ represents $\langle x\rangle$, via
$x = \bigl(\tfrac{x+1}2\bigr)^2 - \bigl(\tfrac{x-1}2\bigr)^2$. -/
theorem RepD.hyperbolic (hp : p ≠ 2) (x : ℤ_[p]) :
    RepD (![1, -1] : Fin 2 → ℤ_[p]) (fun _ : Fin 1 => x) := by
  obtain ⟨h, hh⟩ : ∃ h : ℤ_[p], 2 * h = 1 :=
    ⟨↑((isUnit_two_padic p hp).unit⁻¹), (isUnit_two_padic p hp).mul_val_inv⟩
  refine ⟨Matrix.of fun i _ => if i = 0 then h * (x + 1) else h * (x - 1), fun y => ?_⟩
  simp [Fin.sum_univ_two, mulVec, dotProduct]
  linear_combination (x * y 0 ^ 2 * (2 * h + 1)) * hh

/-- **$A_{m+1}$ at a prime $p$ with $p \,\|\, m + 2$** ($p$ odd; $A_5$ at $3$, $A_6$ at $7$): a Watson-minimal positive
definite $f$ in $n \ge 12$ variables with $m + 1 \le r_p(f)$ represents $A_{m+1}$ (`phiA (m + 1)`) over $\mathbb Z_p$,
for $m \le 8$, where $m + 2 = p q$ with $p \nmid q$. *Proof:* the Jordan decomposition of $A_{m+1}$ over $\mathbb Z_p$ has
$\sum \nu_i = v_p(\det H) = 1$, so $A_{m+1} \cong \langle w_0, \dots, w_{m-1}, p w'\rangle$. If $n - r \ge 2$, represent
$\langle w_0, \dots, w_{m-1}\rangle$ by the first $m + 1$ unit coordinates and $\langle p w'\rangle$ by
$p\langle u_r, u_{r+1}\rangle$ (`RepD.of_units`, `RepD.append`). Otherwise $r \ge n - 1 \ge 11 \ge m + 3$, and $\langle w,
p w'\rangle$ is represented by $\langle w, 1, -1\rangle$ (`RepD.hyperbolic`), itself represented by $m + 3$ unit
coordinates. -/
theorem repOver_phiA_special {n m q : ℕ} {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f)
    (hn : 12 ≤ n) (hp : p ≠ 2) (hmq : m + 2 = p * q) (hq : ¬ p ∣ q) (hm : m ≤ 8)
    (hr : m + 1 ≤ rankModP p f) : RepOver ℤ_[p] f (phiA (m + 1)) := by
  classical
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hpp.ne_zero
  obtain ⟨u, hu, hiso⟩ := exists_diag_of_minimal_odd hf hmin p hp
  have hrn : rankModP p f ≤ n := rankModP_le p f
  set r := rankModP p f with hrdef
  set c : Fin n → ℤ_[p] := fun i => if (i : ℕ) < r then u i else (p : ℤ_[p]) * u i with hc
  have hcu : ∀ k : Fin n, (k : ℕ) < r → c k = u k := fun k hk => by
    rw [hc]; simp only [hk, ↓reduceIte]
  have hcp : ∀ k : Fin n, r ≤ (k : ℕ) → c k = (p : ℤ_[p]) * u k := fun k hk => by
    rw [hc]; simp only [show ¬ (k : ℕ) < r from not_lt.mpr hk, ↓reduceIte]
  -- Jordan decomposition of A_{m+1}
  have hA : (phiA (m + 1)).hessian.det ≠ 0 := by
    rw [phiA_hessian_det]; positivity
  obtain ⟨T, T', ν, w, hTT, hw, hT⟩ := exists_diag_padic p hp (phiA (m + 1)) hA
  set a : Fin (m + 1) → ℤ_[p] := fun i => (p : ℤ_[p]) ^ ν i * w i with ha
  have hTu : IsUnit T.det := Matrix.isUnit_det_of_right_inverse hTT
  have hevalT : ∀ x, (QuadForm.diag a).eval x = ((phiA (m + 1)).map (Int.castRingHom ℤ_[p])).eval (T *ᵥ x) := by
    intro x
    rw [eval_diag', eval_map_padic, hT]
  have step1 : IsometricGL ((phiA (m + 1)).map (Int.castRingHom ℤ_[p])) (QuadForm.diag a) := by
    rw [isometricGL_iff_isometricIn]
    exact ⟨T, hTu, fun x => (hevalT x).symm⟩
  -- the exponents sum to one
  have hdetA : (((phiA (m + 1)).hessian.det : ℤ) : ℤ_[p]) = (p : ℤ_[p]) * q := by
    rw [phiA_hessian_det]
    have := congrArg (Nat.cast : ℕ → ℤ_[p]) hmq
    push_cast at this ⊢
    linear_combination this
  have hdetEq := congrArg Matrix.det (LocalDensity.DVR.hessian_eq_of_eval hevalT)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LocalDensity.DVR.det_hessian_diag,
    hessian_map_det_padic, hdetA] at hdetEq
  have hprod : ∏ i, a i = (p : ℤ_[p]) ^ (∑ i, ν i) * ∏ i, w i := by
    simp only [ha, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hprod] at hdetEq
  have hqu : IsUnit (q : ℤ_[p]) := by
    rw [isUnit_iff_not_dvd]
    intro h
    apply hq
    have := (toZMod_eq_zero_iff_dvd p _).2 h
    rw [map_natCast, ZMod.natCast_eq_zero_iff] at this
    exact this
  have hWu : IsUnit (∏ i, w i) := isUnit_prod_padic p w hw
  have hU1 : IsUnit ((2 : ℤ_[p]) ^ (m + 1) * ∏ i, w i) := ((isUnit_two_padic p hp).pow _).mul hWu
  have hU2 : IsUnit (T.det * T.det * (q : ℤ_[p])) := (hTu.mul hTu).mul hqu
  have hnu : ∀ U : ℤ_[p], IsUnit U → ¬ (p : ℤ_[p]) ∣ U := fun U hU => (isUnit_iff_not_dvd p U).1 hU
  have hE : (p : ℤ_[p]) ^ (∑ i, ν i) * ((2 : ℤ_[p]) ^ (m + 1) * ∏ i, w i) =
      (p : ℤ_[p]) * (T.det * T.det * (q : ℤ_[p])) := by
    linear_combination hdetEq
  have hs : (∑ i, ν i) = 1 := by
    by_contra hne
    rcases Nat.lt_or_ge (∑ i, ν i) 1 with h0 | h2
    · have h0' : (∑ i, ν i) = 0 := by omega
      rw [h0', pow_zero, one_mul] at hE
      exact hnu _ hU1 ⟨_, hE⟩
    · obtain ⟨k, hk⟩ : ∃ k, ∑ i, ν i = k + 2 := ⟨(∑ i, ν i) - 2, by omega⟩
      have hE' : (p : ℤ_[p]) * ((p : ℤ_[p]) ^ (k + 1) * ((2 : ℤ_[p]) ^ (m + 1) * ∏ i, w i)) =
          (p : ℤ_[p]) * (T.det * T.det * (q : ℤ_[p])) := by
        calc (p : ℤ_[p]) * ((p : ℤ_[p]) ^ (k + 1) * ((2 : ℤ_[p]) ^ (m + 1) * ∏ i, w i))
            = (p : ℤ_[p]) ^ (∑ i, ν i) * ((2 : ℤ_[p]) ^ (m + 1) * ∏ i, w i) := by rw [hk]; ring
          _ = _ := hE
      have := mul_left_cancel₀ hp0 hE'
      exact hnu _ hU2 ⟨(p : ℤ_[p]) ^ k * ((2 : ℤ_[p]) ^ (m + 1) * ∏ i, w i), by rw [← this]; ring⟩
  obtain ⟨i0, hi0, hother⟩ : ∃ i0, ν i0 = 1 ∧ ∀ i, i ≠ i0 → ν i = 0 := by
    have hne : ∃ i, ν i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      simp [h] at hs
    obtain ⟨i0, hi0⟩ := hne
    have hle : ν i0 ≤ ∑ i, ν i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
    refine ⟨i0, by omega, fun i hi => ?_⟩
    by_contra hne
    have h1 := Finset.sum_le_sum_of_subset (f := ν) (Finset.subset_univ {i0, i})
    rw [Finset.sum_pair (Ne.symm hi)] at h1
    omega
  -- move the p-entry to the last coordinate
  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap (Fin.last m) i0 with hσ
  set t : Fin (m + 1) → ℤ_[p] := fun j => a (σ j) with ht
  have hlast : t (Fin.last m) = (p : ℤ_[p]) * w i0 := by
    simp only [ht, hσ, Equiv.swap_apply_left, ha, hi0, pow_one]
  have hunits : ∀ j : Fin m, IsUnit (t (Fin.castSucc j)) := by
    intro j
    have hne : σ (Fin.castSucc j) ≠ i0 := by
      intro h
      have : σ (Fin.castSucc j) = σ (Fin.last m) := by rw [h]; simp [hσ]
      exact (Fin.castSucc_lt_last j).ne (σ.injective this)
    simp only [ht, ha, hother _ hne, pow_zero, one_mul]
    exact hw _
  have h3 : IsometricGL (QuadForm.diag t) ((phiA (m + 1)).map (Int.castRingHom ℤ_[p])) :=
    (step1.trans (isometricGL_diag_perm a σ)).symm
  -- representing t
  have hw0 : IsUnit (w i0) := hw i0
  have hcu' : ∀ k : Fin n, (k : ℕ) < r → IsUnit (c k) := fun k hk => by rw [hcu k hk]; exact hu k
  have hrep : RepD c t := by
    rcases Nat.lt_or_ge (r + 1) n with hA2 | hA2
    · -- two non-unit coordinates are available
      obtain ⟨e, he_val⟩ : ∃ e : Fin (m + 1 + 2) → Fin n, ∀ j, (e j : ℕ) =
          if (j : ℕ) < m + 1 then (j : ℕ) else r + ((j : ℕ) - (m + 1)) :=
        ⟨fun j => ⟨if (j : ℕ) < m + 1 then (j : ℕ) else r + ((j : ℕ) - (m + 1)), by
          have := j.2; split_ifs <;> omega⟩, fun j => rfl⟩
      have he : Function.Injective e := by
        intro i j hij
        have h := congrArg Fin.val hij
        rw [he_val, he_val] at h
        apply Fin.ext
        have := i.2; have := j.2
        split_ifs at h <;> omega
      have h1 := RepD.of_injective c e he
      set B : Fin (m + 1 + 2) → ℤ_[p] := fun j => c (e j) with hB
      have hX : RepD (B ∘ Fin.castAdd 2) (fun j : Fin m => t (Fin.castSucc j)) := by
        refine RepD.of_units p hp _ _ (fun j => ?_) hunits
        simp only [Function.comp, hB]
        apply hcu'
        rw [he_val]
        have := j.2
        simp only [Fin.val_castAdd]
        split_ifs
        omega
      have hY : RepD (B ∘ Fin.natAdd (m + 1)) (fun _ : Fin 1 => t (Fin.last m)) := by
        set u2 : Fin 2 → ℤ_[p] := fun j => u (e (Fin.natAdd (m + 1) j)) with hu2
        have h2 : RepD u2 (fun _ : Fin 1 => w i0) :=
          RepD.of_units p hp u2 _ (fun j => hu _) (fun _ => hw0)
        have h2' := h2.smul (p : ℤ_[p])
        have e1 : (B ∘ Fin.natAdd (m + 1)) = fun j => (p : ℤ_[p]) * u2 j := by
          funext j
          simp only [Function.comp, hB]
          apply hcp
          rw [he_val]
          have := j.2
          simp only [Fin.val_natAdd]
          split_ifs <;> omega
        rw [e1, hlast]
        exact h2'
      have h4 := RepD.append hX hY
      have e1 : Fin.append (B ∘ Fin.castAdd 2) (B ∘ Fin.natAdd (m + 1)) = B := Fin.append_castAdd_natAdd
      rw [e1, ← eq_append_snoc] at h4
      exact h1.trans h4
    · -- r ≥ n - 1 ≥ 11 ≥ m + 3
      have hmn : m + 1 + 2 ≤ n := by omega
      have h1 := RepD.of_injective c (Fin.castLE hmn) (Fin.castLE_injective _)
      have hX : RepD (fun j : Fin (m + 1 + 2) => c (Fin.castLE hmn j))
          (Fin.append (fun j : Fin m => t (Fin.castSucc j)) (![1, -1] : Fin 2 → ℤ_[p])) := by
        refine RepD.of_units_lt p hp (by omega) _ _ (fun j => ?_) (fun i => ?_)
        · apply hcu'
          have := j.2
          simp only [Fin.val_castLE]
          omega
        · refine Fin.addCases (motive := fun i => IsUnit
            (Fin.append (fun j : Fin m => t (Fin.castSucc j)) (![1, -1] : Fin 2 → ℤ_[p]) i))
            (fun j => ?_) (fun j => ?_) i
          · rw [Fin.append_left]; exact hunits j
          · rw [Fin.append_right]
            fin_cases j <;> simp
      have hY := RepD.append (RepD.refl (fun j : Fin m => t (Fin.castSucc j)))
        (RepD.hyperbolic p hp (t (Fin.last m)))
      rw [← eq_append_snoc] at hY
      exact h1.trans (hX.trans hY)
  exact RepOver.of_chain p hiso hrep h3

end Padic

/-! ### The odd-prime part of `WatsonLocalProbes` -/

/-- **The local probes at an odd prime** (Watson 1963, Lemma 2, local part ((4.12), p. 555), $p$ odd): a Watson-minimal
positive definite form $f$ in $n \ge 12$ variables represents, over $\mathbb Z_p$, $A_5$ and $\Phi_5$ if $r_p(f) \ge 6$;
$A_6$ and $\Phi_6$ if $r_p(f) \ge 7$; $E_7$ if $r_p(f) \ge 8$; $E_8$ if $r_p(f) \ge 9$; $\Phi_9$ if $r_p(f) \ge 10$.
*Proof:* the probes with $p \nmid \det H$ by `repOver_of_unimodular` (determinants $v + 1$ for $A_v$, $4$, $2$, $1$);
the two exceptions $A_5$ at $p = 3$ and $A_6$ at $p = 7$ by `repOver_phiA_special`. This is the odd-prime part of the
named input `WatsonLocalProbes`. -/
@[kb "watson1963" "§4, Lemma 2, local part ((4.12), p. 555; odd p)"]
theorem localProbes_odd {n : ℕ} {f : QuadForm ℤ n} (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f) (hn : 12 ≤ n)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (6 ≤ rankModP p f → RepOver ℤ_[p] f (phiA 5) ∧ RepOver ℤ_[p] f (phiD 4)) ∧
    (7 ≤ rankModP p f → RepOver ℤ_[p] f (phiA 6) ∧ RepOver ℤ_[p] f (phiD 5)) ∧
    (8 ≤ rankModP p f → RepOver ℤ_[p] f formE7) ∧
    (9 ≤ rankModP p f → RepOver ℤ_[p] f formE8) ∧
    (10 ≤ rankModP p f → RepOver ℤ_[p] f (phiD 8)) := by
  have hpp : p.Prime := Fact.out
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
  have h4 : ¬ (p : ℤ) ∣ 4 := by
    intro h
    have h' : p ∣ 2 ^ 2 := by exact_mod_cast h
    exact h2 (by exact_mod_cast hpp.dvd_of_dvd_pow h')
  have h1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have : p ∣ 1 := by exact_mod_cast h
    exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
  refine ⟨fun h6 => ⟨?_, ?_⟩, fun h7 => ⟨?_, ?_⟩, fun h8 => ?_, fun h9 => ?_, fun h10 => ?_⟩
  · by_cases hp3 : p = 3
    · have := repOver_phiA_special p (m := 4) (q := 2) hf hmin hn hp (by rw [hp3]) (by rw [hp3]; decide)
        (by norm_num) (by omega)
      exact this
    · refine repOver_of_unimodular p hf hmin hp (phiA 5) ?_ (by omega)
      rw [phiA_hessian_det]
      intro h
      have h' : p ∣ 2 * 3 := by norm_num at h; exact_mod_cast h
      rcases (Nat.Prime.dvd_mul hpp).mp h' with h | h
      · exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h)
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h)
  · exact repOver_of_unimodular p hf hmin hp (phiD 4) (by rw [phiD_hessian_det]; exact h4) (by omega)
  · by_cases hp7 : p = 7
    · exact repOver_phiA_special p (m := 5) (q := 1) hf hmin hn hp (by rw [hp7]) (by rw [hp7]; decide)
        (by norm_num) (by omega)
    · refine repOver_of_unimodular p hf hmin hp (phiA 6) ?_ (by omega)
      rw [phiA_hessian_det]
      intro h
      have h' : p ∣ 7 := by norm_num at h; exact_mod_cast h
      exact hp7 ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h')
  · exact repOver_of_unimodular p hf hmin hp (phiD 5) (by rw [phiD_hessian_det]; exact h4) (by omega)
  · exact repOver_of_unimodular p hf hmin hp formE7 (by rw [formE7_hessian_det]; exact h2) (by omega)
  · exact repOver_of_unimodular p hf hmin hp formE8 (by rw [formE8_hessian_det]; exact h1) (by omega)
  · exact repOver_of_unimodular p hf hmin hp (phiD 8) (by rw [phiD_hessian_det]; exact h4) (by omega)

end QuadFormsKB.Watson1963
