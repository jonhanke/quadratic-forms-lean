/-
# Cassels, Chapter 14, §7: splitting off hyperbolic planes (diagonal forms)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §7, pp. 353–354: the algebra over a field $K$ of characteristic
$0$ behind steps 1 and 3 of the reduction in `QuadFormsKB.Literature.Cassels.Ch14.HasseFour`. The hyperbolic plane is
written diagonally, $\langle 1, -1 \rangle$.

* `exists_split_diag_four`: an isotropic nondegenerate $\langle a_0, a_1, a_2, a_3 \rangle$ is isometric to
  $\langle b_0, b_1, 1, -1 \rangle$ with $b_0 b_1 = -a_0 a_1 a_2 a_3$ (Cassels' $f \cong g_p \perp H$, with
  $d(g_p) = -d(f)$);
* `diag_six_hyperbolic`: $\langle b_0, b_1, 1, -1, -b_0, -b_1 \rangle$ is the sum of three hyperbolic planes;
* `diag_append_isometric`, `diag_neg_isometric`: isometries of diagonal blocks.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Existence

namespace QuadFormsKB.Composition

open QuadForm

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Isotropy transfers along an isometry: if `Q.IsometricIn K Q'` and `Q'` is isotropic, so is `Q`. -/
theorem isotropicIn_of_isometricIn_aux {n : ℕ} {Q Q' : QuadForm K n} (h : Q.IsometricIn K Q')
    (hQ' : Q'.IsotropicIn K) : Q.IsotropicIn K := by
  obtain ⟨P, hP, hPQ⟩ := h
  obtain ⟨x, hx0, hx⟩ := hQ'
  refine ⟨P.mulVec x, fun h0 => hx0 ?_, by rw [hPQ]; exact hx⟩
  exact Matrix.eq_zero_of_mulVec_eq_zero hP.ne_zero h0

/-- Scaling the second entry of $\langle b_0, b_1, 1, -1 \rangle$ by a square. -/
theorem diag_four_scale_aux (b₀ b₁ t : K) (ht : t ≠ 0) :
    (diag ![b₀, b₁, 1, -1]).IsometricIn K (diag ![b₀, b₁ / t ^ 2, 1, -1]) := by
  refine ⟨Matrix.diagonal ![1, t⁻¹, 1, 1], ?_, fun x => ?_⟩
  · rw [isUnit_iff_ne_zero, Matrix.det_diagonal, Fin.prod_univ_four]
    simp [ht]
  · rw [PadicClass.evalIn_diag_self, PadicClass.evalIn_diag_self, Fin.sum_univ_four, Fin.sum_univ_four]
    simp [Matrix.mulVec_diagonal]
    field_simp

/-- $\langle b, -b \rangle \cong \langle 1, -1 \rangle$ for $b \ne 0$. -/
theorem diag_pair_hyperbolic_aux {b : K} (hb : b ≠ 0) :
    (diag ![b, -b]).IsometricIn K (diag ![1, -1]) := by
  refine ⟨!![(1 + b⁻¹) / 2, (1 - b⁻¹) / 2; (1 - b⁻¹) / 2, (1 + b⁻¹) / 2], ?_, fun x => ?_⟩
  · rw [isUnit_iff_ne_zero, Matrix.det_fin_two_of]
    have : (1 + b⁻¹) / 2 * ((1 + b⁻¹) / 2) - (1 - b⁻¹) / 2 * ((1 - b⁻¹) / 2) = b⁻¹ := by ring
    rw [this]; exact inv_ne_zero hb
  · rw [PadicClass.evalIn_diag_self, PadicClass.evalIn_diag_self, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    ring

/-- The linear equivalence $\langle a, c \rangle \cong \langle a \rangle \times \langle c \rangle$ as Mathlib forms. -/
theorem equivalent_diag_append_aux {m n : ℕ} (a : Fin m → K) (c : Fin n → K) :
    ((diag (Fin.append a c)).toQuadraticFormIn K).Equivalent
      (((diag a).toQuadraticFormIn K).prod ((diag c).toQuadraticFormIn K)) :=
  ⟨{ finAddLinearEquiv K m n with
    map_app' := fun x => by
      simp only [QuadraticMap.prod_apply, toQuadraticFormIn_apply, PadicClass.evalIn_diag_self,
        Fin.sum_univ_add]
      simp [finAddLinearEquiv, Fin.append_left, Fin.append_right] }⟩

/-- **An isotropic quaternary diagonal form splits off a hyperbolic plane** (Cassels, Ch. 14, §7, p. 354, step 1;
Ch. 2, Lemma 2.1): if $\langle a_0, a_1, a_2, a_3 \rangle$ ($a_i \ne 0$) is isotropic over $K$, then it is isometric
over $K$ to $\langle b_0, b_1, 1, -1 \rangle$ for some non-zero $b_0, b_1$ with $b_0 b_1 = -a_0 a_1 a_2 a_3$. -/
theorem exists_split_diag_four {a : Fin 4 → K} (ha : ∀ i, a i ≠ 0) (hiso : (diag a).IsotropicIn K) :
    ∃ b₀ b₁ : K, b₀ ≠ 0 ∧ b₁ ≠ 0 ∧ b₀ * b₁ = -(a 0 * a 1 * a 2 * a 3) ∧
      (diag a).IsometricIn K (diag ![b₀, b₁, 1, -1]) := by
  obtain ⟨α, hα, hiso1⟩ := exists_isometric_diag_cons (m := 3) (nondegenerate_diag ha) one_ne_zero
    (PadicClass.representsIn_of_isotropic ha hiso 1)
  have hiso2 : (diag (Fin.cons 1 α : Fin 4 → K)).IsotropicIn K :=
    isotropicIn_of_isometricIn_aux (isometricIn_symm K hiso1) hiso
  have hR : (diag α).RepresentsIn K (-1) := by
    obtain ⟨y, hy0, hy⟩ := (PadicClass.isotropicIn_diag_iff _).mp hiso2
    rw [Fin.sum_univ_succ] at hy
    simp only [Fin.cons_zero, Fin.cons_succ, one_mul] at hy
    by_cases ht : y 0 = 0
    · rw [ht] at hy
      refine PadicClass.representsIn_of_isotropic hα
        ((PadicClass.isotropicIn_diag_iff α).mpr ⟨Fin.tail y, fun h => hy0 ?_, ?_⟩) (-1)
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ht
        · exact congrFun h j
      · simpa [Fin.tail] using hy
    · rw [PadicClass.representsIn_diag_iff]
      refine ⟨fun i => (y 0)⁻¹ * y i.succ, ?_⟩
      have : ∑ i : Fin 3, α i * ((y 0)⁻¹ * y i.succ) ^ 2 = ((y 0)⁻¹) ^ 2 * ∑ i : Fin 3, α i * y i.succ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, show ∑ i : Fin 3, α i * y i.succ ^ 2 = -(y 0) ^ 2 by
        rw [eq_neg_iff_add_eq_zero, add_comm]; simpa using hy]
      field_simp
  obtain ⟨β, hβ, hiso3⟩ := exists_isometric_diag_cons (m := 2) (nondegenerate_diag hα)
    (neg_ne_zero.mpr one_ne_zero) hR
  have hiso5 := isometricIn_trans K hiso1 (isometricIn_diag_cons_of K 1 hiso3)
  let v : Fin 4 → K := Fin.cons 1 (Fin.cons (-1) β)
  let σ : Equiv.Perm (Fin 4) := ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩
  have hv : v ∘ σ = ![β 0, β 1, 1, -1] := by
    funext i; fin_cases i <;> rfl
  have hiso6 : (diag a).IsometricIn K (diag ![β 0, β 1, 1, -1]) := by
    rw [← hv]; exact isometricIn_trans K hiso5 (PadicClass.isometric_diag_comp_perm v σ)
  obtain ⟨t, ht, hd⟩ := PadicClass.disc_of_isometric hiso6
  simp [Fin.prod_univ_four] at hd
  have hb0 : β 0 ≠ 0 := hβ 0
  have hb1 : β 1 ≠ 0 := hβ 1
  refine ⟨β 0, β 1 / t ^ 2, hb0, div_ne_zero hb1 (pow_ne_zero 2 ht), ?_,
    isometricIn_trans K hiso6 (diag_four_scale_aux _ _ t ht)⟩
  field_simp
  linear_combination (-1 : K) * hd

/-- **Isometric diagonal blocks give isometric diagonal sums**: if $\langle a \rangle \cong \langle a' \rangle$ and
$\langle c \rangle \cong \langle c' \rangle$ over $K$, then $\langle a, c \rangle \cong \langle a', c' \rangle$
(`Fin.append`). -/
theorem diag_append_isometric {m n : ℕ} {a a' : Fin m → K} {c c' : Fin n → K}
    (ha : (diag a).IsometricIn K (diag a')) (hc : (diag c).IsometricIn K (diag c')) :
    (diag (Fin.append a c)).IsometricIn K (diag (Fin.append a' c')) := by
  rw [isometricIn_iff_equivalent] at ha hc ⊢
  obtain ⟨e₁⟩ := ha
  obtain ⟨e₂⟩ := hc
  exact (equivalent_diag_append_aux a' c').trans
    ⟨QuadraticMap.IsometryEquiv.prod e₁ e₂⟩ |>.trans (equivalent_diag_append_aux a c).symm

/-- **Negating isometric diagonal forms**: $\langle c \rangle \cong \langle c' \rangle$ implies
$\langle -c \rangle \cong \langle -c' \rangle$. -/
theorem diag_neg_isometric {n : ℕ} {c c' : Fin n → K} (h : (diag c).IsometricIn K (diag c')) :
    (diag (-c)).IsometricIn K (diag (-c')) := by
  obtain ⟨P, hP, hPQ⟩ := h
  refine ⟨P, hP, fun x => ?_⟩
  have := hPQ x
  rw [PadicClass.evalIn_diag_self, PadicClass.evalIn_diag_self] at this
  rw [PadicClass.evalIn_diag_self, PadicClass.evalIn_diag_self]
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, this]

/-- **$g \perp H \perp (-g)$ is three hyperbolic planes** (Cassels, Ch. 14, §7, p. 354, step 3): for non-zero
$b_0, b_1$, $\langle b_0, b_1, 1, -1, -b_0, -b_1 \rangle \cong \langle 1, -1, 1, -1, 1, -1 \rangle$ over $K$. -/
theorem diag_six_hyperbolic {b₀ b₁ : K} (h₀ : b₀ ≠ 0) (h₁ : b₁ ≠ 0) :
    (diag ![b₀, b₁, 1, -1, -b₀, -b₁]).IsometricIn K (diag ![1, -1, 1, -1, 1, -1]) := by
  let v : Fin 6 → K := ![b₀, b₁, 1, -1, -b₀, -b₁]
  let σ : Equiv.Perm (Fin 6) := ⟨![0, 4, 1, 5, 2, 3], ![0, 2, 4, 5, 1, 3], by decide, by decide⟩
  have hv : v ∘ σ = Fin.append (Fin.append ![b₀, -b₀] ![b₁, -b₁]) ![1, -1] := by
    funext i; fin_cases i <;> simp [v, σ, Fin.append, Fin.addCases]
  have hw : (![1, -1, 1, -1, 1, -1] : Fin 6 → K) =
      Fin.append (Fin.append ![1, -1] ![1, -1]) ![1, -1] := by
    funext i; fin_cases i <;> simp [Fin.append, Fin.addCases]
  have h2 := diag_pair_hyperbolic_aux h₀
  have h3 := diag_pair_hyperbolic_aux h₁
  have h4 := diag_append_isometric (diag_append_isometric h2 h3) (isometricIn_refl K (diag ![(1 : K), -1]))
  refine isometricIn_trans K (PadicClass.isometric_diag_comp_perm v σ) ?_
  rw [hv, hw]
  exact h4

end QuadFormsKB.Composition
