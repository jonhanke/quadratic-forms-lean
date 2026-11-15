/-
# Chenevier–Lannes, §3.1: $d$-neighbours of even unimodular lattices are even unimodular

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.1, pp. 46–48 (a $d$-neighbour of $L$ is again a q-module
over $\mathbb{Z}$, of the same dimension), and §3.4.2, Theorem 3.4.2.10, p. 69 (the holy neighbours are Niemeier
lattices). Printed page numbers.

**Proves** (unconditional):
- `exists_basis_of_isDNeighbor`: a $d$-neighbour $L' \subset \mathbb{Q}^n$ of a unimodular $L = \mathbb{Z}^n$ has a
  basis: $L' = g\,\mathbb{Z}^n$ with $\det g \ne 0$ (it lies between $dL$ and $\tfrac1d L$);
- `isEvenUnimodular_of_isDNeighbor`: if $L$ is even unimodular (positive definite, $\det H = 1$), the form of a
  $d$-neighbour $L'$ in such a basis is even unimodular (positive definite, determinant $1$, by self-duality of $L'$),
  so $[L'] \in X_n$;
- `voisLat_isEvenUnimodular`: in particular $\mathrm{vois}_d(L; u)$ is an even unimodular lattice of
  dimension $n$ (with Proposition 3.1.4, `isDNeighbor_voisLat`).

The basis lemma adapts `QuadFormsKB.Siegel.Kneser.exists_basis_of_le` (stated there for a prime $p$) to an integer
$d \ge 1$.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave4.NeighborLattices

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### Lattices between $dL$ and $\tfrac1d L$ have a basis -/

section Basis

variable {d : ℕ}

/-- $\tfrac1d\mathbb{Z}^n \cong \mathbb{Z}^n$ (`scaledLat n d`, for $d \ne 0$). -/
noncomputable def scaledEquivD (hd : d ≠ 0) : (Fin n → ℤ) ≃ₗ[ℤ] scaledLat n d where
  toFun y := ⟨(1 / (d : ℚ)) • cv y, y, rfl⟩
  map_add' y z := by ext1; simp [cv_add, smul_add]
  map_smul' k y := by
    ext1
    simp only [RingHom.id_apply, SetLike.val_smul, cv_smul]
    rw [smul_comm, ← Int.cast_smul_eq_zsmul ℚ]
  invFun x := intPart ((d : ℚ) • (x : Fin n → ℚ))
  left_inv y := by
    have : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    simp only
    rw [smul_smul, show (d : ℚ) * (1 / d) = 1 by field_simp, one_smul, intPart_cv]
  right_inv x := by
    obtain ⟨x, y, rfl⟩ := x
    have : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    ext1
    simp only
    rw [smul_smul, show (d : ℚ) * (1 / d) = 1 by field_simp, one_smul, intPart_cv]

/-- **Lattices between $d\mathbb{Z}^n$ and $\tfrac1d\mathbb{Z}^n$ have a basis** ($d \ge 1$): $L = g\mathbb{Z}^n$ with
$\det g \ne 0$. (Adapted from `QuadFormsKB.Siegel.Kneser.exists_basis_of_le`, stated there for a prime.) -/
theorem exists_basis_of_le_scaled (hd : d ≠ 0) {L : Submodule ℤ (Fin n → ℚ)} (hL : L ≤ scaledLat n d)
    (hdL : ∀ y : Fin n → ℤ, cv ((d : ℤ) • y) ∈ L) :
    ∃ g : Matrix (Fin n) (Fin n) ℚ, g.det ≠ 0 ∧ L = imgLat g := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  let bO : Module.Basis (Fin n) ℤ (scaledLat n d) := (Pi.basisFun ℤ (Fin n)).map (scaledEquivD hd)
  obtain ⟨k, bL⟩ := Submodule.basisOfPidOfLE hL bO
  haveI : Module.Finite ℤ (scaledLat n d) := Module.Finite.of_basis bO
  haveI : Module.Finite ℤ L := Module.Finite.of_basis bL
  have hk1 : k ≤ n := by
    have hli : LinearIndependent ℤ ((Submodule.inclusion hL) ∘ bL) :=
      bL.linearIndependent.map' _ (Submodule.ker_inclusion _ _ hL)
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_eq_card_basis bO, Fintype.card_fin] at this
  have hk2 : n ≤ k := by
    let v : Fin n → L := fun i => ⟨cv ((d : ℤ) • Pi.single i 1), hdL _⟩
    have hli : LinearIndependent ℤ v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have := congrArg (fun x : L => (x : Fin n → ℚ) i) hc
      simp only [v, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, cv_apply,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Submodule.coe_zero, Pi.zero_apply] at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)] at this
      simp only [if_true, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast] at this
      have : (c i : ℚ) * d = 0 := by simpa using this
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hd0
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_eq_card_basis bL, Fintype.card_fin] at this
  have hk : k = n := le_antisymm hk1 hk2
  subst hk
  let g : Matrix (Fin k) (Fin k) ℚ := Matrix.of fun i j => ((bL j : L) : Fin k → ℚ) i
  have hcol : ∀ j, g.col j = ((bL j : L) : Fin k → ℚ) := fun j => by ext i; rfl
  have hLg : L = imgLat g := by
    ext x
    constructor
    · intro hx
      refine ⟨fun j => bL.repr ⟨x, hx⟩ j, ?_⟩
      rw [mulVec_cv_eq_sum]
      have := congrArg (fun y : L => (y : Fin k → ℚ)) (bL.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      conv_lhs => rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [hcol]
    · rintro ⟨c, rfl⟩
      rw [mulVec_cv_eq_sum]
      exact L.sum_mem fun j _ => L.smul_of_tower_mem _ (by rw [hcol]; exact (bL j).2)
  refine ⟨g, ?_, hLg⟩
  have hC : ∀ i, ∃ c : Fin k → ℤ, cv ((d : ℤ) • Pi.single i 1) = g *ᵥ cv c := fun i => by
    have := hdL (Pi.single i 1); rw [hLg] at this; exact this
  choose C hC using hC
  let Cm : Matrix (Fin k) (Fin k) ℚ := Matrix.of fun r i => (C i r : ℚ)
  have hgC : g * Cm = (d : ℚ) • (1 : Matrix (Fin k) (Fin k) ℚ) := by
    ext r i
    have h1 := congrFun (hC i) r
    have h2 : (g * Cm) r i = (g *ᵥ cv (C i)) r := by
      simp only [mul_apply, mulVec, dotProduct, Cm, of_apply, cv_apply]
    rw [h2, ← h1]
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  intro h0
  have := congrArg Matrix.det hgC
  rw [det_mul, h0, zero_mul, det_smul, det_one, mul_one, Fintype.card_fin] at this
  exact pow_ne_zero _ hd0 this.symm

end Basis

/-- **A $d$-neighbour has a basis**: $L' = g\,\mathbb{Z}^n$ with $\det g \ne 0$ ($L$ unimodular, $d \ge 1$). -/
theorem exists_basis_of_isDNeighbor {Q : QuadForm ℤ n} (hdet : IsUnit Q.hessian.det) {d : ℕ} (hd : 1 ≤ d)
    {N : Submodule ℤ (Fin n → ℚ)} (hN : IsDNeighbor Q d N) :
    ∃ g : Matrix (Fin n) (Fin n) ℚ, g.det ≠ 0 ∧ N = imgLat g := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  refine exists_basis_of_le_scaled (by omega) (fun x hx => ?_) hN.smul_mem
  obtain ⟨y, hy⟩ := hN.smul_mem_std hdet hx
  refine ⟨y, ?_⟩
  rw [← hy, smul_smul, one_div_mul_cancel hd0, one_smul]

/-- **A $d$-neighbour of an even unimodular lattice is even unimodular** (Chenevier–Lannes, §3.1, pp. 46–48): if
$Q$ is even unimodular (`IsEvenUnimodular`: positive definite with $\det H = 1$) and $L'$ is a $d$-neighbour of
$L = \mathbb{Z}^n$ ($d \ge 1$), then $L' = g\,\mathbb{Z}^n$ for some $g$ with $\det g \ne 0$, and the form $P$ of $L'$
in this basis ($P(x) = Q(gx)$) is even unimodular. Unconditional. -/
@[kb "chenevierlannes2019" "§3.1, pp. 46–48 (d-neighbours of even unimodular lattices are even unimodular)"]
theorem isEvenUnimodular_of_isDNeighbor {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {d : ℕ} (hd : 1 ≤ d)
    {N : Submodule ℤ (Fin n → ℚ)} (hN : IsDNeighbor Q d N) :
    ∃ (g : Matrix (Fin n) (Fin n) ℚ) (P : QuadForm ℤ n), g.det ≠ 0 ∧ N = imgLat g ∧
      (∀ x, P.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) ∧ IsEvenUnimodular P := by
  classical
  have hdet : IsUnit Q.hessian.det := by rw [hQ.det_one]; exact isUnit_one
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  obtain ⟨g, hg, hNg⟩ := exists_basis_of_isDNeighbor hdet hd hN
  have hmem : ∀ c : Fin n → ℤ, g *ᵥ cv c ∈ N := fun c => by rw [hNg]; exact ⟨c, rfl⟩
  obtain ⟨P, hP⟩ := exists_gramForm (Q := Q) fun c => hN.even _ (hmem c)
  refine ⟨g, P, hg, hNg, hP, ?_, ?_⟩
  · -- positive definite: $P(c) = Q(gc) = Q(y)/d^2$ with $d\,gc = y \ne 0$
    intro c hc
    obtain ⟨y, hy⟩ := hN.smul_mem_std hdet (hmem c)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [cv_zero, smul_eq_zero] at hy
      rcases hy with h | h
      · exact hd0 h
      · have : cv c = 0 := by
          have := congrArg (fun x => g⁻¹ *ᵥ x) h
          simpa [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg)] using this
        exact hc (cv_injective (by rw [this, cv_zero]))
    have h1 : (P.eval c : ℚ) = Q.eval y / d ^ 2 := by
      rw [← evalIn_cv, hP, ← evalIn_cv, ← hy, evalIn_smulQ]
      field_simp
    have h2 : (0 : ℚ) < Q.eval y := by exact_mod_cast hQ.posDef y hy0
    have : (0 : ℚ) < P.eval c := by rw [h1]; positivity
    exact_mod_cast this
  · -- determinant: $\det P = (\det g)^2 > 0$, and $\det P = \pm 1$ by self-duality of $L'$
    set Hq := Q.hessian.map (algebraMap ℤ ℚ)
    set Pq := P.hessian.map (algebraMap ℤ ℚ)
    have hPq : Pq = gᵀ * Hq * g := hessian_eq_conj hP
    have hHq : Hq.det = 1 := by
      have := RingHom.map_det (algebraMap ℤ ℚ) Q.hessian
      rw [hQ.det_one] at this
      simp only [map_one, RingHom.mapMatrix_apply] at this
      exact this.symm
    have hdetP : Pq.det = g.det ^ 2 := by rw [hPq, det_mul, det_mul, det_transpose, hHq]; ring
    have hPq0 : IsUnit Pq.det := by rw [hdetP]; exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hg)
    have hPsym : Pqᵀ = Pq := by
      rw [← Matrix.transpose_map, (hessian_isSymm P).eq]
    -- the dual basis lies in $L'$
    have hcol : ∀ i, ∃ c : Fin n → ℤ, Pq⁻¹ *ᵥ Pi.single i 1 = cv c := fun i => by
      have hx : g *ᵥ (Pq⁻¹ *ᵥ Pi.single i 1) ∈ N := by
        refine (hN.selfDual _).mpr fun y hy => ?_
        rw [hNg] at hy
        obtain ⟨c, rfl⟩ := hy
        refine ⟨c i, ?_⟩
        rw [bQ, ← Kneser.dotProduct_conj, ← hPq, dotProduct_mulVec, ← mulVec_transpose, hPsym, mulVec_mulVec, mul_nonsing_inv _ hPq0, one_mulVec]
        simp [cv]
      rw [hNg] at hx
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, ?_⟩
      have := congrArg (fun x => g⁻¹ *ᵥ x) hc
      simpa [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg)] using this
    choose C hC using hcol
    let Cz : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun r i => C i r
    have hCz : Cz.map (algebraMap ℤ ℚ) = Pq⁻¹ := by
      ext r i
      have := congrFun (hC i) r
      simp only [Cz, Matrix.map_apply, of_apply]
      rw [show (Pq⁻¹ *ᵥ Pi.single i 1) r = Pq⁻¹ r i by simp [mulVec, dotProduct, Pi.single_apply]] at this
      rw [this]; simp [cv]
    have hmul : (P.hessian * Cz).map (algebraMap ℤ ℚ) = 1 := by
      rw [Matrix.map_mul, hCz, mul_nonsing_inv _ hPq0]
    have hmul' : P.hessian * Cz = 1 := by
      ext r i
      have := congrFun (congrFun hmul r) i
      simp only [Matrix.map_apply, Matrix.one_apply] at this
      rw [Matrix.one_apply]
      rw [eq_intCast] at this
      split_ifs at this ⊢ <;> exact_mod_cast this
    have hu : IsUnit P.hessian.det := isUnit_iff_exists_inv.mpr ⟨Cz.det, by rw [← det_mul, hmul', det_one]⟩
    have hpos : (0 : ℚ) < (P.hessian.det : ℚ) := by
      have := RingHom.map_det (algebraMap ℤ ℚ) P.hessian
      simp only [RingHom.mapMatrix_apply] at this
      rw [show ((P.hessian.det : ℤ) : ℚ) = algebraMap ℤ ℚ P.hessian.det from rfl, this]
      show (0 : ℚ) < Pq.det
      rw [hdetP]; positivity
    rcases Int.isUnit_iff.mp hu with h | h
    · exact h
    · rw [h] at hpos; norm_num at hpos

/-- **$\mathrm{vois}_d(L; u)$ is an even unimodular lattice** (Chenevier–Lannes, Proposition 3.1.4, p. 47, for $L$
even unimodular): for $d \ge 1$, $q(u) \equiv 0 \bmod d$ and $u \cdot v \equiv 1 \bmod d$, $\mathrm{vois}_d(L; u) =
g\,\mathbb{Z}^n$ with $\det g \ne 0$ and its form $P$ in this basis is even unimodular. Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 3.1.4, p. 47 (vois_d(L; u) is even unimodular)"]
theorem voisLat_isEvenUnimodular {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {d : ℕ} (hd : 1 ≤ d)
    {u v : Fin n → ℤ} (hq : (d : ℤ) ∣ Q.eval u) (hv : (d : ℤ) ∣ bZ Q u v - 1) :
    ∃ (g : Matrix (Fin n) (Fin n) ℚ) (P : QuadForm ℤ n), g.det ≠ 0 ∧ imgLat g = voisLat Q d u v ∧
      (∀ x, P.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) ∧ IsEvenUnimodular P := by
  have hdet : IsUnit Q.hessian.det := by rw [hQ.det_one]; exact isUnit_one
  obtain ⟨g, P, hg, hN, hP, hPe⟩ := isEvenUnimodular_of_isDNeighbor hQ hd (isDNeighbor_voisLat hdet hd hq hv)
  exact ⟨g, P, hg, hN.symm, hP, hPe⟩

end QuadFormsKB.ChenevierLannes
