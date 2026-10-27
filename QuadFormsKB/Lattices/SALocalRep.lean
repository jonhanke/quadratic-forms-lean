/-
# Local representation by orthogonal complements at good primes (O'Meara 104:3 step 3)

**Layer:** a complete non-dyadic DVR $R$ with finite residue field (for the application $R = \mathfrak o_\mathfrak p$),
diagonal unimodular forms $\langle a_0, \dots, a_{n-1}\rangle$ ($a_i \in R^\times$) and linear conditions $t \cdot z = 0$.

**Proves** the local facts used in step 3 of O'Meara 1973, 104:3 (p. 313):
* `exists_eval_eq_dvr`: a unimodular form in $m \ge 3$ variables represents every $c \in R$ (O'Meara 92:1b);
* `exists_perp_eval_eq_unit`: if $n \ge 4$ and some $t_k$ is a unit, every unit is $\sum a_i z_i^2$ with $t\cdot z = 0$
  (the role of O'Meara's 82:15/82:17 binary unimodular sublattice);
* `exists_perp_eval_eq`: if moreover $\sum_i t_i^2/a_i$ is a unit, every $c \in R$ is $\sum a_i z_i^2$ with $t \cdot z = 0$
  (the complement of a unit-norm vector is unimodular, O'Meara 92:1b).

*Method (a simplification of O'Meara's sublattice arguments).* For a set $J$ of
indices not containing $k$, the vectors supported on $J \cup \{k\}$ with $t \cdot z = 0$ form a free module with basis
indexed by $J$, on which the form is $\langle a_j\rangle_{j \in J} + a_k (\sum_J t_j y_j / t_k)^2$; by the matrix determinant
lemma its Hessian determinant is a unit times $\sigma_J = t_k^2/a_k + \sum_J t_j^2/a_j$. Among three indices $j_0, j_1, j_2
\ne k$ one of $\sigma_{\{j_0,j_1\}}, \sigma_{\{j_0,j_2\}}, \sigma_{\{j_1,j_2\}}, \sigma_{\{j_0,j_1,j_2\}}$ is a unit.
-/
import QuadFormsKB.Lattices.SAVectorsIsotropic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices.LocRep

open QuadFormsKB.Siegel.Kneser

section Ring

variable {R : Type*} [CommRing R] {n m : ℕ}

/-- **The pull-back of a form along a matrix** $L \in M_{n\times m}(R)$: $y \mapsto Q_0(Ly)$ (any commutative ring). -/
def pullR (Q₀ : QuadForm R n) (L : Matrix (Fin n) (Fin m) R) : QuadForm R m :=
  QuadForm.ofUpper fun i j =>
    if i = j then (Lᵀ * Q₀.coeff * L) i i else (Lᵀ * Q₀.coeff * L) i j + (Lᵀ * Q₀.coeff * L) j i

theorem eval_pullR (Q₀ : QuadForm R n) (L : Matrix (Fin n) (Fin m) R) (y : Fin m → R) :
    (pullR Q₀ L).eval y = Q₀.eval (L *ᵥ y) := by
  rw [QuadForm.eval, pullR, evalIn_ofUpper_symm, QuadForm.eval, QuadForm.evalIn_eq_dotProduct]
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem hessian_ofUpper_symm (A : Matrix (Fin m) (Fin m) R) :
    (QuadForm.ofUpper fun i j => if i = j then A i i else A i j + A j i).hessian = A + Aᵀ := by
  ext i j
  simp only [QuadForm.hessian, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h.le, not_le.mpr h, h.ne]
  · simp
  · simp [h.le, not_le.mpr h, h.ne]; ring

/-- **Matrix determinant lemma** for a diagonal matrix of units plus a symmetric rank-one term. -/
theorem det_diagonal_add_vecMulVec (b : Fin m → R) (hb : ∀ i, IsUnit (b i)) (s : R) (w : Fin m → R) :
    (diagonal b + s • vecMulVec w w).det =
      (∏ i, b i) * (1 + s * ∑ i, w i ^ 2 * ↑((hb i).unit⁻¹)) := by
  set x : Fin m → R := fun i => s * w i * ↑((hb i).unit⁻¹)
  have e : diagonal b + s • vecMulVec w w = diagonal b * (1 + replicateCol Unit x * replicateRow Unit w) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← vecMulVec_eq]
    congr 1
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, diagonal_mul, x]
    have : b i * ↑((hb i).unit⁻¹) = 1 := (hb i).mul_val_inv
    linear_combination (-(s * w i * w j)) * this
  rw [e, det_mul, det_diagonal, det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct, x, Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => by ring)

/-! ### Complements of a linear condition in a diagonal unimodular form -/

/-- **The parametrization of $\{z : t\cdot z = 0,\ \operatorname{supp} z \subseteq J \cup \{k\}\}$:** $y \mapsto z$ with
$z_{J(j)} = y_j$, $z_k = -t_k^{-1}\sum_j t_{J(j)}y_j$. ($t_k' = t_k^{-1}$.) -/
def perpMat {m : ℕ} (t : Fin n → R) (k : Fin n) (tk' : R) (J : Fin m → Fin n) : Matrix (Fin n) (Fin m) R :=
  Matrix.of fun i j => (if i = J j then (1 : R) else 0) + (if i = k then -(t (J j)) * tk' else 0)

theorem vecMul_perpMat {m : ℕ} (t : Fin n → R) {k : Fin n} {tk' : R} (htk : t k * tk' = 1)
    (J : Fin m → Fin n) (hJk : ∀ j, J j ≠ k) : t ᵥ* perpMat t k tk' J = 0 := by
  funext j
  simp only [vecMul, dotProduct, perpMat, Matrix.of_apply, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply]
  linear_combination (-(t (J j))) * htk

theorem perpMat_gram {m : ℕ} (a t : Fin n → R) (k : Fin n) (tk' : R) (J : Fin m → Fin n)
    (hJ : Function.Injective J) (hJk : ∀ j, J j ≠ k) :
    (perpMat t k tk' J)ᵀ * diagonal a * perpMat t k tk' J =
      diagonal (fun j => a (J j)) + a k • vecMulVec (fun j => -(t (J j)) * tk') (fun j => -(t (J j)) * tk') := by
  ext j j'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, diagonal_apply, perpMat, Matrix.of_apply, 
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, add_mul, mul_add, Finset.sum_add_distrib,
    one_mul, Finset.sum_ite_eq]
  by_cases hjj : j = j'
  · subst hjj; simp [hJk j, Ne.symm (hJk j)]; ring
  · have : J j ≠ J j' := hJ.ne hjj
    simp [hjj, this, Ne.symm this, hJk j, hJk j', Ne.symm (hJk j), Ne.symm (hJk j')]; ring

theorem perpMat_mulVec_succAbove {m : ℕ} (t : Fin (m + 1) → R) (k : Fin (m + 1)) (tk' : R) (y : Fin m → R)
    (j₀ : Fin m) : (perpMat t k tk' k.succAbove *ᵥ y) (k.succAbove j₀) = y j₀ := by
  simp only [perpMat, mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Fin.succAbove_right_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Fin.succAbove_ne,
    ite_false, Finset.sum_const_zero, add_zero]

theorem perpMat_mulVec_self {m : ℕ} (t : Fin (m + 1) → R) (k : Fin (m + 1)) (tk' : R) (y : Fin m → R) :
    (perpMat t k tk' k.succAbove *ᵥ y) k = ∑ j, -t (k.succAbove j) * tk' * y j := by
  simp only [perpMat, mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, ite_true]
  rw [Finset.sum_eq_zero fun j _ => if_neg (Fin.succAbove_ne k j).symm, zero_add]

end Ring

section DVR

open QuadFormsKB.LocalDensity

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

variable {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
include hπ h2

theorem not_dvd_of_isUnit {x : R} (hx : IsUnit x) : ¬ π ∣ x := fun h =>
  hπ.not_isUnit (isUnit_of_dvd_unit h hx)

/-- **A unimodular form in $m \ge 3$ variables represents every element** of $R$ (O'Meara 1963, 92:1b, p. 247, there over a non-dyadic local field):
units by `exists_eval_eq_unit_dvr`; for $c \in \pi R$ solve $a_0x_0^2 + a_1x_1^2 = c - a_2$ (a unit) and take $x_2 = 1$. -/
@[kb "omeara1963" "§92, 92:1b, p. 247 (a unimodular lattice represents every unit); §104, proof of 104:3, step 3, p. 313"]
theorem exists_eval_eq_dvr {m : ℕ} (Q₀ : QuadForm R m) (hdet : ¬ π ∣ Q₀.hessian.det) (hm : 3 ≤ m) (c : R) :
    ∃ x, Q₀.eval x = c := by
  by_cases hc : IsUnit c
  · exact exists_eval_eq_unit_dvr hπ h2 Q₀ hdet (by omega) hc
  obtain ⟨a, ha, ⟨U, -, hU⟩, -⟩ := DVR.exists_diag_of_unimodular Q₀ π hπ h2 hdet
  have haU : ∀ i, IsUnit (a i) := fun i => DVR.isUnit_of_not_dvd _ hπ _ (ha i)
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let i2 : Fin m := ⟨2, by omega⟩
  have hcm : c ∈ IsLocalRing.maximalIdeal R := hc
  have hd : IsUnit (c - a i2) := by
    by_contra h
    have h' : c - a i2 ∈ IsLocalRing.maximalIdeal R := h
    have : a i2 ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hcm h'; simpa using this
    exact this (haU i2)
  obtain ⟨s, t, hst⟩ := Nbr.exists_binary_one_dvr hπ h2 ((haU i0).mul hd.unit⁻¹.isUnit)
    ((haU i1).mul hd.unit⁻¹.isUnit)
  let z : Fin m → R := Pi.single i0 s + Pi.single i1 t + Pi.single i2 1
  refine ⟨U *ᵥ z, ?_⟩
  rw [← hU, eval_diag]
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hz : ∀ i, a i * z i ^ 2 = (if i = i0 then a i0 * s ^ 2 else 0) + (if i = i1 then a i1 * t ^ 2 else 0) +
      (if i = i2 then a i2 else 0) := by
    intro i
    by_cases e0 : i = i0
    · subst e0; simp [z, h01, h02]
    · by_cases e1 : i = i1
      · subst e1; simp [z, e0, h12]
      · by_cases e2 : i = i2
        · subst e2; simp [z, e0, e1]
        · simp [z, e0, e1, e2]
  rw [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have hinv : (↑hd.unit⁻¹ : R) * (c - a i2) = 1 := hd.val_inv_mul
  have := congrArg (· * (c - a i2)) hst
  simp only [one_mul] at this
  linear_combination this - (a i0 * s ^ 2 + a i1 * t ^ 2) * hinv

/-- **The complement form is unimodular** when $\sigma_J = t_k^2/a_k + \sum_J t_{J(j)}^2/a_{J(j)}$ is a unit. -/
theorem not_dvd_det_pullR_perpMat {m : ℕ} (a : Fin n → R) (ha : ∀ i, IsUnit (a i)) (t : Fin n → R) {k : Fin n}
    (htk : IsUnit (t k)) (J : Fin m → Fin n) (hJ : Function.Injective J) (hJk : ∀ j, J j ≠ k)
    (hσ : IsUnit (t k ^ 2 * ↑((ha k).unit⁻¹) + ∑ j, t (J j) ^ 2 * ↑((ha (J j)).unit⁻¹))) :
    ¬ π ∣ (pullR (QuadForm.diag a) (perpMat t k ↑(htk.unit⁻¹) J)).hessian.det := by
  set tk' : R := ↑(htk.unit⁻¹)
  have h1 : t k * tk' = 1 := htk.mul_val_inv
  have h1' : a k * ↑((ha k).unit⁻¹) = 1 := (ha k).mul_val_inv
  rw [pullR, hessian_ofUpper_symm]
  have hcoeff : (QuadForm.diag a).coeff = diagonal a := rfl
  rw [hcoeff, perpMat_gram a t k tk' J hJ hJk]
  set A := diagonal (fun j => a (J j)) + a k • vecMulVec (fun j => -(t (J j)) * tk') (fun j => -(t (J j)) * tk')
  have hAt : Aᵀ = A := by
    simp only [A, transpose_add, diagonal_transpose, transpose_smul, transpose_vecMulVec]
  rw [hAt, ← two_smul R A, det_smul, Fintype.card_fin, det_diagonal_add_vecMulVec _ (fun j => ha (J j))]
  apply not_dvd_of_isUnit hπ h2
  have hp : IsUnit (∏ j, a (J j)) :=
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j _ => ha (J j)
  have e : 1 + a k * ∑ j, (-(t (J j)) * tk') ^ 2 * ↑((ha (J j)).unit⁻¹) =
      (a k * tk' ^ 2) * (t k ^ 2 * ↑((ha k).unit⁻¹) + ∑ j, t (J j) ^ 2 * ↑((ha (J j)).unit⁻¹)) := by
    have : a k * tk' ^ 2 * (t k ^ 2 * ↑((ha k).unit⁻¹)) = 1 := by
      linear_combination (t k * tk' + 1) * a k * ↑((ha k).unit⁻¹) * h1 + h1'
    rw [mul_add, this]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact (IsUnit.pow _ (DVR.isUnit_of_not_dvd _ hπ _ h2)).mul (hp.mul (((ha k).mul
    (htk.unit⁻¹.isUnit.pow 2)).mul hσ))

theorem exists_perp_of_sigma {m : ℕ} (a : Fin n → R) (ha : ∀ i, IsUnit (a i)) (t : Fin n → R) {k : Fin n}
    (htk : IsUnit (t k)) (J : Fin m → Fin n) (hJ : Function.Injective J) (hJk : ∀ j, J j ≠ k)
    (hσ : IsUnit (t k ^ 2 * ↑((ha k).unit⁻¹) + ∑ j, t (J j) ^ 2 * ↑((ha (J j)).unit⁻¹))) {c : R}
    (hc : (2 ≤ m ∧ IsUnit c) ∨ 3 ≤ m) : ∃ z, t ⬝ᵥ z = 0 ∧ (QuadForm.diag a).eval z = c := by
  have hdet := not_dvd_det_pullR_perpMat hπ h2 a ha t htk J hJ hJk hσ
  obtain ⟨y, hy⟩ : ∃ y, (pullR (QuadForm.diag a) (perpMat t k ↑(htk.unit⁻¹) J)).eval y = c := by
    rcases hc with ⟨hm, hu⟩ | hm
    · exact exists_eval_eq_unit_dvr hπ h2 _ hdet hm hu
    · exact exists_eval_eq_dvr hπ h2 _ hdet hm c
  refine ⟨perpMat t k ↑(htk.unit⁻¹) J *ᵥ y, ?_, ?_⟩
  · rw [dotProduct_mulVec, vecMul_perpMat t htk.mul_val_inv J hJk, zero_dotProduct]
  · rw [← eval_pullR]; exact hy

/-- **Every unit is represented by the complement of a primitive linear condition** in a diagonal unimodular form in
$n \ge 4$ variables over a complete non-dyadic DVR. -/
theorem exists_perp_eval_eq_unit (hn : 4 ≤ n) (a : Fin n → R) (ha : ∀ i, IsUnit (a i)) (t : Fin n → R) {k : Fin n}
    (htk : IsUnit (t k)) {u : R} (hu : IsUnit u) : ∃ z, t ⬝ᵥ z = 0 ∧ (QuadForm.diag a).eval z = u := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set r : Fin (m + 1) → R := fun i => t i ^ 2 * ↑((ha i).unit⁻¹)
  have key : ∀ {m' : ℕ} (e : Fin m' → Fin m), Function.Injective e → 2 ≤ m' →
      IsUnit (r k + ∑ j, r (k.succAbove (e j))) → ∃ z, t ⬝ᵥ z = 0 ∧ (QuadForm.diag a).eval z = u :=
    fun e he hm hσ => exists_perp_of_sigma hπ h2 a ha t htk (fun j => k.succAbove (e j))
      (Fin.succAbove_right_injective.comp he) (fun j => Fin.succAbove_ne k (e j)) hσ (Or.inl ⟨hm, hu⟩)
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let i2 : Fin m := ⟨2, by omega⟩
  have inj2 : ∀ x y : Fin m, x ≠ y → Function.Injective ![x, y] := by
    intro x y hxy p q h
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  set p := k.succAbove
  by_cases c01 : IsUnit (r k + r (p i0) + r (p i1))
  · exact key ![i0, i1] (inj2 _ _ h01) le_rfl (by simpa [Fin.sum_univ_two, add_assoc] using c01)
  by_cases c02 : IsUnit (r k + r (p i0) + r (p i2))
  · exact key ![i0, i2] (inj2 _ _ h02) le_rfl (by simpa [Fin.sum_univ_two, add_assoc] using c02)
  by_cases c12 : IsUnit (r k + r (p i1) + r (p i2))
  · exact key ![i1, i2] (inj2 _ _ h12) le_rfl (by simpa [Fin.sum_univ_two, add_assoc] using c12)
  have inj3 : Function.Injective ![i0, i1, i2] := by
    intro p q h
    fin_cases p <;> fin_cases q <;> simp_all [i0, i1, i2, Fin.ext_iff]
  refine key ![i0, i1, i2] inj3 (by norm_num) ?_
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ← add_assoc]
  by_contra c3
  have hs0 : IsUnit (r k) := (htk.pow 2).mul (ha k).unit⁻¹.isUnit
  have M : ∀ x : R, ¬ IsUnit x → x ∈ IsLocalRing.maximalIdeal R := fun x hx => hx
  have m3 := M _ c3
  have m01 := M _ c01
  have m02 := M _ c02
  have m12 := M _ c12
  have r2 : r (p i2) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ m3 m01; convert this using 1; ring
  have r1 : r (p i1) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ m3 m02; convert this using 1; ring
  have r0 : r (p i0) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ m3 m12; convert this using 1; ring
  have : r k ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ (Ideal.sub_mem _ m01 r0) r1; convert this using 1; ring
  exact this hs0

/-- **Every element is represented by the complement of a unit-norm vector:** if $\sum_i t_i^2/a_i$ is a unit (for
$t = $ the Gram image of $x_0$ this is $4Q(x_0)$), $t \cdot z = 0$ and $\sum a_iz_i^2 = c$ is solvable for every $c$
($n \ge 4$). -/
theorem exists_perp_eval_eq (hn : 4 ≤ n) (a : Fin n → R) (ha : ∀ i, IsUnit (a i)) (t : Fin n → R) {k : Fin n}
    (htk : IsUnit (t k)) (hσ : IsUnit (∑ i, t i ^ 2 * ↑((ha i).unit⁻¹))) (c : R) :
    ∃ z, t ⬝ᵥ z = 0 ∧ (QuadForm.diag a).eval z = c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine exists_perp_of_sigma hπ h2 a ha t htk (fun j => k.succAbove j) Fin.succAbove_right_injective
    (fun j => Fin.succAbove_ne k j) ?_ (Or.inr (by omega))
  rwa [Fin.sum_univ_succAbove _ k] at hσ

end DVR

/-! ### Transfer to $F_\mathfrak p$ at a good prime -/

section Transfer

open IsDedekindDomain NumberField WithZero

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {Q : QuadForm F n} {Q₀ : QuadForm (𝓞 F) n} {k : 𝓞 F}
  (hQ₀ : Q₀.map (algebraMap (𝓞 F) F) = (algebraMap (𝓞 F) F k) • Q)

/-- A vector of $\mathfrak o_\mathfrak p^n$ as a vector over $\mathfrak o_\mathfrak p$. -/
def toO {x : Fin n → Fv} (hx : x ∈ std v) : Fin n → 𝔬 := fun i =>
  ⟨x i, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
    have := hx i; rwa [neg_zero, exp_zero] at this)⟩

theorem coe_toO {x : Fin n → Fv} (hx : x ∈ std v) : (fun i => ((toO v hx i : 𝔬) : Fv)) = x := rfl

theorem coe_mem_std (y : Fin n → 𝔬) : (fun i => ((y i : 𝔬) : Fv)) ∈ std v := fun i => by
  rw [neg_zero, exp_zero]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (y i).2

include hQ₀ in
theorem evalIn_coe_model (hk : k ∉ v.asIdeal) (y : Fin n → 𝔬) :
    Q.evalIn Fv (fun i => ((y i : 𝔬) : Fv)) =
      (algebraMap (𝓞 F) Fv k)⁻¹ * (((LocalDensity.NF.Qp v Q₀).eval y : 𝔬) : Fv) := by
  have h1 := Tamagawa.evalIn_coe_o v Q₀ y
  rw [evalIn_model v hQ₀] at h1
  have hk0 : algebraMap (𝓞 F) Fv k ≠ 0 := by
    intro h0; have := valued_k v hQ₀ hk; rw [h0, map_zero] at this; exact zero_ne_one this
  rw [← h1, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]

include hQ₀ in
/-- **Local representation by the orthogonal complement of a vector at a good prime** ($\mathfrak p \nmid 2k\det H(Q_0)$,
$n \ge 4$, $x_0 \in \mathfrak o_\mathfrak p^n$): every unit $c$ is $Q(y)$ with $y \in \mathfrak o_\mathfrak p^n$, $B(x_0, y) = 0$, if
$x_0$ is primitive; every $c \in \mathfrak o_\mathfrak p$ is, if $Q(x_0)$ is a unit. (O'Meara 1973, 104:3 step 3, via 82:15,
82:17, 92:1b; here from the diagonal lemmas above.) -/
@[kb "omeara1963" "§104, proof of 104:3, step 3, p. 313"]
theorem exists_perp_std (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hk : k ∉ v.asIdeal) (hdet : Q₀.hessian.det ∉ v.asIdeal)
    (hn : 4 ≤ n) {x₀ : Fin n → Fv} (hx₀ : x₀ ∈ std v) {c : Fv}
    (hc : ((∃ i, Valued.v (x₀ i) = 1) ∧ Valued.v c = 1) ∨ (Valued.v c ≤ 1 ∧ Valued.v (Q.evalIn Fv x₀) = 1)) :
    ∃ y ∈ std v, qbil Q Fv x₀ y = 0 ∧ Q.evalIn Fv y = c := by
  classical
  have hπ := LocalDensity.NF.irreducible_π v
  have h2' := LocalDensity.NF.π_not_dvd_two v h2
  have hdet' := LocalDensity.NF.π_not_dvd_det v Q₀ hdet
  set Qp := LocalDensity.NF.Qp v Q₀
  obtain ⟨a, ha, ⟨U, hU1, hU⟩, -⟩ := LocalDensity.DVR.exists_diag_of_unimodular Qp _ hπ h2' hdet'
  have haU : ∀ i, IsUnit (a i) := fun i => LocalDensity.DVR.isUnit_of_not_dvd _ hπ _ (ha i)
  set x₀' := toO v hx₀
  set w := U⁻¹ *ᵥ x₀'
  have hUw : U *ᵥ w = x₀' := by rw [mulVec_mulVec, mul_nonsing_inv _ hU1, one_mulVec]
  have hk1 := valued_k v hQ₀ hk
  have hk0 : algebraMap (𝓞 F) Fv k ≠ 0 := fun h0 => by rw [h0, map_zero] at hk1; exact zero_ne_one hk1
  have hev : ∀ y : Fin n → 𝔬, Q.evalIn Fv (fun i => ((y i : 𝔬) : Fv)) =
      (algebraMap (𝓞 F) Fv k)⁻¹ * (((QuadForm.diag a).eval (U⁻¹ *ᵥ y) : 𝔬) : Fv) := by
    intro y
    rw [evalIn_coe_model v hQ₀ hk, hU, mulVec_mulVec, mul_nonsing_inv _ hU1, one_mulVec]
  -- `w` is primitive
  have hM : ∀ x : 𝔬, ¬ IsUnit x → x ∈ IsLocalRing.maximalIdeal 𝔬 := fun x hx => hx
  obtain ⟨kk, hkk⟩ : ∃ kk, IsUnit (w kk) := by
    by_contra hcon
    push Not at hcon
    have hw : ∀ j, w j ∈ IsLocalRing.maximalIdeal 𝔬 := fun j => hM _ (hcon j)
    rcases hc with ⟨⟨i, hi⟩, -⟩ | ⟨-, hq⟩
    · have hx : x₀' i ∈ IsLocalRing.maximalIdeal 𝔬 := by
        rw [← hUw, mulVec, dotProduct]
        exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hw j)
      apply hx
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact hi
    · have hD : (QuadForm.diag a).eval w ∈ IsLocalRing.maximalIdeal 𝔬 := by
        rw [eval_diag]
        exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (by
          rw [pow_two]; exact Ideal.mul_mem_left _ _ (hw j))
      apply hD
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have := hev x₀'
      rw [show U⁻¹ *ᵥ x₀' = w from rfl, coe_toO] at this
      rw [eq_inv_mul_iff_mul_eq₀ hk0] at this
      change Valued.v (((QuadForm.diag a).eval w : 𝔬) : Fv) = 1
      rw [← this, map_mul, hk1, hq, one_mul]
  have h2u : IsUnit (2 : 𝔬) := LocalDensity.DVR.isUnit_of_not_dvd _ hπ _ h2'
  set t : Fin n → 𝔬 := fun i => 2 * a i * w i
  have htk : IsUnit (t kk) := (h2u.mul (haU kk)).mul hkk
  -- the target `k c` in `𝔬`
  have hkc : Valued.v (algebraMap (𝓞 F) Fv k * c) ≤ 1 := by
    rw [map_mul, hk1, one_mul]
    rcases hc with ⟨-, h⟩ | ⟨h, -⟩
    · exact h.le
    · exact h
  set c' : 𝔬 := ⟨algebraMap (𝓞 F) Fv k * c, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hkc⟩
  obtain ⟨z, hz, hzc⟩ : ∃ z, t ⬝ᵥ z = 0 ∧ (QuadForm.diag a).eval z = c' := by
    rcases hc with ⟨-, h⟩ | ⟨-, hq⟩
    · refine exists_perp_eval_eq_unit hπ h2' hn a haU t htk ?_
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      change Valued.v (algebraMap (𝓞 F) Fv k * c) = 1
      rw [map_mul, hk1, h, one_mul]
    · refine exists_perp_eval_eq hπ h2' hn a haU t htk ?_ c'
      have e : ∑ i, t i ^ 2 * ↑((haU i).unit⁻¹) = 4 * (QuadForm.diag a).eval w := by
        rw [eval_diag, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have : a i * ↑((haU i).unit⁻¹) = 1 := (haU i).mul_val_inv
        simp only [t]
        linear_combination (4 * a i * w i ^ 2) * this
      rw [e]
      refine (show IsUnit (4 : 𝔬) by convert h2u.mul h2u using 1; norm_num).mul ?_
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have := hev x₀'
      rw [show U⁻¹ *ᵥ x₀' = w from rfl, coe_toO, eq_inv_mul_iff_mul_eq₀ hk0] at this
      change Valued.v (((QuadForm.diag a).eval w : 𝔬) : Fv) = 1
      rw [← this, map_mul, hk1, hq, one_mul]
  refine ⟨fun i => ((U *ᵥ z) i : Fv), coe_mem_std v _, ?_, ?_⟩
  · have hpol := QuadForm.polar_eq_hessian Fv Q x₀ (fun i => ((U *ᵥ z) i : Fv))
    rw [qbil, ← hpol]
    have hsum : x₀ + (fun i => (((U *ᵥ z) i : 𝔬) : Fv)) = fun i => (((U *ᵥ (w + z)) i : 𝔬) : Fv) := by
      rw [← coe_toO v hx₀, mulVec_add, hUw]; funext i; simp [x₀']
    rw [hsum, hev, hev, ← coe_toO v hx₀, hev]
    simp only [mulVec_mulVec, nonsing_inv_mul _ hU1, one_mulVec, show U⁻¹ *ᵥ x₀' = w from rfl]
    rw [← mul_sub, ← mul_sub, mul_eq_zero]
    right
    have : (QuadForm.diag a).eval (w + z) - (QuadForm.diag a).eval w - (QuadForm.diag a).eval z = t ⬝ᵥ z := by
      simp only [eval_diag, dotProduct, t, ← Finset.sum_sub_distrib, Pi.add_apply]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h3 := congrArg (fun x : 𝔬 => (x : Fv)) (this.trans hz)
    push_cast at h3
    exact h3
  · rw [hev, mulVec_mulVec, nonsing_inv_mul _ hU1, one_mulVec, hzc]
    change (algebraMap (𝓞 F) Fv k)⁻¹ * (algebraMap (𝓞 F) Fv k * c) = c
    rw [← mul_assoc, inv_mul_cancel₀ hk0, one_mul]

end Transfer

end QuadFormsKB.Lattices.LocRep
