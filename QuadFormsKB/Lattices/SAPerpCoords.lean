/-
# Coordinates on the orthogonal complement of a vector, and lattices on it (O'Meara 104:3 step 3)

**Layer:** $V = F^{m+1}$ with `Q : QuadForm F (m+1)` nondegenerate over a number field $F$, an anisotropic $v_0 \in V$,
its orthogonal complement $U = v_0^\perp$, and lattices in $F^m$ (`Lat F m`).

**Proves**
* `exists_perp_coords`: an explicit pair $M \in M_{(m+1)\times m}(F)$, $N \in M_{m \times (m+1)}(F)$ with $NM = 1$, $N$ a
  coordinate projection, $M$ a basis of $v_0^\perp$ over every extension field ($B(v_0, My) = 0$, and $MNx = x$ when
  $B(v_0, x) = 0$), and the pulled-back form $R(y) = Q(My)$ nondegenerate;
* `exists_lat_comap`: the lattice $K \subseteq F^m$ with $K_\mathfrak p = \{y : My \in \mathfrak p^{k_\mathfrak p}\mathfrak o_\mathfrak p^{m+1}\}$
  ($k_\mathfrak p = 0$ off a finite set), O'Meara's lattice "$K$ on $U$" of step 3 (via 81:14) in coordinates;
* `exists_primitive`: a nonzero local vector has a primitive scalar multiple.
-/
import QuadFormsKB.Lattices.SALocalRep

open NumberField IsDedekindDomain Matrix Topology WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {m : ℕ}

theorem qbil_eq_polar {n : ℕ} (Q : QuadForm F n) (K : Type*) [Field K] [Algebra F K] (x y : Fin n → K) :
    qbil Q K x y = Q.evalIn K (x + y) - Q.evalIn K x - Q.evalIn K y := by
  rw [QuadForm.polar_eq_hessian]; rfl

theorem qbil_pullback {n : ℕ} (Q : QuadForm F n) (Mb : Matrix (Fin n) (Fin m) F) (K : Type*) [Field K] [Algebra F K]
    (x y : Fin m → K) :
    qbil (pullbackForm Q Mb) K x y = qbil Q K (Mb.map (algebraMap F K) *ᵥ x) (Mb.map (algebraMap F K) *ᵥ y) := by
  rw [qbil_eq_polar, qbil_eq_polar, evalIn_pullback, evalIn_pullback, evalIn_pullback, mulVec_add]

theorem qbil_eq_dot {n : ℕ} (Q : QuadForm F n) (K : Type*) [Field K] [Algebra F K] (v₀ : Fin n → F)
    (x : Fin n → K) :
    qbil Q K (fun i => algebraMap F K (v₀ i)) x = (fun i => algebraMap F K ((Q.hessian *ᵥ v₀) i)) ⬝ᵥ x := by
  rw [qbil, dotProduct_mulVec, ← mulVec_transpose, ← transpose_map,
    show Q.hessianᵀ = Q.hessian by ext i j; simp [QuadForm.hessian, add_comm]]
  congr 1
  funext i
  simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

/-- **Coordinates on $v_0^\perp$.** See the module docstring. -/
theorem exists_perp_coords (Q : QuadForm F (m + 1)) (hQ : Q.Nondegenerate) {v₀ : Fin (m + 1) → F}
    (hv₀ : Q.evalIn F v₀ ≠ 0) :
    ∃ (Mb : Matrix (Fin (m + 1)) (Fin m) F) (Nb : Matrix (Fin m) (Fin (m + 1)) F),
      Nb * Mb = 1 ∧ (∀ i j, Nb i j = 0 ∨ Nb i j = 1) ∧
      (∀ (K : Type) [Field K] [Algebra F K] (y : Fin m → K),
        qbil Q K (fun i => algebraMap F K (v₀ i)) (Mb.map (algebraMap F K) *ᵥ y) = 0) ∧
      (∀ (K : Type) [Field K] [Algebra F K] (x : Fin (m + 1) → K),
        qbil Q K (fun i => algebraMap F K (v₀ i)) x = 0 →
          Mb.map (algebraMap F K) *ᵥ (Nb.map (algebraMap F K) *ᵥ x) = x) ∧
      (pullbackForm Q Mb).Nondegenerate := by
  classical
  set t := Q.hessian *ᵥ v₀
  have ht : t ≠ 0 := by
    intro h0
    apply hv₀
    have h1 := qbil_eq_dot Q F v₀ v₀
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at h1
    have h2 := qbil_self Q F v₀
    rw [show (fun i => v₀ i) = v₀ from rfl] at h1
    rw [h1, show (fun i => (Q.hessian *ᵥ v₀) i) = t from rfl, h0, zero_dotProduct] at h2
    have : (2 : F) ≠ 0 := two_ne_zero
    exact (mul_eq_zero.mp h2.symm).resolve_left this
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp ht
  set Mb : Matrix (Fin (m + 1)) (Fin m) F := LocRep.perpMat t i₀ (t i₀)⁻¹ i₀.succAbove
  set Nb : Matrix (Fin m) (Fin (m + 1)) F := Matrix.of fun j i => if i = i₀.succAbove j then 1 else 0
  have hMmap : ∀ (K : Type) [Field K] [Algebra F K], Mb.map (algebraMap F K) =
      LocRep.perpMat (fun i => algebraMap F K (t i)) i₀ (algebraMap F K (t i₀)⁻¹) i₀.succAbove := by
    intro K _ _
    ext i j
    simp only [Mb, LocRep.perpMat, Matrix.map_apply, Matrix.of_apply, map_add]
    split_ifs <;> simp
  have hdot : ∀ (K : Type) [Field K] [Algebra F K] (y : Fin m → K),
      (fun i => algebraMap F K (t i)) ⬝ᵥ (Mb.map (algebraMap F K) *ᵥ y) = 0 := by
    intro K _ _ y
    rw [hMmap, dotProduct_mulVec, LocRep.vecMul_perpMat _ (by rw [← map_mul, mul_inv_cancel₀ hi₀, map_one]) i₀.succAbove
      (fun j => Fin.succAbove_ne i₀ j), zero_dotProduct]
  have hNM : Nb * Mb = 1 := by
    ext j j'
    simp only [Nb, Mb, LocRep.perpMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [ite_eq_right_iff.mpr fun h => absurd h (Fin.succAbove_ne i₀ j)]
    simp [Fin.succAbove_right_inj, eq_comm]
  have hMN : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin (m + 1) → K),
      qbil Q K (fun i => algebraMap F K (v₀ i)) x = 0 →
        Mb.map (algebraMap F K) *ᵥ (Nb.map (algebraMap F K) *ᵥ x) = x := by
    intro K _ _ x hx
    rw [qbil_eq_dot] at hx
    have hN : Nb.map (algebraMap F K) *ᵥ x = fun j => x (i₀.succAbove j) := by
      funext j
      simp only [Nb, mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, apply_ite (algebraMap F K), map_one,
        map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hN, hMmap]
    funext i
    by_cases hi : i = i₀
    · rw [hi]
      rw [LocRep.perpMat_mulVec_self]
      rw [dotProduct, Fin.sum_univ_succAbove _ i₀] at hx
      have h1 : algebraMap F K (t i₀) ≠ 0 := (map_ne_zero _).mpr hi₀
      have h2 : algebraMap F K (t i₀)⁻¹ * algebraMap F K (t i₀) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hi₀, map_one]
      have : ∑ j, -algebraMap F K (t (i₀.succAbove j)) * algebraMap F K (t i₀)⁻¹ * x (i₀.succAbove j) =
          -algebraMap F K (t i₀)⁻¹ * ∑ j, algebraMap F K (t (i₀.succAbove j)) * x (i₀.succAbove j) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      linear_combination (-algebraMap F K (t i₀)⁻¹) * hx + x i₀ * h2
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      exact LocRep.perpMat_mulVec_succAbove _ _ _ _ j
  have hperp : ∀ (K : Type) [Field K] [Algebra F K] (y : Fin m → K),
      qbil Q K (fun i => algebraMap F K (v₀ i)) (Mb.map (algebraMap F K) *ᵥ y) = 0 := fun K _ _ y => by
    rw [qbil_eq_dot]; exact hdot K y
  refine ⟨Mb, Nb, hNM, fun i j => by simp only [Nb, Matrix.of_apply]; split_ifs <;> simp, hperp, hMN, ?_⟩
  have hidM : Mb.map (algebraMap F F) = Mb := by ext i j; simp
  have hidN : Nb.map (algebraMap F F) = Nb := by ext i j; simp
  have hv : (fun i => algebraMap F F (v₀ i)) = v₀ := by funext i; simp
  by_contra hdeg
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (not_not.mp hdeg)
  have hR : ∀ y', qbil Q F (Mb *ᵥ y') (Mb *ᵥ y) = 0 := by
    intro y'
    have := qbil_pullback Q Mb F y' y
    rw [hidM] at this
    rw [← this, qbil]
    simp [hy]
  have hMy : Mb *ᵥ y = 0 := by
    refine eq_zero_of_qbil_eq_zero hQ fun x => ?_
    have hvv : qbil Q F v₀ v₀ ≠ 0 := by rw [qbil_self]; exact mul_ne_zero two_ne_zero hv₀
    set c := qbil Q F v₀ x / qbil Q F v₀ v₀
    have hx' : qbil Q F v₀ (x - c • v₀) = 0 := by
      rw [sub_eq_add_neg, ← neg_smul, qbil_add_right, qbil_smul_right]
      simp only [c]; field_simp; ring
    have h1 := hMN F (x - c • v₀) (by rw [hv]; exact hx')
    rw [hidM, hidN] at h1
    have h2 := hperp F y
    rw [hv, hidM] at h2
    have : x = (x - c • v₀) + c • v₀ := by abel
    rw [this, qbil_add_right, qbil_smul_right, ← h1, qbil_comm Q F (Mb *ᵥ y) (Mb *ᵥ (Nb *ᵥ (x - c • v₀))), hR,
      qbil_comm Q F (Mb *ᵥ y) v₀, h2, mul_zero, add_zero]
  apply hy0
  rw [← one_mulVec y, ← hNM, ← mulVec_mulVec, hMy, mulVec_zero]

/-! ### Local lattices defined by a matrix, and the glued lattice -/

theorem mulVec_mem_ball_rect {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {A : Matrix (Fin n) (Fin m) (v.adicCompletion F)} {k k' : ℤ} (hA : ∀ i j, Valued.v (A i j) ≤ exp (-k))
    {y : Fin m → v.adicCompletion F} (hy : y ∈ ball v k') : A *ᵥ y ∈ ball v (k + k') := by
  intro i
  rw [mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, neg_add, exp_add]
  exact mul_le_mul' (hA i j) (hy j)

/-- **The lattice $\{y : My \in \mathfrak p^{k_\mathfrak p}\mathfrak o_\mathfrak p^n\ \forall \mathfrak p\}$** ($k_\mathfrak p = 0$ off $T$), for
$NM = 1$ with $N$ a $0/1$ matrix. -/
theorem exists_lat_comap {n : ℕ} (Mb : Matrix (Fin n) (Fin m) F) (Nb : Matrix (Fin m) (Fin n) F) (hNM : Nb * Mb = 1)
    (hN01 : ∀ i j, Nb i j = 0 ∨ Nb i j = 1) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (r : HeightOneSpectrum (𝓞 F) → ℤ) (hr : ∀ v ∉ T, r v = 0) :
    ∃ K : Lat F m, ∀ v (y : Fin m → v.adicCompletion F), y ∈ loc v K.1 ↔
      Mb.map (algebraMap F (v.adicCompletion F)) *ᵥ y ∈ ball v (r v) := by
  classical
  have hNv : ∀ v : HeightOneSpectrum (𝓞 F), ∀ i j,
      Valued.v ((Nb.map (algebraMap F (v.adicCompletion F))) i j) ≤ exp (-(0 : ℤ)) := by
    intro v i j
    rw [Matrix.map_apply, neg_zero, exp_zero]
    rcases hN01 i j with h | h <;> simp [h]
  have hNMv : ∀ v : HeightOneSpectrum (𝓞 F), ∀ y : Fin m → v.adicCompletion F,
      Nb.map (algebraMap F (v.adicCompletion F)) *ᵥ (Mb.map (algebraMap F (v.adicCompletion F)) *ᵥ y) = y := by
    intro v y
    rw [mulVec_mulVec, ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]
  let Mv : ∀ v : HeightOneSpectrum (𝓞 F), Submodule (v.adicCompletionIntegers F) (Fin m → v.adicCompletion F) :=
    fun v => Submodule.comap ((Matrix.mulVecLin (Mb.map (algebraMap F (v.adicCompletion F)))).restrictScalars _)
      (ball v (r v))
  have hmem : ∀ v y, y ∈ Mv v ↔ Mb.map (algebraMap F (v.adicCompletion F)) *ᵥ y ∈ ball v (r v) := fun v y => Iff.rfl
  have hup : ∀ v, Mv v ≤ ball v (r v) := by
    intro v y hy
    rw [hmem] at hy
    have := mulVec_mem_ball_rect (hNv v) hy
    rwa [hNMv, zero_add] at this
  have hlat : ∀ v, (Mv v).IsLattice (v.adicCompletion F) := by
    intro v
    choose kM hkM using fun i j => exists_valued_le v ((Mb.map (algebraMap F (v.adicCompletion F))) i j)
    set c : ℤ := ∑ i, ∑ j, (kM i j : ℤ)
    have hc : ∀ i j, Valued.v ((Mb.map (algebraMap F (v.adicCompletion F))) i j) ≤ exp (-(-c)) := by
      intro i j
      rw [neg_neg]
      refine (hkM i j).trans (exp_le_exp.mpr ?_)
      have h1 : (kM i j : ℤ) ≤ ∑ j, (kM i j : ℤ) :=
        Finset.single_le_sum (f := fun j => (kM i j : ℤ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ j)
      have h2 : ∑ j, (kM i j : ℤ) ≤ c :=
        Finset.single_le_sum (f := fun i => ∑ j, (kM i j : ℤ)) (fun _ _ => Finset.sum_nonneg fun _ _ =>
          Nat.cast_nonneg _) (Finset.mem_univ i)
      omega
    refine isLattice_of_bounds v (k := r v + c) (k' := r v) (fun y hy => ?_) (hup v)
    rw [hmem]
    have := mulVec_mem_ball_rect hc hy
    rwa [show -c + (r v + c) = r v by ring] at this
  have hev : ∀ᶠ v in Filter.cofinite, Mv v = std v := by
    have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        ∀ i j, Valued.v ((Mb.map (algebraMap F (v.adicCompletion F))) i j) ≤ 1 := by
      have := Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
        eventually_valuation_le_one (F := F) (Mb i j)
      filter_upwards [this] with v hv i j
      rw [Matrix.map_apply, valued_algebraMap]; exact hv i j
    have hT : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v ∉ T := T.finite_toSet.compl_mem_cofinite
    filter_upwards [hint, hT] with v hv hvT
    have hr0 : r v = 0 := hr v hvT
    refine le_antisymm (by have := hup v; rwa [hr0] at this) fun y hy => ?_
    rw [hmem, hr0]
    have := mulVec_mem_ball_rect (k := 0) (fun i j => by rw [neg_zero, exp_zero]; exact hv i j) hy
    rwa [zero_add] at this
  let fam : LocFamily F m := ⟨Mv, hlat, hev⟩
  exact ⟨⟨fam.glue, fam.glue_isLattice⟩, fun v y => by
    change y ∈ loc v fam.glue ↔ _
    rw [fam.loc_glue v]; exact hmem v y⟩

/-- **A primitive multiple** of a nonzero local vector. -/
theorem exists_primitive {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {x : Fin n → v.adicCompletion F} (hx : x ≠ 0) :
    ∃ c : v.adicCompletion F, c ≠ 0 ∧ c • x ∈ std v ∧ ∃ i, Valued.v ((c • x) i) = 1 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (x i)) ⟨j, Finset.mem_univ j⟩
  have hxi : x i ≠ 0 := by
    intro h0
    have := hi j (Finset.mem_univ j)
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hj this
  refine ⟨(x i)⁻¹, inv_ne_zero hxi, fun k => ?_, i, ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, neg_zero, exp_zero]
    rw [inv_mul_le_iff₀ ((Valuation.pos_iff _).mpr hxi), mul_one]
    exact hi k (Finset.mem_univ k)
  · rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hxi, map_one]

end QuadFormsKB.Lattices
