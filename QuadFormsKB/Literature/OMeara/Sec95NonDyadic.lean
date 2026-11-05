/-
# O'Meara 95:1 (iii) and 95:1a: the exceptional case over a non-dyadic field

**Setting.** $R$ is a complete discrete valuation ring (O'Meara's $\mathfrak o$; `IsAdicComplete`) with finite residue
field and fraction field $F$, non-dyadic ($2 \in R^\times$); $(V, Q)$ is an anisotropic quaternary quadratic space
over $F$ (the exceptional case of O'Meara's 95:1, 1973 printing, p. 280). $\pi$ is any prime element and $\Delta$ any
unit of $R$ which is not a square; $\tau_{(\alpha)}$ is a symmetry $\tau_x$ with $Q(x) = \alpha$.

**Proves**
* `S95.symProd_not_mem_omega` (step 4 of the proof, p. 282–283): $\tau_{(1)}\tau_{(\Delta)}\tau_{(\pi)}
  \tau_{(\pi\Delta)} \notin \Omega_4(V)$, for every choice of the vectors;
* `S95.symProd_mem_orthPrime`: that element lies in $O'_4(V)$;
* `S95.omega_cosets_nondyadic` (**Corollary 95:1a**, p. 283): $\Omega_4$ and
  $\tau_{(1)}\tau_{(\Delta)}\tau_{(\pi)}\tau_{(\pi\Delta)}\Omega_4$ are the two distinct cosets of $O'_4$ modulo
  $\Omega_4$;
* `S95.relIndex_omega_orthPrime_nondyadic` (**95:1, the exceptional case**, pp. 280–283):
  $(O'_4 : \Omega_4) = 2$.
-/
import QuadFormsKB.Literature.OMeara.Sec95Classes
import QuadFormsKB.Literature.OMeara.Sec95Coord
import QuadFormsKB.Literature.OMeara.Sec95Reduce
import QuadFormsKB.Literature.OMeara.Sec95Step3

open QuadraticMap Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open Cl54

namespace S95

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- An anisotropic space is regular. -/
theorem nondegenerate_of_anisotropic (hQ : Q.Anisotropic) : (QuadraticMap.associated Q).Nondegenerate :=
  cd_nondeg_of_reg Q fun x hx => hQ x (by rw [← bil_self]; exact hx x)

variable {Q}

/-- The coordinate facts of `Sec95Coord.lean`, bundled for the reduction homomorphism. -/
theorem NormalBasis.redData (h2 : IsUnit (2 : R)) {π : R} (hπ : Irreducible π) (hQ : Q.Anisotropic)
    (N : NormalBasis Q π) : N.RedData :=
  ⟨fun _ _ hz i => N.integral h2 hπ hQ hz i, fun _ _ hz i hi => N.mem_pi h2 hπ hQ hz i hi, hπ⟩

/-- A binary unimodular form $\langle a, b\rangle$ represents every unit $\delta$ over $\mathfrak o$ (92:1b). -/
theorem exists_binary_eq (h2 : IsUnit (2 : R)) {a b δ : R} (ha : IsUnit a) (hb : IsUnit b) (hδ : IsUnit δ) :
    ∃ s t : R, a * s ^ 2 + b * t ^ 2 = δ := by
  have hw : δ * ↑hδ.unit⁻¹ = 1 := hδ.mul_val_inv
  have hwu : IsUnit (↑hδ.unit⁻¹ : R) := (hδ.unit⁻¹).isUnit
  obtain ⟨s, t, hst⟩ := exists_binary_one (F := FractionRing R) h2 (ha.mul hwu) (hb.mul hwu)
  exact ⟨s, t, by linear_combination δ * hst + (-(a * s ^ 2) - b * t ^ 2) * hw⟩

theorem NormalBasis.exists_vec01 (h2 : IsUnit (2 : R)) {π : R} (N : NormalBasis Q π) {δ : R} (hδ : IsUnit δ) :
    ∃ c : Fin 4 → R, c 2 = 0 ∧ c 3 = 0 ∧ N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2 = δ := by
  obtain ⟨s, t, hst⟩ := exists_binary_eq h2 (N.unit 0) (N.unit 1) hδ
  exact ⟨![s, t, 0, 0], rfl, rfl, by simpa using hst⟩

theorem NormalBasis.exists_vec23 (h2 : IsUnit (2 : R)) {π : R} (N : NormalBasis Q π) {δ : R} (hδ : IsUnit δ) :
    ∃ c : Fin 4 → R, c 0 = 0 ∧ c 1 = 0 ∧ N.a 2 * c 2 ^ 2 + N.a 3 * c 3 ^ 2 = δ := by
  obtain ⟨s, t, hst⟩ := exists_binary_eq h2 (N.unit 2) (N.unit 3) hδ
  exact ⟨![0, 0, s, t], rfl, rfl, by simpa using hst⟩

theorem NormalBasis.Q_vec01 {π : R} (N : NormalBasis Q π) {c : Fin 4 → R} (hc : c 2 = 0 ∧ c 3 = 0) :
    Q (N.vec c) = algebraMap R F (N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2) := by
  rw [N.Q_vec, hc.1, hc.2]; simp

theorem NormalBasis.Q_vec23 {π : R} (N : NormalBasis Q π) {c : Fin 4 → R} (hc : c 0 = 0 ∧ c 1 = 0) :
    Q (N.vec c) = algebraMap R F (π * (N.a 2 * c 2 ^ 2 + N.a 3 * c 3 ^ 2)) := by
  rw [N.Q_vec, hc.1, hc.2]; simp

/-- The residue of a non-square unit is not a square (Local Square Theorem, non-dyadic). -/
theorem not_isSquare_residue (h2 : IsUnit (2 : R)) {Δ : R} (hΔ : IsUnit Δ) (hΔs : ¬ IsSquare Δ) :
    ¬ IsSquare (residue R Δ) := by
  rintro ⟨r, hr⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have h2' : ¬ π ∣ 2 := fun h => hπ.not_isUnit (isUnit_of_dvd_unit h h2)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at hr
    exact hr hΔ
  obtain ⟨z, hz⟩ := Lattices.Nbr.exists_sq_eq_of_residue hπ h2' Δ hr0 (by rw [hr, _root_.sq])
  exact hΔs ⟨z, by rw [← hz, _root_.sq]⟩

/-- Vectors realizing the four square classes: $Q(y_i) = 1, \Delta, \pi, \pi\Delta$. -/
theorem exists_vectors_cls (h2 : IsUnit (2 : R)) {π : R} (hπ : Irreducible π) (hQ : Q.Anisotropic)
    (hn : finrank F V = 4) {Δ : R} (hΔ : IsUnit Δ) : ∃ y : Fin 4 → V, ∀ i, Q (y i) = cls π Δ i := by
  obtain ⟨N⟩ := exists_normalBasis h2 hπ Q hQ hn
  obtain ⟨c0, hc0a, hc0b, hc0⟩ := N.exists_vec01 h2 isUnit_one
  obtain ⟨c1, hc1a, hc1b, hc1⟩ := N.exists_vec01 h2 hΔ
  obtain ⟨c2, hc2a, hc2b, hc2⟩ := N.exists_vec23 h2 isUnit_one
  obtain ⟨c3, hc3a, hc3b, hc3⟩ := N.exists_vec23 h2 hΔ
  refine ⟨![N.vec c0, N.vec c1, N.vec c2, N.vec c3], fun i => ?_⟩
  fin_cases i
  · simp [N.Q_vec01 ⟨hc0a, hc0b⟩, hc0, cls]
  · simp [N.Q_vec01 ⟨hc1a, hc1b⟩, hc1, cls]
  · simp [N.Q_vec23 ⟨hc2a, hc2b⟩, hc2, cls]
  · simp [N.Q_vec23 ⟨hc3a, hc3b⟩, hc3, cls]

theorem cls_ne_zero {π : R} (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ) (i : Fin 4) :
    cls (F := F) π Δ i ≠ 0 := by
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  have hΔF : algebraMap R F Δ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hΔ.ne_zero
  fin_cases i <;> simp [cls, hπF, hΔF]

/-- **Step 4 of the proof of 95:1** (O'Meara 1973, pp. 282–283): in the exceptional case,
$\tau_{(1)}\tau_{(\Delta)}\tau_{(\pi)}\tau_{(\pi\Delta)} \notin \Omega_4(V)$, for every choice of vectors $y_i$ with
$Q(y_i) = 1, \Delta, \pi, \pi\Delta$. -/
@[kb "omeara1963" "§95, proof of 95:1, step 4, pp. 282–283 (τ⟨1⟩τ⟨Δ⟩τ⟨π⟩τ⟨πΔ⟩ ∉ Ω₄)"]
theorem symProd_not_mem_omega (h2 : IsUnit (2 : R)) {π : R} (hπ : Irreducible π) (hQ : Q.Anisotropic)
    (hn : finrank F V = 4) {Δ : R} (hΔ : IsUnit Δ) (hΔs : ¬ IsSquare Δ) (y : Fin 4 → V)
    (hy : ∀ i, Q (y i) = cls π Δ i) (hy0 : ∀ u ∈ [y 0, y 1, y 2, y 3], Q u ≠ 0) :
    symProd Q [y 0, y 1, y 2, y 3] hy0 ∉ omega Q := by
  intro hmem
  have hQn := nondegenerate_of_anisotropic Q hQ
  have hres2 : residue R 2 ≠ 0 := fun h => by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h; exact h h2
  letI : Invertible (2 : ResidueField R) := invertibleOfNonzero (by rw [← map_ofNat (residue R) 2]; exact hres2)
  obtain ⟨N⟩ := exists_normalBasis h2 hπ Q hQ hn
  have D := N.redData h2 hπ hQ
  obtain ⟨c, hca, hcb, hc⟩ := N.exists_vec01 h2 isUnit_one
  obtain ⟨d, hda, hdb, hd⟩ := N.exists_vec01 h2 hΔ
  obtain ⟨c', hc'a, hc'b, hc'⟩ := N.exists_vec23 h2 isUnit_one
  obtain ⟨d', hd'a, hd'b, hd'⟩ := N.exists_vec23 h2 hΔ
  have hQc : Q (N.vec c) = cls π Δ 0 := by rw [N.Q_vec01 ⟨hca, hcb⟩, hc]; simp [cls]
  have hQd : Q (N.vec d) = cls π Δ 1 := by rw [N.Q_vec01 ⟨hda, hdb⟩, hd]; simp [cls]
  have hQc' : Q (N.vec c') = cls π Δ 2 := by rw [N.Q_vec23 ⟨hc'a, hc'b⟩, hc']; simp [cls]
  have hQd' : Q (N.vec d') = cls π Δ 3 := by rw [N.Q_vec23 ⟨hd'a, hd'b⟩, hd']; simp [cls]
  have hx : Q (N.vec c) ≠ 0 := by rw [hQc]; exact cls_ne_zero hπ hΔ 0
  have hy' : Q (N.vec d) ≠ 0 := by rw [hQd]; exact cls_ne_zero hπ hΔ 1
  have hu : Q (N.vec c') ≠ 0 := by rw [hQc']; exact cls_ne_zero hπ hΔ 2
  have hw : Q (N.vec d') ≠ 0 := by rw [hQd']; exact cls_ne_zero hπ hΔ 3
  have hstep4 := D.symmetry_prod_not_mem_omega ⟨hca, hcb⟩ ⟨hda, hdb⟩ ⟨hc'a, hc'b⟩ ⟨hd'a, hd'b⟩
    (by rw [hc]; exact isUnit_one) (by rw [hd]; exact hΔ)
    (by rw [hc, hd, one_mul]; exact not_isSquare_residue h2 hΔ hΔs) hx hy' hu hw
  have hl0 : ∀ u ∈ [N.vec c, N.vec d, N.vec c', N.vec d'], Q u ≠ 0 := by simp [hx, hy', hu, hw]
  have hperm : ([N.vec c, N.vec d, N.vec c', N.vec d'].map Q).Perm ([y 0, y 1, y 2, y 3].map Q) := by
    simp [hQc, hQd, hQc', hQd', hy]
  have h55 := symProd_mul_inv_mem_omega Q hQn hl0 hy0 hperm
  apply hstep4
  have := (omega Q).mul_mem h55 hmem
  simpa [symProd, mul_assoc] using this

/-- The element $\tau_{(1)}\tau_{(\Delta)}\tau_{(\pi)}\tau_{(\pi\Delta)}$ lies in $O'(V)$: its spinor norm is
$(\pi\Delta)^2$. -/
theorem symProd_mem_orthPrime {π : R} {Δ : R} (y : Fin 4 → V) (hy : ∀ i, Q (y i) = cls π Δ i)
    (hy0 : ∀ u ∈ [y 0, y 1, y 2, y 3], Q u ≠ 0) (hπΔ : algebraMap R F π * algebraMap R F Δ ≠ 0) :
    symProd Q [y 0, y 1, y 2, y 3] hy0 ∈ orthPrime Q := by
  refine ⟨⟨Sp55.symProd_mem_orth Q _ hy0, (MonoidHom.mem_ker).mpr ?_⟩, ?_⟩
  · rw [Sp55.det_symProd]
    exact Even.neg_one_pow ⟨2, rfl⟩
  · refine (Sp55.hasSpinorNorm_iff Q).mpr ⟨_, hy0, rfl, algebraMap R F π * algebraMap R F Δ, hπΔ, ?_⟩
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hy, cls]
    simp
    ring

/-- **Corollary 95:1a** (O'Meara 1973, p. 283): in the exceptional case (anisotropic quaternary space over a
non-dyadic field), $\tau_{(1)}\tau_{(\Delta)}\tau_{(\pi)}\tau_{(\pi\Delta)}\Omega_4$ and $\Omega_4$ are the two
distinct cosets of $O'_4$ modulo $\Omega_4$; here $\Delta$ is any non-square unit (and $\pi$ any prime element).
Stated as: $\rho = \tau_{y_0}\tau_{y_1}\tau_{y_2}\tau_{y_3} \in O'_4 \setminus \Omega_4$, and every $\sigma \in O'_4$
lies in $\Omega_4$ or in $\rho\Omega_4$. -/
@[kb "omeara1963" "§95, 95:1a, p. 283"]
theorem omega_cosets_nondyadic (h2 : IsUnit (2 : R)) {π : R} (hπ : Irreducible π) (hQ : Q.Anisotropic)
    (hn : finrank F V = 4) {Δ : R} (hΔ : IsUnit Δ) (hΔs : ¬ IsSquare Δ) (y : Fin 4 → V)
    (hy : ∀ i, Q (y i) = cls π Δ i) (hy0 : ∀ u ∈ [y 0, y 1, y 2, y 3], Q u ≠ 0) :
    symProd Q [y 0, y 1, y 2, y 3] hy0 ∈ orthPrime Q ∧ symProd Q [y 0, y 1, y 2, y 3] hy0 ∉ omega Q ∧
      ∀ σ ∈ orthPrime Q, σ ∈ omega Q ∨ σ * (symProd Q [y 0, y 1, y 2, y 3] hy0)⁻¹ ∈ omega Q := by
  have hQn := nondegenerate_of_anisotropic Q hQ
  refine ⟨symProd_mem_orthPrime y hy hy0 (by simpa [cls] using cls_ne_zero (F := F) hπ hΔ 3),
    symProd_not_mem_omega h2 hπ hQ hn hΔ hΔs y hy hy0, fun σ hσ => ?_⟩
  exact mem_omega_or_of_classes Q hQn (Δ := algebraMap R F Δ) (π := algebraMap R F π)
    (fun x hx => exists_cls h2 hπ hΔ hΔs hx) (fun m n => isSquare_pow_iff hπ hΔ hΔs m n) y hy hy0 hσ

/-- **Proposition 95:1, the exceptional case** (O'Meara 1973, pp. 280–283): for an anisotropic quaternary space
over a non-dyadic local field, $(O'_4 : \Omega_4) = 2$. -/
@[kb "omeara1963" "§95, 95:1, pp. 280–283 ((O'₄ : Ω₄) = 2 in the exceptional case)"]
theorem relIndex_omega_orthPrime_nondyadic (h2 : IsUnit (2 : R)) (hQ : Q.Anisotropic) (hn : finrank F V = 4) :
    (omega Q).relIndex (orthPrime Q) = 2 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨Δ, hΔ, hΔs, -⟩ := exists_nonsquare_unit (R := R) h2
  obtain ⟨y, hy⟩ := exists_vectors_cls (F := F) h2 hπ hQ hn hΔ
  have hy0 : ∀ u ∈ [y 0, y 1, y 2, y 3], Q u ≠ 0 := by
    have := fun i => (hy i).symm ▸ cls_ne_zero (F := F) hπ hΔ i
    simp [this]
  have hQn := nondegenerate_of_anisotropic Q hQ
  obtain ⟨hρ', hρ, hall⟩ := omega_cosets_nondyadic h2 hπ hQ hn hΔ hΔs y hy hy0
  set ρ := symProd Q [y 0, y 1, y 2, y 3] hy0
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨ρ, hρ'⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  have hρ2 : ρ * ρ ∈ omega Q := by
    have := sq_mem_omega Q hQn (σ := ρ) hρ'.1.1
    simpa [pow_two] using this
  by_cases hb : (b : V ≃ₗ[F] V) ∈ omega Q
  · refine Or.inr ⟨hb, fun h => hρ ?_⟩
    have := (omega Q).mul_mem ((omega Q).inv_mem hb) h
    simpa [mul_assoc] using this
  · refine Or.inl ⟨?_, hb⟩
    have h1 := (hall b b.2).resolve_left hb
    have := (omega Q).mul_mem h1 hρ2
    simpa [mul_assoc] using this

/-- The unit vector $e_i = \sum_k \delta_{ik}e_k$ as a vector with integral coordinates. -/
theorem NormalBasis.vec_single {π : R} (N : NormalBasis Q π) (i : Fin 4) : N.vec (Pi.single i 1) = N.e i := by
  simp only [NormalBasis.vec]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- $-1_V = \tau_{e_0}\tau_{e_1}\tau_{e_2}\tau_{e_3}$ for an orthogonal base. -/
theorem NormalBasis.neg_eq {π : R} (N : NormalBasis Q π) (h0 : Q (N.e 0) ≠ 0) (h1 : Q (N.e 1) ≠ 0)
    (h2 : Q (N.e 2) ≠ 0) (h3 : Q (N.e 3) ≠ 0) :
    symmetry Q (N.e 0) h0 * symmetry Q (N.e 1) h1 * symmetry Q (N.e 2) h2 * symmetry Q (N.e 3) h3 =
      LinearEquiv.neg F := by
  have hms : ∀ u ∈ List.ofFn N.e, Q u ≠ 0 := by
    intro u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    fin_cases i <;> assumption
  have hneg : symProd Q (List.ofFn N.e) hms = LinearEquiv.neg F := by
    refine LinearEquiv.toLinearMap_injective (N.e.ext fun j => ?_)
    show symProd Q (List.ofFn N.e) hms (N.e j) = -(N.e j)
    exact Sp55.symProd_apply_of_mem Q _ hms (List.pairwise_ofFn.mpr fun i j hij => N.orth i j hij.ne) _
      (List.mem_ofFn.mpr ⟨j, rfl⟩)
  rw [← hneg]
  simp [symProd, List.ofFn_succ, mul_assoc]

/-- **The exceptional case of the structure of $\Omega_4 \cap Z_4$** (O'Meara 1973, §95, pp. 283–284): for an
anisotropic quaternary space over a non-dyadic field, $-1_V \in \Omega_4(V)$ if and only if $-1$ is not a square
in $F$. Since $Z_4 = \{\pm 1_V\}$, this is O'Meara's "$\Omega_4 \cap Z_4 = \{\pm 1_V\}$ if and only if $-1$ is a
non-square in $F$". If $-1$ is a non-square, $V \cong \langle 1\rangle \perp \langle 1\rangle \perp
\langle\pi\rangle \perp \langle\pi\rangle$ up to squares and $-1_V = \tau_{(1)}\tau_{(1)}\tau_{(\pi)}\tau_{(\pi)} \in
\Omega_4$; if $-1$ is a square, $-1_V$ has the form $\tau_{(1)}\tau_{(\Delta)}\tau_{(\pi)}\tau_{(\pi\Delta)}$, which
is not in $\Omega_4$ (here directly by step 4 of the proof of 95:1, instead of O'Meara's appeal to 95:1a). -/
@[kb "omeara1963" "§95, pp. 283–284 (Ω₄ ∩ Z₄ = {±1_V} iff −1 is a non-square, the exceptional case)"]
theorem neg_one_mem_omega_iff_nondyadic (h2 : IsUnit (2 : R)) (hQ : Q.Anisotropic) (hn : finrank F V = 4) :
    LinearEquiv.neg F ∈ omega Q ↔ ¬ IsSquare (-1 : F) := by
  have hQn := nondegenerate_of_anisotropic Q hQ
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨N⟩ := exists_normalBasis h2 hπ Q hQ hn
  have hinj := IsFractionRing.injective R F
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  have hne : ∀ i, Q (N.e i) ≠ 0 := fun i h => by
    have := hQ _ h; exact N.e.ne_zero i this
  have hu : ∀ i, algebraMap R F (N.a i) ≠ 0 := fun i => (map_ne_zero_iff _ hinj).mpr (N.unit i).ne_zero
  have hneg := N.neg_eq (hne 0) (hne 1) (hne 2) (hne 3)
  have hn01 := N.not_isSquare_neg_mul01 hQ
  have hn23 := N.not_isSquare_neg_mul23 hQ
  constructor
  · intro hmem hsq
    have hres2 : residue R 2 ≠ 0 := fun h => by
      rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h; exact h h2
    letI : Invertible (2 : ResidueField R) := invertibleOfNonzero (by rw [← map_ofNat (residue R) 2]; exact hres2)
    have D := N.redData h2 hπ hQ
    -- `a₀a₁` is not a square, since `-1` is one and `-a₀a₁` is not
    have hns : ¬ IsSquare (N.a 0 * N.a 1) := by
      rintro ⟨r, hr⟩
      obtain ⟨t, ht⟩ := hsq
      apply not_isSquare_algebraMap (F := F) (((N.unit 0).mul (N.unit 1)).neg) hn01
      exact ⟨t * algebraMap R F r, by rw [map_neg, hr, map_mul]; linear_combination (algebraMap R F r) ^ 2 * ht⟩
    have hx : ∀ i, Q (N.vec (Pi.single i 1)) ≠ 0 := fun i => by rw [N.vec_single]; exact hne i
    have h4 := D.symmetry_prod_not_mem_omega (c := Pi.single 0 1) (d := Pi.single 1 1) (c' := Pi.single 2 1)
      (d' := Pi.single 3 1) (by simp) (by simp) (by simp) (by simp) (by simpa using N.unit 0)
      (by simpa using N.unit 1)
      (by simpa using not_isSquare_residue h2 ((N.unit 0).mul (N.unit 1)) hns) (hx 0) (hx 1) (hx 2) (hx 3)
    apply h4
    simp only [N.vec_single]
    rwa [hneg]
  · intro hns
    have hns' : ¬ IsSquare (-1 : R) := fun ⟨r, hr⟩ => hns ⟨algebraMap R F r, by rw [← map_mul, ← hr]; simp⟩
    have hsq01 : IsSquare (N.a 0 * N.a 1) := by
      rcases isSquare_or_isSquare_mul h2 isUnit_one.neg hns' ((N.unit 0).mul (N.unit 1)).neg with h | h
      · exact absurd h hn01
      · simpa using h
    have hsq23 : IsSquare (N.a 2 * N.a 3) := by
      rcases isSquare_or_isSquare_mul h2 isUnit_one.neg hns' ((N.unit 2).mul (N.unit 3)).neg with h | h
      · exact absurd h hn23
      · simpa using h
    obtain ⟨r, hr⟩ := hsq01
    obtain ⟨r', hr'⟩ := hsq23
    have hr0 : algebraMap R F r ≠ 0 := fun h => by
      have := congrArg (algebraMap R F) hr
      rw [map_mul, map_mul, h, zero_mul] at this
      exact mul_ne_zero (hu 0) (hu 1) this
    have hr'0 : algebraMap R F r' ≠ 0 := fun h => by
      have := congrArg (algebraMap R F) hr'
      rw [map_mul, map_mul, h, zero_mul] at this
      exact mul_ne_zero (hu 2) (hu 3) this
    have h01 := symmetry_mul_symmetry_mem_omega Q hQn (hne 0) (hne 1)
      (s := algebraMap R F r / algebraMap R F (N.a 1)) (div_ne_zero hr0 (hu 1)) (by
        have := congrArg (algebraMap R F) hr
        rw [map_mul, map_mul] at this
        rw [N.Q0, N.Q1, div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 (hu 1))]
        linear_combination (algebraMap R F (N.a 1)) * this)
    have h23 := symmetry_mul_symmetry_mem_omega Q hQn (hne 2) (hne 3)
      (s := algebraMap R F r' / algebraMap R F (N.a 3)) (div_ne_zero hr'0 (hu 3)) (by
        have := congrArg (algebraMap R F) hr'
        rw [map_mul, map_mul] at this
        rw [N.Q2, N.Q3, map_mul, map_mul, div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 (hu 3))]
        linear_combination (algebraMap R F π * algebraMap R F (N.a 3)) * this)
    rw [← hneg, mul_assoc]
    exact (omega Q).mul_mem h01 h23

end S95

end QuadFormsKB.OMeara
