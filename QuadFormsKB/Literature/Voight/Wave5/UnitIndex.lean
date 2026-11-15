/-
# The unit index $[\mathcal O^\times : 1 + \mathfrak p\mathcal O]$ of a local Eichler order (Voight, Lemma 24.3.12)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Lemma 24.3.12 (p. 402).

**Setting.** $R$ a discrete valuation ring with fraction field $F$ (Lean: `K`), uniformizer $\pi$, finite residue field
$k$ with $q = \#k$; $\mathcal O = \mathcal O_0(\pi^e) = \begin{pmatrix} R & R \\ \pi^eR & R\end{pmatrix}$ (`stdEichlerOrder`); for
$e = 0$ this is $\mathrm M_2(R)$. Entries are indexed $0, 1$.

**Lemma 24.3.12** says $1 + \mathfrak p\mathcal O \subseteq \mathcal O^\times$ and computes $[\mathcal O^\times : 1 + \mathfrak p\mathcal O]$ from the
Eichler symbol: $q(q-1)^2(q+1)$ if $(\mathcal O \mid \mathfrak p) = *$, $q^2(q-1)^2$ if $(\mathcal O \mid \mathfrak p) = 1$,
$q^2(q^2-1)$ if $-1$, $q^3(q-1)$ if $0$.

**Contents** (proved).
* `onePlusUnits O π`: the subgroup $1 + \pi\mathcal O$ of $\mathcal O^\times$, for any $R$-algebra.
* `isUnit_one_add_smul`: $1 + \pi\mathcal O \subseteq \mathcal O^\times$ for $\mathcal O = \mathcal O_0(\pi^e)$.
* `index_onePlusUnits_stdEichlerOrder`: for $e \ge 1$ (residually split, $(\mathcal O \mid \mathfrak p) = 1$ by
  `Wave6.hasEichlerSymbol_one_stdEichlerOrder`) the index is $q^2(q-1)^2$.
* `index_onePlusUnits_matOrder`: for $\mathcal O = \mathrm M_2(R)$ ($(\mathcal O \mid \mathfrak p) = *$) the index is
  $\#\mathrm{GL}_2(k) = (q^2 - 1)(q^2 - q) = q(q-1)^2(q+1)$.
The residually inert and residually ramified cases are not treated (no such orders are constructed here). Completeness of
$R$ is not used.
-/
import QuadFormsKB.Literature.Voight.Wave5.EichlerSymbol
import QuadFormsKB.Literature.Voight.Wave4.EichlerDiscriminant

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave6

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4 QuadFormsKB.Voight.Wave5 IsLocalization

/-- **The subgroup $1 + \pi\mathcal O$** of the unit group $\mathcal O^\times$ of an $R$-algebra $\mathcal O$ (Voight 2021,
Lemma 24.3.12, with $\mathfrak p = \pi R$): the units $u$ with $u = 1 + \pi y$ for some $y \in \mathcal O$. -/
@[kb "voight2021" "Lemma 24.3.12, p. 402"]
def onePlusUnits {R B : Type*} [CommRing R] [Ring B] [Algebra R B] (O : Subalgebra R B) (π : R) : Subgroup Oˣ where
  carrier := {u | ∃ y : O, (u : O) = 1 + π • y}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro u v ⟨y, hy⟩ ⟨z, hz⟩
    refine ⟨y + z + π • (y * z), ?_⟩
    rw [Units.val_mul, hy, hz]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel
  inv_mem' := by
    rintro u ⟨y, hy⟩
    refine ⟨-((↑u⁻¹ : O) * y), ?_⟩
    have h1 : (↑u⁻¹ : O) * u = 1 := u.inv_mul
    rw [hy, mul_add, mul_one, mul_smul_comm] at h1
    rw [smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq, h1]


/-- The index $[\mathcal O^\times : 1 + \pi\mathcal O]$ is invariant under isomorphisms of $R$-algebras. -/
theorem index_onePlusUnits_of_algEquiv {R B B' : Type*} [CommRing R] [Ring B] [Algebra R B] [Ring B'] [Algebra R B']
    {O : Subalgebra R B} {O' : Subalgebra R B'} (f : O ≃ₐ[R] O') (π : R) :
    (onePlusUnits O' π).index = (onePlusUnits O π).index := by
  have h : onePlusUnits O π = (onePlusUnits O' π).comap (Units.map (f : O →* O')) := by
    ext u
    simp only [Subgroup.mem_comap]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨f y, ?_⟩
      simp only [Units.coe_map, MonoidHom.coe_ofClass, hy, map_add, map_one, map_smul]
    · rintro ⟨y', hy'⟩
      refine ⟨f.symm y', f.injective ?_⟩
      simp only [Units.coe_map, MonoidHom.coe_ofClass] at hy'
      rw [hy', map_add, map_one, map_smul, AlgEquiv.apply_symm_apply]
  rw [h, Subgroup.index_comap_of_surjective]
  intro u'
  refine ⟨Units.map (f.symm : O' →* O) u', Units.ext ?_⟩
  simp only [Units.coe_map, MonoidHom.coe_ofClass]
  exact f.apply_symm_apply _

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Coordinates on $\mathcal O_0(\pi^e)$ -/

section Coord

variable {π : R} {e : ℕ}

/-- The coordinates $(c_0, c_1, c_2, c_3) \in R^4$ of $x = \begin{pmatrix} c_0 & c_1 \\ \pi^ec_2 & c_3\end{pmatrix} \in
\mathcal O_0(\pi^e)$ in the basis $E_{00}, E_{01}, \pi^eE_{10}, E_{11}$ (`stdEichlerComb`). -/
def coordE (hπ : π ≠ 0) (x : stdEichlerOrder R K π e) : Fin 4 → R :=
  (LinearEquiv.ofBijective (stdEichlerCombS (K := K) π e) (stdEichlerCombS_bijective hπ)).symm ⟨(x : Matrix (Fin 2) (Fin 2) K), x.2⟩

theorem coordE_spec (hπ : π ≠ 0) (x : stdEichlerOrder R K π e) :
    stdEichlerComb (K := K) π e (coordE hπ x) = (x : Matrix (Fin 2) (Fin 2) K) :=
  congrArg Subtype.val
    ((LinearEquiv.ofBijective (stdEichlerCombS (K := K) π e) (stdEichlerCombS_bijective hπ)).apply_symm_apply
      ⟨(x : Matrix (Fin 2) (Fin 2) K), x.2⟩)

theorem coordE_eq_of_comb (hπ : π ≠ 0) (x : stdEichlerOrder R K π e) {c : Fin 4 → R}
    (h : stdEichlerComb (K := K) π e c = (x : Matrix (Fin 2) (Fin 2) K)) : coordE hπ x = c := by
  apply (stdEichlerCombS_bijective (K := K) hπ).1
  apply Subtype.ext
  change stdEichlerComb (K := K) π e (coordE hπ x) = stdEichlerComb (K := K) π e c
  rw [coordE_spec, h]

theorem intMat_eq_coordE (hπ : π ≠ 0) (x : stdEichlerOrder R K π e) :
    intMat x = !![coordE hπ x 0, coordE hπ x 1; π ^ e * coordE hπ x 2, coordE hπ x 3] := by
  have h := coordE_spec hπ x
  rw [stdEichlerComb_apply] at h
  ext i j
  apply IsFractionRing.injective R K
  rw [algebraMap_intMat, ← h]
  fin_cases i <;> fin_cases j <;> rfl

/-- The element of $\mathcal O_0(\pi^e)$ with coordinates $c$. -/
def ofCoord (π : R) (e : ℕ) (c : Fin 4 → R) : stdEichlerOrder R K π e :=
  ⟨stdEichlerComb (K := K) π e c, stdEichlerComb_mem π e c⟩

theorem coordE_ofCoord (hπ : π ≠ 0) (c : Fin 4 → R) : coordE hπ (ofCoord (K := K) π e c) = c :=
  coordE_eq_of_comb hπ _ rfl

theorem coordE_add_smul (hπ : π ≠ 0) (x z : stdEichlerOrder R K π e) (r : R) :
    coordE hπ (x + r • z) = coordE hπ x + r • coordE hπ z := by
  apply coordE_eq_of_comb
  rw [map_add, map_smul, coordE_spec, coordE_spec]
  rfl

end Coord

/-! ### Units of $\mathcal O_0(\pi^e)$ and the congruence $x \equiv y \bmod \pi\mathcal O$ -/

section Local

variable [IsLocalRing R] {π : R} {e : ℕ}

/-- The coordinates modulo $\mathfrak p$, $\Phi(x) \in k^4$. -/
def resCoord (hπ : π ≠ 0) (x : stdEichlerOrder R K π e) : Fin 4 → IsLocalRing.ResidueField R :=
  fun i => IsLocalRing.residue R (coordE hπ x i)

/-- $x \equiv y \pmod{\pi\mathcal O}$ iff $x$ and $y$ have the same coordinates modulo $\mathfrak p = \pi R$. -/
theorem resCoord_eq_iff (hπ : π ≠ 0) (hπm : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (x y : stdEichlerOrder R K π e) : resCoord hπ x = resCoord hπ y ↔ ∃ z, y = x + π • z := by
  constructor
  · intro h
    have hd : ∀ i, ∃ d, coordE hπ y i = coordE hπ x i + π * d := fun i => by
      have hi := congrFun h i
      simp only [resCoord] at hi
      rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hπm,
        Ideal.mem_span_singleton] at hi
      obtain ⟨d, hd⟩ := hi
      exact ⟨d, by rw [← hd]; ring⟩
    choose d hd using hd
    refine ⟨ofCoord π e d, ?_⟩
    have hc : coordE hπ y = coordE hπ (x + π • ofCoord (K := K) π e d) := by
      rw [coordE_add_smul, coordE_ofCoord]
      funext i
      rw [hd i]
      rfl
    have := congrArg (stdEichlerComb (K := K) π e) hc
    rw [coordE_spec, coordE_spec] at this
    exact Subtype.ext this
  · rintro ⟨z, rfl⟩
    funext i
    simp only [resCoord, coordE_add_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
      (IsLocalRing.residue_eq_zero_iff π).2 (by rw [hπm]; exact Ideal.mem_span_singleton_self π), zero_mul,
      add_zero]

/-- The residue of $\det x$, in coordinates: $\Phi_0\Phi_3 - \Phi_1\bar\pi^e\Phi_2$. -/
theorem residue_det_intMat (hπ : π ≠ 0) (x : stdEichlerOrder R K π e) :
    IsLocalRing.residue R (intMat x).det =
      resCoord hπ x 0 * resCoord hπ x 3 - resCoord hπ x 1 * IsLocalRing.residue R π ^ e * resCoord hπ x 2 := by
  rw [intMat_eq_coordE hπ, Matrix.det_fin_two_of]
  simp only [resCoord, map_sub, map_mul, map_pow]
  ring

/-- **Units of $\mathcal O_0(\pi^e)$**: $x$ is a unit iff $\det x$ is a unit of $R$. -/
theorem isUnit_iff_isUnit_det (x : stdEichlerOrder R K π e) : IsUnit x ↔ IsUnit (intMat x).det := by
  refine ⟨fun ⟨u, hu⟩ => ?_, isUnit_of_isUnit_det x⟩
  have h : intMat (u : stdEichlerOrder R K π e) * intMat (↑u⁻¹ : stdEichlerOrder R K π e) = 1 := by
    rw [← intMat_mul, u.mul_inv, intMat_one]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hd
  rw [← hu]
  exact IsUnit.of_mul_eq_one _ hd

theorem isUnit_iff_residue (hπ : π ≠ 0) (x : stdEichlerOrder R K π e) :
    IsUnit x ↔ resCoord hπ x 0 * resCoord hπ x 3 - resCoord hπ x 1 * IsLocalRing.residue R π ^ e * resCoord hπ x 2 ≠ 0 := by
  rw [isUnit_iff_isUnit_det, ← residue_det_intMat hπ, ne_eq, IsLocalRing.residue_eq_zero_iff]
  exact IsLocalRing.notMem_maximalIdeal.symm

/-- **$1 + \pi\mathcal O \subseteq \mathcal O^\times$** (Voight 2021, Lemma 24.3.12, first statement) for
$\mathcal O = \mathcal O_0(\pi^e)$. -/
@[kb "voight2021" "Lemma 24.3.12, p. 402"]
theorem isUnit_one_add_smul (hπ : π ≠ 0) (hπm : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (y : stdEichlerOrder R K π e) : IsUnit (1 + π • y) := by
  have h1 : resCoord hπ (1 : stdEichlerOrder R K π e) = resCoord hπ (1 + π • y) :=
    (resCoord_eq_iff hπ hπm _ _).2 ⟨y, rfl⟩
  rw [isUnit_iff_residue hπ, ← h1, ← isUnit_iff_residue hπ]
  exact isUnit_one

/-- Two units lie in the same left coset of $1 + \pi\mathcal O$ iff they agree modulo $\pi\mathcal O$. -/
theorem inv_mul_mem_onePlusUnits_iff (hπ : π ≠ 0) (hπm : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (u v : (stdEichlerOrder R K π e)ˣ) :
    u⁻¹ * v ∈ onePlusUnits (stdEichlerOrder R K π e) π ↔ resCoord hπ (u : stdEichlerOrder R K π e) = resCoord hπ (v : stdEichlerOrder R K π e) := by
  rw [resCoord_eq_iff hπ hπm]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(u : stdEichlerOrder R K π e) * z, ?_⟩
    have : (v : stdEichlerOrder R K π e) = u * ((u⁻¹ * v : (stdEichlerOrder R K π e)ˣ) : stdEichlerOrder R K π e) := by
      rw [Units.val_mul, ← mul_assoc, u.mul_inv, one_mul]
    rw [this, hz, mul_add, mul_one, mul_smul_comm]
  · rintro ⟨z, hz⟩
    refine ⟨(↑u⁻¹ : stdEichlerOrder R K π e) * z, ?_⟩
    rw [Units.val_mul, hz, mul_add, u.inv_mul, mul_smul_comm]

/-- The quotient $\mathcal O^\times/(1 + \pi\mathcal O)$ (left cosets) is in bijection with the coordinate vectors
$w \in k^4$ with $w_0w_3 - w_1\bar\pi^ew_2 \ne 0$. -/
def quotEquiv (hπ : π ≠ 0) (hπm : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    (stdEichlerOrder R K π e)ˣ ⧸ onePlusUnits (stdEichlerOrder R K π e) π ≃
      {w : Fin 4 → IsLocalRing.ResidueField R // w 0 * w 3 - w 1 * IsLocalRing.residue R π ^ e * w 2 ≠ 0} :=
  Equiv.ofBijective
    (Quotient.lift (fun u : (stdEichlerOrder R K π e)ˣ =>
        (⟨resCoord hπ (u : stdEichlerOrder R K π e), (isUnit_iff_residue hπ _).1 u.isUnit⟩ :
          {w : Fin 4 → IsLocalRing.ResidueField R // w 0 * w 3 - w 1 * IsLocalRing.residue R π ^ e * w 2 ≠ 0}))
      (fun u v huv => Subtype.ext ((inv_mul_mem_onePlusUnits_iff hπ hπm u v).1
        (QuotientGroup.leftRel_apply.1 huv))))
    (by
      constructor
      · rintro ⟨u⟩ ⟨v⟩ h
        exact Quotient.sound (QuotientGroup.leftRel_apply.2
          ((inv_mul_mem_onePlusUnits_iff hπ hπm u v).2 (congrArg Subtype.val h)))
      · rintro ⟨w, hw⟩
        choose c hc using fun i => IsLocalRing.residue_surjective (w i)
        have hcw : resCoord hπ (ofCoord (K := K) π e c) = w := by
          funext i
          simp only [resCoord, coordE_ofCoord, hc]
        have hu : IsUnit (ofCoord (K := K) π e c) := by
          rw [isUnit_iff_residue hπ, hcw]
          exact hw
        exact ⟨Quotient.mk _ hu.unit, Subtype.ext hcw⟩)

theorem index_onePlusUnits_eq_card (hπ : π ≠ 0) (hπm : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    (onePlusUnits (stdEichlerOrder R K π e) π).index =
      Nat.card {w : Fin 4 → IsLocalRing.ResidueField R // w 0 * w 3 - w 1 * IsLocalRing.residue R π ^ e * w 2 ≠ 0} :=
  Nat.card_congr (quotEquiv hπ hπm)

end Local

/-! ### Counting -/

section Count

variable {k : Type*} [Field k] [Finite k]

/-- $\#\{a \in k : a \ne 0\} = q - 1$. -/
theorem card_ne_zero_field : Nat.card {a : k // a ≠ 0} = Nat.card k - 1 := by
  have := Fintype.ofFinite k
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- $\#\{w \in k^4 : w_0w_3 \ne 0\} = q^2(q-1)^2$. -/
theorem card_split (q : ℕ) (hq : Nat.card k = q) :
    Nat.card {w : Fin 4 → k // w 0 * w 3 ≠ 0} = q ^ 2 * (q - 1) ^ 2 := by
  let E : {w : Fin 4 → k // w 0 * w 3 ≠ 0} ≃ {a : k // a ≠ 0} × k × k × {a : k // a ≠ 0} :=
    { toFun := fun w => (⟨w.1 0, left_ne_zero_of_mul w.2⟩, w.1 1, w.1 2, ⟨w.1 3, right_ne_zero_of_mul w.2⟩)
      invFun := fun p => ⟨![p.1.1, p.2.1, p.2.2.1, p.2.2.2.1], mul_ne_zero p.1.2 p.2.2.2.2⟩
      left_inv := fun w => by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr E, Nat.card_prod, Nat.card_prod, Nat.card_prod, card_ne_zero_field, hq]
  ring

/-- $\#\{w \in k^4 : w_0w_3 - w_1w_2 \ne 0\} = \#\mathrm{GL}_2(k) = (q^2 - 1)(q^2 - q)$. -/
theorem card_gl (q : ℕ) (hq : Nat.card k = q) :
    Nat.card {w : Fin 4 → k // w 0 * w 3 - w 1 * w 2 ≠ 0} = (q ^ 2 - 1) * (q ^ 2 - q) := by
  let E : {w : Fin 4 → k // w 0 * w 3 - w 1 * w 2 ≠ 0} ≃ GL (Fin 2) k :=
    { toFun := fun w => Matrix.GeneralLinearGroup.mkOfDetNeZero !![w.1 0, w.1 1; w.1 2, w.1 3]
        (by rw [Matrix.det_fin_two_of]; exact w.2)
      invFun := fun g => ⟨![(g : Matrix (Fin 2) (Fin 2) k) 0 0, (g : Matrix (Fin 2) (Fin 2) k) 0 1,
          (g : Matrix (Fin 2) (Fin 2) k) 1 0, (g : Matrix (Fin 2) (Fin 2) k) 1 1], by
        have h := Matrix.isUnits_det_units g
        rw [Matrix.det_fin_two] at h
        show (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 1 -
          (g : Matrix (Fin 2) (Fin 2) k) 0 1 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0
        exact h.ne_zero⟩
      left_inv := fun w => by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      right_inv := fun g => by
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;> rfl }
  let _ := Fintype.ofFinite k
  rw [Nat.card_congr E, Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hq, Fin.prod_univ_two]
  simp

end Count

/-! ### Lemma 24.3.12 for the standard Eichler order and for $\mathrm M_2(R)$ -/

variable [IsDiscreteValuationRing R]

theorem maximalIdeal_eq_span {π : R} (hπ : Irreducible π) : IsLocalRing.maximalIdeal R = Ideal.span {π} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ

/-- **Lemma 24.3.12, residually split case** (Voight 2021): for the standard Eichler order $\mathcal O = \mathcal O_0(\pi^e)$ of
level $\pi^e$, $e \ge 1$, which has $(\mathcal O \mid \mathfrak p) = 1$ (`hasEichlerSymbol_one_stdEichlerOrder`), and a finite
residue field with $q$ elements,
$$[\mathcal O^\times : 1 + \pi\mathcal O] = q^2(q-1)^2.$$ -/
@[kb "voight2021" "Lemma 24.3.12, p. 402"]
theorem index_onePlusUnits_stdEichlerOrder {π : R} (hπ : Irreducible π) [Finite (IsLocalRing.ResidueField R)]
    {e : ℕ} (he : 1 ≤ e) :
    (onePlusUnits (stdEichlerOrder R K π e) π).index =
      Nat.card (IsLocalRing.ResidueField R) ^ 2 * (Nat.card (IsLocalRing.ResidueField R) - 1) ^ 2 := by
  have hπm := maximalIdeal_eq_span hπ
  rw [index_onePlusUnits_eq_card hπ.ne_zero hπm]
  have h0 : IsLocalRing.residue R π ^ e = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff π |>.2 (by rw [hπm]; exact Ideal.mem_span_singleton_self π)]
    exact zero_pow (by omega)
  simp only [h0, mul_zero, zero_mul, sub_zero]
  exact card_split _ rfl

/-- **Lemma 24.3.12, case $(\mathcal O \mid \mathfrak p) = *$** (Voight 2021) for $\mathcal O = \mathrm M_2(R)$ $(= \mathcal O_0(\pi^0))$
and a finite residue field with $q$ elements:
$$[\mathcal O^\times : 1 + \pi\mathcal O] = \#\mathrm{GL}_2(k) = (q^2 - 1)(q^2 - q) = q(q-1)^2(q+1).$$ -/
@[kb "voight2021" "Lemma 24.3.12, p. 402"]
theorem index_onePlusUnits_matOrder {π : R} (hπ : Irreducible π) [Finite (IsLocalRing.ResidueField R)] :
    (onePlusUnits (stdEichlerOrder R K π 0) π).index =
      (Nat.card (IsLocalRing.ResidueField R) ^ 2 - 1) * (Nat.card (IsLocalRing.ResidueField R) ^ 2 -
        Nat.card (IsLocalRing.ResidueField R)) := by
  rw [index_onePlusUnits_eq_card hπ.ne_zero (maximalIdeal_eq_span hπ)]
  simp only [pow_zero, mul_one]
  exact card_gl _ rfl

/-- **Lemma 24.3.12, residually split case, for every local Eichler order** (Voight 2021): over a discrete valuation ring
with finite residue field of $q$ elements, a non-maximal Eichler order $\mathcal O \subseteq \mathrm M_2(F)$ (residually
split by Lemma 24.3.6, `IsEichler.hasEichlerSymbol_one`) has $[\mathcal O^\times : 1 + \pi\mathcal O] = q^2(q-1)^2$. -/
@[kb "voight2021" "Lemma 24.3.12, p. 402"]
theorem IsEichler.index_onePlusUnits {π : R} (hπ : Irreducible π) [Finite (IsLocalRing.ResidueField R)]
    {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)} (hO : IsEichler R K O) (hmax : ¬ IsMaximalOrder R K O) :
    (onePlusUnits O π).index =
      Nat.card (IsLocalRing.ResidueField R) ^ 2 * (Nat.card (IsLocalRing.ResidueField R) - 1) ^ 2 := by
  obtain ⟨e, P, Q, hPQ, hQP, rfl⟩ := (isEichler_iff_exists_conj hπ O).1 hO
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exfalso
    apply hmax
    rw [stdEichlerOrder_zero]
    exact isMaximalOrder_matOrder.map (conjAlgEquiv P Q hPQ hQP)
  · rw [index_onePlusUnits_of_algEquiv
      (Subalgebra.equivMapOfInjective (stdEichlerOrder R K π e)
        (((conjAlgEquiv P Q hPQ hQP) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R)
        (conjAlgEquiv P Q hPQ hQP).injective)]
    exact index_onePlusUnits_stdEichlerOrder hπ he

/-- The two forms of the $*$ count agree: $(q^2 - 1)(q^2 - q) = q(q-1)^2(q+1)$. -/
theorem gl_count_eq (q : ℕ) : (q ^ 2 - 1) * (q ^ 2 - q) = q * (q - 1) ^ 2 * (q + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have h1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hq; simp [pow_two]; ring_nf; omega
    have h2 : q ^ 2 - q = q * (q - 1) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hq; simp [pow_two]; ring_nf; omega
    rw [h1, h2]
    ring

end QuadFormsKB.Voight.Wave6
