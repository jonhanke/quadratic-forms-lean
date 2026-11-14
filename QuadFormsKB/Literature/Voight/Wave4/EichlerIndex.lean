/-
# The unit index of the standard Eichler order (Voight, Lemma 26.6.7 / 23.4.12)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`).

**Model.** $R$ a discrete valuation ring with uniformizer $\pi$ and finite residue field of size $q$, $K = \operatorname{Frac} R$,
$\mathcal O_0(\pi^e) = \begin{pmatrix} R & R\\ \pi^eR & R\end{pmatrix} \subseteq \mathrm M_2(R)$.

**Main result** (`index_units_stdEichlerOrder`): for $e \ge 1$,
$$[\mathrm{GL}_2(R) : \mathcal O_0(\pi^e)^\times] = q^{e-1}(q+1).$$

**Proof.** $\mathrm{GL}_2(R)$ acts on $(R/\pi^e)^2$ by reduction. The stabilizer $\Gamma_1$ of $v_0 = (1,0)$ has index equal to
the number of unimodular vectors, $q^{2e} - q^{2e-2}$; it lies in $H = \mathcal O_0(\pi^e)^\times$ with $[H:\Gamma_1] = \#(R/\pi^e)^\times
= q^e - q^{e-1}$ (the $H$-orbit of $v_0$). Hence $[\mathrm{GL}_2(R):H] = q^{e-1}(q+1)$.
Matrix indices are 0-based.
-/
import QuadFormsKB.Literature.Voight.Wave3.EichlerLocal
import QuadFormsKB.Tamagawa.AlphaLawIndex

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave4

/-! ### Generic part: a local ring and a proper ideal -/

section Generic

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- For $I \subseteq \mathfrak m$, an element of $R/I$ is a unit iff any lift is. -/
theorem isUnit_mk_iff {I : Ideal R} (hI : I ≤ IsLocalRing.maximalIdeal R) (r : R) :
    IsUnit (Ideal.Quotient.mk I r) ↔ IsUnit r := by
  constructor
  · rintro ⟨u, hu⟩
    by_contra hr
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : R ⧸ I)
    have h1 : Ideal.Quotient.mk I (r * b - 1) = 0 := by
      rw [map_sub, map_mul, hb, ← hu, map_one, Units.mul_inv, sub_self]
    have h2 : r * b - 1 ∈ IsLocalRing.maximalIdeal R := hI (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    have h3 : r ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal r).2 hr
    have h4 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right b _ h3) h2
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h4)
  · exact fun h => h.map _

/-- The matrix $\begin{pmatrix} a&b\\c&d\end{pmatrix} \in \mathrm{GL}_2(R)$ when $ad - bc$ is a unit. -/
def mkUnit (a b c d : R) (h : IsUnit (a * d - b * c)) : (Matrix (Fin 2) (Fin 2) R)ˣ :=
  Matrix.nonsingInvUnit !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

theorem mkUnit_val (a b c d : R) (h : IsUnit (a * d - b * c)) :
    ((mkUnit a b c d h : (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R) = !![a, b; c, d] := rfl

/-- Reduction of a matrix of $\mathrm{GL}_2(R)$ modulo $I$. -/
def redM (I : Ideal R) (g : (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) (R ⧸ I) :=
  (g : Matrix (Fin 2) (Fin 2) R).map (Ideal.Quotient.mk I)

/-- The action of $\mathrm{GL}_2(R)$ on $(R/I)^2$ through reduction mod $I$. -/
def actV (I : Ideal R) : MulAction (Matrix (Fin 2) (Fin 2) R)ˣ (Fin 2 → R ⧸ I) where
  smul g v := redM I g *ᵥ v
  one_smul v := by
    change redM I 1 *ᵥ v = v
    simp [redM]
  mul_smul g h v := by
    change redM I (g * h) *ᵥ v = redM I g *ᵥ (redM I h *ᵥ v)
    simp only [redM, Units.val_mul, Matrix.map_mul, Matrix.mulVec_mulVec]

end Generic

section Lower

variable {R : Type*} [CommRing R]

/-- $\Gamma_0(I) = \{g \in \mathrm{GL}_2(R) : g_{10} \in I\}$. -/
def lowerSub (I : Ideal R) : Subgroup (Matrix (Fin 2) (Fin 2) R)ˣ where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ I}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at hg hh ⊢
    exact I.add_mem (I.mul_mem_right _ hg) (I.mul_mem_left _ hh)
  one_mem' := by simp
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
    exact I.mul_mem_left _ (I.neg_mem hg)

theorem mem_lowerSub {I : Ideal R} {g : (Matrix (Fin 2) (Fin 2) R)ˣ} :
    g ∈ lowerSub I ↔ (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ I := Iff.rfl

end Lower

section Generic

variable {R : Type*} [CommRing R] [IsLocalRing R]

attribute [local instance] actV

/-- The reduction of $g v_0$, $v_0 = (1, 0)$. -/
theorem smul_v0 (I : Ideal R) (g : (Matrix (Fin 2) (Fin 2) R)ˣ) :
    g • (![1, 0] : Fin 2 → R ⧸ I) =
      ![Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) R) 0 0),
        Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) R) 1 0)] := by
  change redM I g *ᵥ ![1, 0] = _
  ext i
  fin_cases i <;> simp [redM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem stabilizer_le_lowerSub (I : Ideal R) :
    MulAction.stabilizer (Matrix (Fin 2) (Fin 2) R)ˣ (![1, 0] : Fin 2 → R ⧸ I) ≤ lowerSub I := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff, smul_v0] at hg
  have := congrFun hg 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

/-- Orbit of $v_0$ under $\mathrm{GL}_2(R)$: the unimodular vectors. -/
theorem orbit_v0 {I : Ideal R} (hI : I ≤ IsLocalRing.maximalIdeal R) :
    MulAction.orbit (Matrix (Fin 2) (Fin 2) R)ˣ (![1, 0] : Fin 2 → R ⧸ I) =
      {v | IsUnit (v 0) ∨ IsUnit (v 1)} := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    have e0 : (g • (![1, 0] : Fin 2 → R ⧸ I)) 0 =
        Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) R) 0 0) := by rw [smul_v0]; rfl
    have e1 : (g • (![1, 0] : Fin 2 → R ⧸ I)) 1 =
        Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) R) 1 0) := by rw [smul_v0]; rfl
    show IsUnit ((g • (![1, 0] : Fin 2 → R ⧸ I)) 0) ∨ IsUnit ((g • (![1, 0] : Fin 2 → R ⧸ I)) 1)
    rw [e0, e1, isUnit_mk_iff hI, isUnit_mk_iff hI]
    by_contra hcon
    push Not at hcon
    have hd := Matrix.isUnits_det_units g
    rw [Matrix.det_fin_two] at hd
    have h0 : (g : Matrix (Fin 2) (Fin 2) R) 0 0 ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).2 hcon.1
    have h1 : (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).2 hcon.2
    have : (g : Matrix (Fin 2) (Fin 2) R) 0 0 * (g : Matrix (Fin 2) (Fin 2) R) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) R) 0 1 * (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∈
        IsLocalRing.maximalIdeal R :=
      Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h0) (Ideal.mul_mem_left _ _ h1)
    exact (IsLocalRing.mem_maximalIdeal _).1 this hd
  · intro hv
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v 0)
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (v 1)
    rcases hv with h | h
    · rw [← ha, isUnit_mk_iff hI] at h
      refine ⟨mkUnit a 0 c 1 (by simpa using h), ?_⟩
      beta_reduce
      rw [smul_v0, mkUnit_val]
      ext i; fin_cases i <;> simp [ha, hc]
    · rw [← hc, isUnit_mk_iff hI] at h
      refine ⟨mkUnit a 1 c 0 (by simpa using h.neg), ?_⟩
      beta_reduce
      rw [smul_v0, mkUnit_val]
      ext i; fin_cases i <;> simp [ha, hc]

/-- Orbit of $v_0$ under $\Gamma_0(I)$. -/
theorem orbit_v0_lowerSub {I : Ideal R} (hI : I ≤ IsLocalRing.maximalIdeal R) :
    MulAction.orbit (lowerSub I) (![1, 0] : Fin 2 → R ⧸ I) =
      (fun a : R ⧸ I => (![a, 0] : Fin 2 → R ⧸ I)) '' {a | IsUnit a} := by
  ext v
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    have e1 : (⟨g, hg⟩ : lowerSub I) • (![1, 0] : Fin 2 → R ⧸ I) = g • ![1, 0] := rfl
    beta_reduce
    rw [e1, smul_v0]
    refine ⟨Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) R) 0 0), ?_, ?_⟩
    · show IsUnit _
      rw [isUnit_mk_iff hI]
      by_contra hcon
      have hd := Matrix.isUnits_det_units g
      rw [Matrix.det_fin_two] at hd
      have h0 : (g : Matrix (Fin 2) (Fin 2) R) 0 0 ∈ IsLocalRing.maximalIdeal R :=
        (IsLocalRing.mem_maximalIdeal _).2 hcon
      have h1 : (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ IsLocalRing.maximalIdeal R := hI hg
      have : (g : Matrix (Fin 2) (Fin 2) R) 0 0 * (g : Matrix (Fin 2) (Fin 2) R) 1 1 -
          (g : Matrix (Fin 2) (Fin 2) R) 0 1 * (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∈
          IsLocalRing.maximalIdeal R :=
        Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h0) (Ideal.mul_mem_left _ _ h1)
      exact (IsLocalRing.mem_maximalIdeal _).1 this hd
    · have : Ideal.Quotient.mk I ((g : Matrix (Fin 2) (Fin 2) R) 1 0) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 hg
      rw [this]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hr : IsUnit r := (isUnit_mk_iff hI r).1 ha
    have hh : IsUnit (r * 1 - 0 * 0) := by simpa using hr
    refine ⟨⟨mkUnit r 0 0 1 hh, ?_⟩, ?_⟩
    · show ((mkUnit r 0 0 1 hh : (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ I
      rw [mkUnit_val]; simp
    · show mkUnit r 0 0 1 hh • (![1, 0] : Fin 2 → R ⧸ I) = _
      rw [smul_v0, mkUnit_val]
      ext i; fin_cases i <;> simp

/-- $\#(R/I) = \#k \cdot \#\{\text{nonunits of } R/I\}$ for $I \subseteq \mathfrak m$, $k = R/\mathfrak m$. -/
theorem card_eq_mul_ncard_nonunit {I : Ideal R} (hI : I ≤ IsLocalRing.maximalIdeal R) :
    Nat.card (R ⧸ I) = Nat.card (IsLocalRing.ResidueField R) * {a : R ⧸ I | ¬ IsUnit a}.ncard := by
  let ψ : (R ⧸ I) →+* IsLocalRing.ResidueField R :=
    Ideal.Quotient.lift I (IsLocalRing.residue R)
      (fun a ha => (IsLocalRing.residue_eq_zero_iff a).2 (hI ha))
  have hs : Function.Surjective ψ := fun y => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk I r, by simp [ψ]; rfl⟩
  have hk : {a : R ⧸ I | ¬ IsUnit a} = (ψ.toAddMonoidHom.ker : Set (R ⧸ I)) := by
    ext a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp [ψ, isUnit_mk_iff hI, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      nonunits]
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.toAddMonoidHom.ker,
    ← Nat.card_coe_set_eq, hk]
  congr 1
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ.toAddMonoidHom hs).toEquiv

/-- The count identity: with $T$ the number of units and $N$ the number of nonunits of $R/I$,
$T\,[\mathrm{GL}_2(R):\Gamma_0(I)] + N^2 = (T+N)^2$. -/
theorem lowerSub_index_eq {I : Ideal R} (hI : I ≤ IsLocalRing.maximalIdeal R) [Finite (R ⧸ I)] :
    {a : R ⧸ I | IsUnit a}.ncard * (lowerSub I).index + {a : R ⧸ I | ¬ IsUnit a}.ncard ^ 2 =
      Nat.card (R ⧸ I) ^ 2 := by
  set S := MulAction.stabilizer (Matrix (Fin 2) (Fin 2) R)ˣ (![1, 0] : Fin 2 → R ⧸ I) with hS
  have h1 : S.index = {v : Fin 2 → R ⧸ I | IsUnit (v 0) ∨ IsUnit (v 1)}.ncard := by
    rw [hS, MulAction.index_stabilizer, orbit_v0 hI]
  have h2 : S.relIndex (lowerSub I) = {a : R ⧸ I | IsUnit a}.ncard := by
    rw [Subgroup.relIndex, hS, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer,
      orbit_v0_lowerSub hI]
    exact Set.ncard_image_of_injective _ (fun a b h => by simpa using congrFun h 0)
  have h3 := Subgroup.relIndex_mul_index (stabilizer_le_lowerSub I)
  have h4 : {v : Fin 2 → R ⧸ I | IsUnit (v 0) ∨ IsUnit (v 1)}ᶜ.ncard =
      {a : R ⧸ I | ¬ IsUnit a}.ncard ^ 2 := by
    have : {v : Fin 2 → R ⧸ I | IsUnit (v 0) ∨ IsUnit (v 1)}ᶜ =
        (fun p : (R ⧸ I) × (R ⧸ I) => (![p.1, p.2] : Fin 2 → R ⧸ I)) ''
          ({a : R ⧸ I | ¬ IsUnit a} ×ˢ {a : R ⧸ I | ¬ IsUnit a}) := by
      ext v
      constructor
      · intro hv
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_or] at hv
        exact ⟨(v 0, v 1), hv, by ext i; fin_cases i <;> rfl⟩
      · rintro ⟨p, hp, rfl⟩
        simpa [not_or] using hp
    rw [this, Set.ncard_image_of_injective, Set.ncard_prod, sq]
    intro p p' h
    exact Prod.ext (by simpa using congrFun h 0) (by simpa using congrFun h 1)
  have h5 := Set.ncard_add_ncard_compl {v : Fin 2 → R ⧸ I | IsUnit (v 0) ∨ IsUnit (v 1)}
  rw [h4, Nat.card_pi, Fin.prod_univ_two, ← sq, ← h1, ← h3, h2] at h5
  exact h5

end Generic

/-! ### The Eichler order and its unit group -/

section Eichler

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **$\mathcal O_0(\pi^e) \subseteq \mathrm M_2(R)$:** the standard Eichler order of level $\pi^e$ is contained in the
maximal order $\mathrm M_2(R) \subseteq \mathrm M_2(K)$. -/
theorem stdEichlerOrder_le_matOrder (π : R) (e : ℕ) :
    stdEichlerOrder R K π e ≤ matOrder R K :=
  fun _ hx => mem_matOrder.2 hx.1

/-- $\mathrm M_2(R) \cong \mathrm M_2(R)\subseteq \mathrm M_2(K)$ as $R$-algebras (entrywise `algebraMap`). -/
def toMatOrder (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    Matrix (Fin 2) (Fin 2) R ≃ₐ[R] matOrder R K :=
  AlgEquiv.ofInjective (AlgHom.mapMatrix (Algebra.ofId R K))
    (fun a b h => by
      ext i j
      exact IsFractionRing.injective R K (congrFun (congrFun h i) j))

theorem toMatOrder_val (g : Matrix (Fin 2) (Fin 2) R) :
    ((toMatOrder R K g : matOrder R K) : Matrix (Fin 2) (Fin 2) K) = g.map (algebraMap R K) := rfl

/-- **The unit group of $\mathcal O_0(\pi^e)$ inside $\mathrm{GL}_2(R)$:** under
$\mathrm{GL}_2(R) \cong \mathrm M_2(R)^\times$, the units of $\mathcal O_0(\pi^e)$ are
$\{g \in \mathrm{GL}_2(R) : g_{10} \in \pi^eR\}$. -/
theorem comap_range_units (π : R) (e : ℕ) :
    (Units.map (Subalgebra.inclusion (stdEichlerOrder_le_matOrder (K := K) π e)).toMonoidHom).range.comap
        (Units.mapEquiv (toMatOrder R K).toRingEquiv.toMulEquiv).toMonoidHom =
      lowerSub (Ideal.span {π ^ e}) := by
  ext g
  rw [Subgroup.mem_comap]
  constructor
  · rintro ⟨u, hu⟩
    have h1 := congrArg (fun w : (matOrder R K)ˣ => ((w : matOrder R K) : Matrix (Fin 2) (Fin 2) K)) hu
    simp only [Units.coe_map] at h1
    obtain ⟨-, r, hr⟩ := (u : stdEichlerOrder R K π e).2
    have h2 : ((u : stdEichlerOrder R K π e) : Matrix (Fin 2) (Fin 2) K) 1 0 =
        algebraMap R K ((g : Matrix (Fin 2) (Fin 2) R) 1 0) := by
      have := congrFun (congrFun h1 1) 0
      exact this
    rw [hr] at h2
    have h3 := IsFractionRing.injective R K h2
    rw [mem_lowerSub, ← h3]
    exact Ideal.mem_span_singleton'.2 ⟨r, mul_comm _ _⟩
  · intro hg
    have key : ∀ h : (Matrix (Fin 2) (Fin 2) R)ˣ, h ∈ lowerSub (Ideal.span {π ^ e}) →
        ((h : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K)) ∈ stdEichlerOrder R K π e := by
      intro h hh
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (mem_lowerSub.1 hh)
      refine ⟨fun i j => ⟨(h : Matrix (Fin 2) (Fin 2) R) i j, rfl⟩, r, ?_⟩
      show algebraMap R K ((h : Matrix (Fin 2) (Fin 2) R) 1 0) = _
      rw [← hr, mul_comm]
    let u : (stdEichlerOrder R K π e)ˣ :=
      { val := ⟨_, key g hg⟩
        inv := ⟨_, key g⁻¹ ((lowerSub _).inv_mem hg)⟩
        val_inv := by
          apply Subtype.ext
          change (g : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) *
            ((g⁻¹ : (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) = 1
          rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
        inv_val := by
          apply Subtype.ext
          change ((g⁻¹ : (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) *
            (g : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) = 1
          rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)] }
    exact ⟨u, Units.ext (Subtype.ext rfl)⟩

theorem index_range_units_eq (π : R) (e : ℕ) :
    (Units.map (Subalgebra.inclusion (stdEichlerOrder_le_matOrder (K := K) π e)).toMonoidHom).range.index =
      (lowerSub (Ideal.span {π ^ e})).index := by
  rw [← comap_range_units (K := K) π e, Subgroup.index_comap_of_surjective]
  exact (Units.mapEquiv (toMatOrder R K).toRingEquiv.toMulEquiv).surjective

/-- **Level $\pi^0 = 1$:** $\mathcal O_0(1) = \mathrm M_2(R)$ has unit index $1$. -/
theorem index_units_stdEichlerOrder_zero (π : R) :
    (Units.map (Subalgebra.inclusion (stdEichlerOrder_le_matOrder (K := K) π 0)).toMonoidHom).range.index = 1 := by
  rw [index_range_units_eq]
  refine Subgroup.index_eq_one.2 ?_
  ext g
  simp only [Subgroup.mem_top, iff_true]
  rw [mem_lowerSub, pow_zero, Ideal.span_singleton_one]
  trivial

end Eichler

section Final

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {π : R}

/-- **The unit index of the standard Eichler order** (Voight 2021, Lemma 26.6.7 for Eichler orders, and 23.4.12):
for $R$ a discrete valuation ring with uniformizer $\pi$, finite residue field of size $q$, and level $\pi^e$, $e \ge 1$,
$$[\mathrm{GL}_2(R) : \mathcal O_0(\pi^e)^\times] = q^{e-1}(q+1),$$
where $\mathcal O_0(\pi^e)^\times \subseteq \mathrm M_2(R)^\times = \mathrm{GL}_2(R)$ is the unit group of the standard Eichler
order. -/
@[kb "voight2021" "Lemma 26.6.7, p. 446; 23.4.12, p. 384"]
theorem index_units_stdEichlerOrder (hπ : Irreducible π) [Finite (IsLocalRing.ResidueField R)] {e : ℕ}
    (he : 1 ≤ e) :
    (Units.map (Subalgebra.inclusion (stdEichlerOrder_le_matOrder (K := K) π e)).toMonoidHom).range.index =
      QuadFormsKB.LocalDensity.DVR.q R ^ (e - 1) * (QuadFormsKB.LocalDensity.DVR.q R + 1) := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [index_range_units_eq, Nat.add_sub_cancel]
  have hI : Ideal.span {π ^ (e' + 1)} ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_mem_of_mem _
      (by rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π) _ (Nat.succ_pos _)
  have hA : Nat.card (R ⧸ Ideal.span {π ^ (e' + 1)}) = q R ^ (e' + 1) := natCard_quot_pow π hπ _
  have hq : 0 < q R := Nat.card_pos
  have hq2 : 2 ≤ q R := Finite.one_lt_card
  have : Finite (R ⧸ Ideal.span {π ^ (e' + 1)}) :=
    Nat.finite_of_card_ne_zero (by rw [hA]; positivity)
  have h1 := lowerSub_index_eq hI
  have h2 := card_eq_mul_ncard_nonunit hI
  have h3 : {a : R ⧸ Ideal.span {π ^ (e' + 1)} | IsUnit a}.ncard +
      {a : R ⧸ Ideal.span {π ^ (e' + 1)} | ¬ IsUnit a}.ncard = Nat.card (R ⧸ Ideal.span {π ^ (e' + 1)}) :=
    Set.ncard_add_ncard_compl {a : R ⧸ Ideal.span {π ^ (e' + 1)} | IsUnit a}
  rw [hA] at h1 h2 h3
  change q R ^ (e' + 1) = q R * _ at h2
  have hN : {a : R ⧸ Ideal.span {π ^ (e' + 1)} | ¬ IsUnit a}.ncard = q R ^ e' :=
    Nat.eq_of_mul_eq_mul_left hq (by rw [← h2, pow_succ'])
  rw [hN] at h1 h3
  rw [show q R ^ (e' + 1) = q R * q R ^ e' from pow_succ' _ _] at h1 h3
  have hx : 0 < q R ^ e' := pow_pos hq _
  generalize {a : R ⧸ Ideal.span {π ^ (e' + 1)} | IsUnit a}.ncard = T at h1 h3
  generalize (lowerSub (Ideal.span {π ^ (e' + 1)})).index = idx at h1 ⊢
  generalize q R ^ e' = x at *
  generalize q R = Q at *
  have hT : 0 < T := by nlinarith
  refine Nat.eq_of_mul_eq_mul_left hT ?_
  have e1 : x * (T + x) = x * (Q * x) := by rw [h3]
  have e2 : x * Q * (T + x) = x * Q * (Q * x) := by rw [h3]
  have e3 : T * (x * (Q + 1)) + x ^ 2 = (Q * x) ^ 2 := by nlinarith [e1, e2]
  exact Nat.add_right_cancel (show T * idx + x ^ 2 = T * (x * (Q + 1)) + x ^ 2 by rw [h1, e3])

end Final

end QuadFormsKB.Voight.Wave4
