/-
# Cassels, Appendix B, §2, Lemma 2.1 for $D > 0$, part c: the congruence conditions and the limit

Counting the lattice points of the hyperbolic sector with the congruence conditions $p \mid f(w)$, $p \in P$ (sublattices),
inclusion-exclusion over the primes dividing $D$, and the proof of `Lemma21Pos`.
-/
import QuadFormsKB.Literature.Cassels.AppB.Lemma21Pos530b

open Filter Topology Matrix MeasureTheory
open scoped Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

namespace Lemma21Pos530

open QuadFormsKB.Binary Lemma21Aux

section Sub2

/-- Helper: **the real coordinates of $Az$ for an integer matrix $A$** are those of $z$ for the matrix $B A$. -/
theorem yv_mulVec_int (f : BinQF) (A : Matrix (Fin 2) (Fin 2) ℤ) (z : Fin 2 → ℤ) :
    yv f (A *ᵥ z) = ((Bm f) * A.map (Int.cast : ℤ → ℝ)).mulVec (fun i => (z i : ℝ)) := by
  rw [← Matrix.mulVec_mulVec]
  unfold yv
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Helper: an integer matrix of nonzero determinant acts injectively on $\mathbb Z^2$. -/
theorem mulVec_inj_int (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) :
    Function.Injective (fun z : Fin 2 → ℤ => A *ᵥ z) := by
  intro z z' h
  have h' := congrArg (Matrix.adjugate A).mulVec h
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h'
  ext i
  have := congrFun h' i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hA this

/-- Helper: **the number of lattice points of the sector in a sublattice $A\mathbb Z^2$.** For $D > 0$, $a \ne 0$,
$\eta > 1$ and an integer matrix $A$ of nonzero determinant, the number of $w \in A\mathbb Z^2$ with
$(L_1, L_2)(w) \in$ `sectorCone η` and $L_1L_2(w) \le c$, divided by $c$, tends to $\log\eta/(\sqrt D\,|\det A|)$.
Arguments: `f`, `hD`, `ha`, `η`, `hη : 1 < η`, `A`, `hA : A.det ≠ 0`. -/
theorem sublattice_count (f : BinQF) (hD : 0 < f.disc) (ha : f.a ≠ 0) {η : ℝ} (hη : 1 < η)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) :
    Tendsto (fun M : ℕ => (Nat.card {w : Fin 2 → ℤ // (∃ z : Fin 2 → ℤ, w = A *ᵥ z) ∧ yv f w ∈ sectorCone η ∧
      hyp (yv f w) ≤ (M : ℝ)} : ℝ) / M) atTop (𝓝 (Real.log η / (sD f * (A.det.natAbs : ℝ)))) := by
  have hs0 : 0 < sD f := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have hdetR : ((Bm f) * A.map (Int.cast : ℤ → ℝ)).det = sD f * (A.det : ℝ) := by
    rw [Matrix.det_mul, det_Bm f ha]
    congr 1
    have := (Int.castRingHom ℝ).map_det A
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hAR : (A.det : ℝ) ≠ 0 := by exact_mod_cast hA
  have hB : ((Bm f) * A.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [hdetR]; exact mul_ne_zero hs0.ne' hAR
  have h := (cone_count hη _ hB).comp tendsto_natCast_atTop_atTop
  have habs : |((Bm f) * A.map (Int.cast : ℤ → ℝ)).det| = sD f * (A.det.natAbs : ℝ) := by
    rw [hdetR, abs_mul, abs_of_pos hs0, Nat.cast_natAbs, Int.cast_abs]
  rw [habs] at h
  refine h.congr (fun M => ?_)
  simp only [Function.comp_apply]
  congr 1
  norm_cast
  refine (Nat.card_congr (Equiv.ofBijective (fun z : {z : Fin 2 → ℤ //
      ((Bm f) * A.map (Int.cast : ℤ → ℝ)).mulVec (fun i => (z i : ℝ)) ∈ sectorCone η ∧
      hyp (((Bm f) * A.map (Int.cast : ℤ → ℝ)).mulVec (fun i => (z i : ℝ))) ≤ (M : ℝ)} =>
      (⟨A *ᵥ z.1, ⟨z.1, rfl⟩, by rw [yv_mulVec_int]; exact z.2.1, by rw [yv_mulVec_int]; exact z.2.2⟩ :
        {w : Fin 2 → ℤ // (∃ z : Fin 2 → ℤ, w = A *ᵥ z) ∧ yv f w ∈ sectorCone η ∧
          hyp (yv f w) ≤ (M : ℝ)})) ⟨?_, ?_⟩))
  · intro z z' hzz
    exact Subtype.ext (mulVec_inj_int A hA (congrArg Subtype.val hzz))
  · rintro ⟨w, ⟨z, rfl⟩, h1, h2⟩
    refine ⟨⟨z, by rw [← yv_mulVec_int]; exact h1, by rw [← yv_mulVec_int]; exact h2⟩, rfl⟩

/-- Helper: **lattice points of the sector with the congruence conditions $p \mid f(w)$, $p \in P$.** The set
$\{w \in \mathbb Z^2 : (L_1, L_2)(w) \in \text{sector},\ L_1L_2(w) \le M,\ p \mid f(w)\ \forall p \in P\}$.
Arguments: `f` the form, `η` the unit, `P` the finite set of primes, `M` the bound. -/
def Pset (f : BinQF) (η : ℝ) (P : Finset ℕ) (M : ℕ) : Set (Fin 2 → ℤ) :=
  {w | yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ (M : ℝ) ∧ ∀ p ∈ P, (p : ℤ) ∣ Fint f.a f.b f.c w}

/-- Helper: **the density of the sector lattice points with $p \mid f(w)$ for $p \in P$** is
$\log\eta/(\sqrt D\prod_{p \in P}p)$ (for a set $P$ of primes dividing $D$, via the sublattice of index $\prod_{p \in P}p$
of `sublattice_exists`). Arguments: `f` the form, `hprim` primitivity, `hD`, `ha`, `hη : 1 < η`, `P`, `hP` that the
elements of $P$ divide the discriminant. -/
theorem pset_tendsto (f : BinQF) (hprim : f.IsPrimitive) (hD : 0 < f.disc) (ha : f.a ≠ 0) {η : ℝ} (hη : 1 < η)
    (P : Finset ℕ) (hP : P ⊆ f.disc.natAbs.primeFactors) :
    Tendsto (fun M : ℕ => (Nat.card (Pset f η P M) : ℝ) / M) atTop
      (𝓝 (Real.log η / (sD f * ∏ p ∈ P, (p : ℝ)))) := by
  have hSp : ∀ p ∈ f.disc.natAbs.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hDd : ∀ p ∈ f.disc.natAbs.primeFactors, (p : ℤ) ∣ f.b ^ 2 - 4 * f.a * f.c := by
    intro p hp
    have : (p : ℤ) ∣ f.disc := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
    simpa [BinQF.disc] using this
  have hpr : ∀ p ∈ f.disc.natAbs.primeFactors, ¬ ((p : ℤ) ∣ f.a ∧ (p : ℤ) ∣ f.b ∧ (p : ℤ) ∣ f.c) := by
    rintro p hp ⟨h1, h2, h3⟩
    have hu := hprim (p : ℤ) h1 h2 h3
    have hp1 := (hSp p hp).one_lt
    rw [Int.isUnit_iff] at hu
    omega
  obtain ⟨A, hAdet, hA⟩ := sublattice_exists f.a f.b f.c _ hSp hDd hpr P hP
  have hprodpos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hSp p (hP hp)).pos)
  have hA0 : A.det ≠ 0 := by
    intro h
    rw [h] at hAdet
    simp at hAdet
    omega
  have h := sublattice_count f hD ha hη A hA0
  rw [hAdet, Nat.cast_prod] at h
  refine h.congr (fun M => ?_)
  have e : Nat.card {w : Fin 2 → ℤ // (∃ z : Fin 2 → ℤ, w = A *ᵥ z) ∧ yv f w ∈ sectorCone η ∧
      hyp (yv f w) ≤ (M : ℝ)} = Nat.card (Pset f η P M) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))
    show _ ↔ (yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ (M : ℝ) ∧ ∀ p ∈ P, (p : ℤ) ∣ Fint f.a f.b f.c w)
    rw [hA w]
    tauto
  rw [e]

/-- Helper: **inclusion-exclusion for a finite set of conditions:**
$[\forall p \in S,\ \neg d(p)] = \sum_{P \subseteq S}(-1)^{|P|}[\forall p \in P,\ d(p)]$. Arguments: `S` the finite set,
`d` the predicate. -/
theorem incl_excl (S : Finset ℕ) (d : ℕ → Prop) [DecidablePred d] :
    (if ∀ p ∈ S, ¬ d p then (1 : ℤ) else 0) =
      ∑ P ∈ S.powerset, (-1 : ℤ) ^ P.card * (if ∀ p ∈ P, d p then 1 else 0) := by
  have h1 : (if ∀ p ∈ S, ¬ d p then (1 : ℤ) else 0) =
      ∏ p ∈ S, ((-1 : ℤ) * (if d p then 1 else 0) + 1) := by
    rw [← Finset.prod_boole]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    split_ifs <;> simp_all
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_boole]

/-- Helper: the Euler factor as an inclusion-exclusion sum,
$\prod_{p \in S}(1 - 1/p) = \sum_{P \subseteq S}(-1)^{|P|}/\prod_{p \in P}p$. -/
theorem euler_expand (S : Finset ℕ) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ)) = ∑ P ∈ S.powerset, (-1 : ℝ) ^ P.card * (1 / ∏ p ∈ P, (p : ℝ)) := by
  have h1 : ∏ p ∈ S, (1 - 1 / (p : ℝ)) = ∏ p ∈ S, ((-1 : ℝ) * (1 / (p : ℝ)) + 1) := by
    refine Finset.prod_congr rfl (fun p _ => ?_)
    ring
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const]
  simp only [one_div, Finset.prod_inv_distrib]

/-- Helper: **inclusion-exclusion for the count** $A^*_f(M)$: with $S$ the set of primes dividing $D$,
$A^*_f(M) = \sum_{P \subseteq S}(-1)^{|P|}\,\#\mathrm{Pset}(P, M)$ (in $\mathbb Z$). Arguments as for
`orbitCountSum_eq`. -/
theorem orbitCountSum_incl_excl (f : BinQF) (hprim : f.IsPrimitive) (ha : f.a ≠ 0) (hD : 0 < f.disc) {η : ℝ}
    (hη : IsNormOneFundamentalUnit f.disc η) (M : ℕ) :
    (orbitCountSum f M : ℤ) = ∑ P ∈ f.disc.natAbs.primeFactors.powerset,
      (-1 : ℤ) ^ P.card * (Nat.card (Pset f η P M) : ℤ) := by
  classical
  rw [orbitCountSum_eq f hprim ha hD hη M]
  have hfin := finite_sector f hD ha hη.1 (M : ℝ)
  set W := hfin.toFinset with hW
  have hcount : ∀ Q : (Fin 2 → ℤ) → Prop, (∀ w, Q w → w ∈ W) →
      Nat.card {w : Fin 2 → ℤ // Q w} = (W.filter Q).card := by
    intro Q hQ
    have : {w : Fin 2 → ℤ | Q w} = ↑(W.filter Q) := by
      ext w
      simp only [Set.mem_ofPred_eq, Finset.coe_filter]
      exact ⟨fun h => ⟨hQ w h, h⟩, fun h => h.2⟩
    show Nat.card ↥{w : Fin 2 → ℤ | Q w} = _
    rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hWmem : ∀ w, yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ (M : ℝ) → w ∈ W := by
    intro w hw
    rw [hW, Set.Finite.mem_toFinset]
    exact hw
  have hWf : ∀ (Q : (Fin 2 → ℤ) → Prop) [DecidablePred Q],
      (((W.filter (fun w => yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ (M : ℝ) ∧ Q w)).card : ℕ) : ℤ) =
        ∑ w ∈ W, (if Q w then (1 : ℤ) else 0) := by
    intro Q _
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun w (hw : w ∈ W) => ?_)
    have : yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ (M : ℝ) := by
      rw [hW, Set.Finite.mem_toFinset] at hw; exact hw
    simp [this]
  set S := f.disc.natAbs.primeFactors with hS
  rw [hcount (fun w => yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ (M : ℝ) ∧ ∀ p ∈ S, ¬ (p : ℤ) ∣ Fint f.a f.b f.c w)
    (fun w hw => hWmem w ⟨hw.1, hw.2.1⟩)]
  have hP : ∀ P : Finset ℕ, (Nat.card (Pset f η P M) : ℤ) = ∑ w ∈ W,
      (if ∀ p ∈ P, (p : ℤ) ∣ Fint f.a f.b f.c w then (1 : ℤ) else 0) := by
    intro P
    have := hcount (fun w => yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ (M : ℝ) ∧ ∀ p ∈ P,
      (p : ℤ) ∣ Fint f.a f.b f.c w) (fun w hw => hWmem w ⟨hw.1, hw.2.1⟩)
    have h2 : Nat.card (Pset f η P M) = _ := this
    rw [h2]
    convert hWf (fun w => ∀ p ∈ P, (p : ℤ) ∣ Fint f.a f.b f.c w) using 4
  simp only [hP]
  calc _ = ∑ w ∈ W, (if ∀ p ∈ S, ¬ (p : ℤ) ∣ Fint f.a f.b f.c w then (1 : ℤ) else 0) := by
        convert hWf (fun w => ∀ p ∈ S, ¬ (p : ℤ) ∣ Fint f.a f.b f.c w) using 4
    _ = ∑ w ∈ W, ∑ P ∈ S.powerset, (-1 : ℤ) ^ P.card *
          (if ∀ p ∈ P, (p : ℤ) ∣ Fint f.a f.b f.c w then 1 else 0) :=
        Finset.sum_congr rfl (fun w _ => incl_excl S (fun p => (p : ℤ) ∣ Fint f.a f.b f.c w))
    _ = _ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm

end Sub2

section Final

/-- Helper: **the limit of Lemma 2.1 for $D > 0$ in terms of the form.** For a primitive integral binary form $f$ of
discriminant $D > 0$ with $a \ne 0$ and $\eta$ the fundamental unit of norm $+1$,
$A^*_f(M)/M \to \frac{\log\eta}{\sqrt D}\prod_{p \mid D}(1 - p^{-1})$. Arguments: `f`, `hprim`, `ha`, `hD`, `hη`. -/
theorem lemma21_pos_of (f : BinQF) (hprim : f.IsPrimitive) (ha : f.a ≠ 0) (hD : 0 < f.disc) {η : ℝ}
    (hη : IsNormOneFundamentalUnit f.disc η) :
    Tendsto (fun M : ℕ => (orbitCountSum f M : ℝ) / M) atTop
      (𝓝 (Real.log η / Real.sqrt (f.disc : ℝ) * ∏ p ∈ f.disc.natAbs.primeFactors, (1 - 1 / (p : ℝ)))) := by
  classical
  set S := f.disc.natAbs.primeFactors with hS
  have key : ∀ M : ℕ, (orbitCountSum f M : ℝ) / M =
      ∑ P ∈ S.powerset, (-1 : ℝ) ^ P.card * ((Nat.card (Pset f η P M) : ℝ) / M) := by
    intro M
    have h := orbitCountSum_incl_excl f hprim ha hD hη M
    have h' : (orbitCountSum f M : ℝ) =
        ∑ P ∈ S.powerset, (-1 : ℝ) ^ P.card * (Nat.card (Pset f η P M) : ℝ) := by exact_mod_cast h
    rw [h', Finset.sum_div]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    ring
  have hlim := tendsto_finsetSum S.powerset (fun P hP =>
    (pset_tendsto f hprim hD ha hη.1 P (Finset.mem_powerset.mp hP)).const_mul ((-1 : ℝ) ^ P.card))
  simp only [← key] at hlim
  convert hlim using 2
  rw [euler_expand, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  unfold sD
  ring

/-- Helper: **the fundamental unit forces $D > 0$.** If `IsNormOneFundamentalUnit D η` then $D > 0$ (for $D \le 0$ the
real square root is $0$, so $\eta = t/2 > 1$ gives $t \ge 3$, contradicting $t^2 = 4 + Du^2 \le 4$). -/
theorem pos_of_unit {D : ℤ} {η : ℝ} (hη : IsNormOneFundamentalUnit D η) : 0 < D := by
  by_contra hD
  push Not at hD
  obtain ⟨h1, ⟨t, u, hu, htu, hηeq⟩, -⟩ := hη
  have hs : Real.sqrt (D : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by exact_mod_cast hD)
  rw [hs, mul_zero, add_zero] at hηeq
  have ht : (2 : ℝ) < t := by rw [hηeq] at h1; linarith
  have ht' : (2 : ℤ) < t := by exact_mod_cast ht
  nlinarith [mul_nonneg (neg_nonneg.mpr hD) (sq_nonneg (u : ℤ))]

end Final

end Lemma21Pos530

open QuadFormsKB.Binary

/-- **Cassels, Appendix B, §2, Lemma 2.1, case $D > 0$ (pp. 371–372), proved (unconditional).** For a fundamental
discriminant $D$ (`IsQuadDisc D`), every integral binary form $f$ of discriminant $D$ and the fundamental unit $\eta$ of
norm $+1$ (`IsNormOneFundamentalUnit D η`; such $\eta$ exists only for $D > 0$),
$$\lim_{M \to \infty} M^{-1}A^*_f(M) = \frac{\log\eta}{\sqrt D}\prod_{p \mid D}\big(1 - p^{-1}\big).$$
Proof as in the book ("similar to $D < 0$"): the proper automorphs are $\pm\gamma_0^k$ with $\gamma_0$ acting on the
real linear forms $L_1, L_2$ ($f = L_1L_2$) by $(\eta, \eta^{-1})$ (`autSL_data`, `exists_autSL_of_pell`), so the half-open
hyperbolic sector `sectorCone η` is a fundamental domain (`sector_unique`, `sector_exists`); $A^*_f(M)$ is the number of
lattice points of the sector with $f \le M$ and $(f(w), D) = 1$ (`orbitCountSum_eq`); the sector $\{f \le M\}$ has area
$M\log\eta/\sqrt D$ (`volume_sectorSet`), and the congruence conditions are handled by inclusion-exclusion over the
sublattices $\{p \mid f(w),\ p \in P\}$ of index $\prod_{p \in P}p$ (`orbitCountSum_incl_excl`, `pset_tendsto`).
Argument: `D` the fundamental discriminant. -/
@[kb "cassels1978" "App. B, §2, Lemma 2.1 (D > 0), (2.10), pp. 371–372"]
theorem lemma21Pos_holds (D : ℤ) [IsQuadDisc D] : Lemma21Pos D := by
  intro f hf η hη
  subst hf
  have hD : 0 < f.disc := Lemma21Pos530.pos_of_unit hη
  have hprim : f.IsPrimitive := Binary.isPrimitive_of_fund (IsQuadDisc.fund (D := f.disc)) rfl
  have ha : f.a ≠ 0 := by
    intro h0
    apply Binary.not_isSquare_of_isQuadDisc (D := f.disc)
    exact ⟨f.b, by simp [BinQF.disc, h0, sq]⟩
  exact Lemma21Pos530.lemma21_pos_of f hprim ha hD hη

/-- **Cassels, Appendix B, §2, Corollary to Lemma 2.1, $D > 0$ (p. 372, (2.12 bis)), unconditional:** for a fundamental
discriminant $D$, every integral binary form $f$ of discriminant $D$ and the fundamental unit $\eta$ of norm $+1$,
$$\lim_{s \to 1+}(s - 1)\sum_{m > 0,\ (m, D) = 1}a^*_f(m)\,m^{-s} = \frac{\log\eta}{\sqrt D}\prod_{p \mid D}\big(1 - p^{-1}\big).$$
Arguments: `D` the fundamental discriminant, `f` with `hf : f.disc = D`, `η` with `hη : IsNormOneFundamentalUnit D η`.
From `lemma21Pos_holds` by partial summation (`cor_lemma_2_1_pos`). -/
@[kb "cassels1978" "App. B, §2, Cor. to Lemma 2.1 (D > 0), (2.12 bis), p. 372"]
theorem cor_lemma_2_1_pos_uncond (D : ℤ) [IsQuadDisc D] (f : BinQF) (hf : f.disc = D) (η : ℝ)
    (hη : IsNormOneFundamentalUnit D η) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' m : ℕ,
      (if 0 < m ∧ Nat.Coprime m f.disc.natAbs then (repOrbitCount f m : ℝ) else 0) * (m : ℝ) ^ (-s))
      (𝓝[>] 1) (𝓝 (Real.log η / Real.sqrt D * coprimeDensity D)) :=
  cor_lemma_2_1_pos D (lemma21Pos_holds D) f hf η hη

end QuadFormsKB.Cassels
