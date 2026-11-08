/-
# Cassels, Chapter 14, §5: Theorem 5.1 with the local groups $\mathcal G_p$

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §3, p. 339 and §5, Theorem 5.1, p. 343.

`Thm51Groups530.lean` realizes the groups $\mathcal G_p = \mathbb Z_p^\times / N$ and $\mathcal G_\infty = \mathbb R^\times / N$
and the homomorphisms $\mathcal G \to \mathcal G_p$, (3.1). Here:

* the Hasse–Minkowski invariant is a character $c_p : \mathcal G_p \to \{\pm 1\}$ of the group $\mathcal G_p$ (the class of
  a form with unit value $w$ has $c_p = (w, D)_p$);
* `globalToLocal D`: the homomorphism (5.2) $\mathcal G \to \prod_{p \mid 2D} \mathcal G_p \times \mathcal G_\infty$;
* `range_eq_ker`: its image is the kernel of $\prod_p c_p$ (`thm_5_1`);
* `thm_5_1_square`, `thm_5_1_nonsquare`: Theorem 5.1, the image is everything if $D$ is a square and has index $2$
  otherwise.

*Deviation (finite product).* Cassels takes the product (5.2) over all $p \le \infty$. Since $\mathcal G_p$ is trivial for
$p \nmid 2D$ (`card_localGroup_of_not_dvd`) the factors with $p \nmid 2D$ contribute nothing, and we take the product
over the finitely many primes dividing $2D$ together with $\infty$, which makes the group a finite product.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Thm51Groups530
import QuadFormsKB.Literature.Hanke2011Structure.DyadicHasseTable

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Composition

open BinQF Binary FormClass Siegel QuadForm HilbertLocal

/-! ### Real forms: the Hasse invariant from a represented value -/

/-- Over $\mathbb R$: a nondegenerate binary form of $-\det H = D$ that represents $u \ne 0$ has $c = (u, D)_\infty$. -/
theorem hasseC_eq_of_represents_real {g : QuadForm ℝ 2} {D : ℝ} (hD : D ≠ 0) (hg : -g.hessian.det = D)
    {u : ℝ} (hu0 : u ≠ 0) (hrep : g.RepresentsIn ℝ u) : hasseC g = hilbertSymbol ℝ u D := by
  have hnd : g.Nondegenerate := nondeg_of_det hD hg
  obtain ⟨α, hα, hiso⟩ := QuadForm.exists_isometric_diag_cons hnd hu0 hrep
  have hiso2 : g.IsometricIn ℝ (QuadForm.diag ![u, -D / (4 * u)]) := by
    have := normal_form_of_diag hg (a := Fin.cons u α) (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hu0
      · simpa using hα j) hiso
    simpa using this
  rw [hasseC_eq_of_isometric_real hnd (hne_diag_two hD hu0) hiso2, PadicClass.hasseVec_two,
    hs_normal_form hilbertSymbol_real_mul_left hu0 hD]

/-! ### The Hasse invariant as a character of $\mathcal G_p$ -/

section Chars

/-- The Hilbert symbol as an element of $\mathbb Z^\times = \{\pm 1\}$. -/
noncomputable def symUnit {K : Type*} [Field K] [CharZero K] (a b : K) : ℤˣ :=
  (Int.isUnit_iff.2 (PadicClass.hs_pm a b)).unit

theorem coe_symUnit {K : Type*} [Field K] [CharZero K] (a b : K) : (symUnit a b : ℤ) = hilbertSymbol K a b := rfl

variable (p : ℕ) [Fact p.Prime] (D : ℤ) [NonzeroDisc D]

/-- Helper: the form $w x^2 + \beta xy + w^{-1} c y^2$ of discriminant $D$ over $\mathbb Z_p$, as a primitive form. -/
noncomputable def localFormOf (w : ℤ_[p]ˣ) : LocalPrimForm p D :=
  ⟨(principalData ℤ_[p] D).unitForm w, Or.inl (by rw [PrinData.unitForm, bq_coeff00]; exact w.isUnit),
    by rw [neg_det_eq_disc2]; exact (principalData ℤ_[p] D).disc2_unitForm w⟩

theorem localCoset_localFormOf (w : ℤ_[p]ˣ) : localCoset p D (localFormOf p D w) = QuotientGroup.mk w :=
  (principalData ℤ_[p] D).cosetOf_unitForm four_ne_zero_padic (halfProp_padic p) w _

/-- **The Hilbert symbol $(\cdot, D)_p$ on units**, a homomorphism $\mathbb Z_p^\times \to \{\pm 1\}$. -/
noncomputable def padicSym : ℤ_[p]ˣ →* ℤˣ where
  toFun u := symUnit ((u : ℤ_[p]) : ℚ_[p]) (D : ℚ_[p])
  map_one' := Units.ext (by
    rw [coe_symUnit]; simp [PadicClass.hs_one_left])
  map_mul' u w := Units.ext (by
    have hD : (D : ℚ_[p]) ≠ 0 := by exact_mod_cast NonzeroDisc.ne_zero (D := D)
    have hu : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := by rw [Ne, PadicInt.coe_eq_zero]; exact u.ne_zero
    have hw : ((w : ℤ_[p]) : ℚ_[p]) ≠ 0 := by rw [Ne, PadicInt.coe_eq_zero]; exact w.ne_zero
    simp only [Units.val_mul, coe_symUnit]
    push_cast
    exact (PadicClass.localHilbertField_padic p).mul_left _ _ _ hu hw hD)

theorem coe_padicSym (u : ℤ_[p]ˣ) :
    (padicSym p D u : ℤ) = hilbertSymbol ℚ_[p] ((u : ℤ_[p]) : ℚ_[p]) (D : ℚ_[p]) := rfl

theorem hasseC_localFormOf (w : ℤ_[p]ˣ) :
    hasseC ((localFormOf p D w).1.map PadicInt.Coe.ringHom) = (padicSym p D w : ℤ) := by
  have hv : (localFormOf p D w).1.eval ![1, 0] = (w : ℤ_[p]) := (principalData ℤ_[p] D).eval_unitForm w
  rcases Hanke2011Structure.hasseC_eq_of_unit_value NonzeroDisc.ne_zero (localFormOf p D w)
    (v := ![1, 0]) with h | h
  · rw [h, hv, coe_padicSym]
  · exact absurd (hv ▸ h) w.ne_zero

theorem padicSym_ker (u : ℤ_[p]ˣ) (hu : u ∈ (principalData ℤ_[p] D).subgroup) : padicSym p D u = 1 := by
  have e : (QuotientGroup.mk u : ℤ_[p]ˣ ⧸ (principalData ℤ_[p] D).subgroup) = QuotientGroup.mk 1 :=
    ((principalData ℤ_[p] D).mk_eq_iff u 1).2 (by simpa using hu)
  have hiso : IsometricGL (localFormOf p D u).1 (localFormOf p D 1).1 :=
    (cosetOf_eq_iff _ four_ne_zero_padic (halfProp_padic p) (disc2_localPrim p D _) (disc2_localPrim p D _)
      (exists_unit_value (localFormOf p D u).2.1) (exists_unit_value (localFormOf p D 1).2.1)).1 (by
      have h1 := localCoset_localFormOf p D u
      have h2 := localCoset_localFormOf p D 1
      unfold localCoset at h1 h2
      rw [h1, h2, e])
  have h3 := Hanke2011Structure.hasseC_eq_of_isometricGL hiso
  rw [hasseC_localFormOf, hasseC_localFormOf] at h3
  have h1 : padicSym p D 1 = 1 := map_one _
  rw [h1] at h3
  exact Units.ext h3

/-- **The Hasse–Minkowski invariant $c_p$ as a character of $\mathcal G_p$** (Cassels, Ch. 14, §5, p. 343–344):
$c_p : \mathcal G_p \to \{\pm 1\}$, $c_p([w]) = (w, D)_p$ for a unit $w$ represented by the form
(`hasseChar_localCoset`). -/
noncomputable def hasseChar : LocalGroup p D →* ℤˣ :=
  QuotientGroup.lift _ (padicSym p D) (fun u hu => (MonoidHom.mem_ker).2 (padicSym_ker p D u hu))

/-- The character `hasseChar` is the Hasse–Minkowski invariant $c_p$ of the $\mathbb Z_p$-class. -/
theorem hasseChar_localCoset (F : LocalPrimForm p D) :
    (hasseChar p D (localCoset p D F) : ℤ) = hasseC (F.1.map PadicInt.Coe.ringHom) := by
  obtain ⟨v, hv⟩ := exists_unit_value F.2.1
  have e : localCoset p D F = QuotientGroup.mk hv.unit :=
    cosetOf_eq _ four_ne_zero_padic (halfProp_padic p) (disc2_localPrim p D F) _ hv
  rw [e, hasseChar, QuotientGroup.lift_mk, coe_padicSym]
  rcases Hanke2011Structure.hasseC_eq_of_unit_value NonzeroDisc.ne_zero F (v := v) with h | h
  · rw [h, IsUnit.unit_spec]
  · exact absurd h hv.ne_zero

/-! #### The real place -/

/-- Helper: the form $w x^2 + \beta xy + w^{-1} c y^2$ over $\mathbb R$. -/
noncomputable def realFormOf (w : ℝˣ) : RealForm D :=
  ⟨(principalData ℝ D).unitForm w, by rw [neg_det_eq_disc2]; exact (principalData ℝ D).disc2_unitForm w⟩

theorem realCoset_realFormOf (w : ℝˣ) : realCoset D (realFormOf D w) = QuotientGroup.mk w :=
  (principalData ℝ D).cosetOf_unitForm (by norm_num) halfProp_real w _

/-- **The Hilbert symbol $(\cdot, D)_\infty$ on real units**, a homomorphism $\mathbb R^\times \to \{\pm 1\}$. -/
noncomputable def realSym : ℝˣ →* ℤˣ where
  toFun u := symUnit ((u : ℝ)) (D : ℝ)
  map_one' := Units.ext (by
    rw [coe_symUnit]; simp [PadicClass.hs_one_left])
  map_mul' u w := Units.ext (by
    have hD : (D : ℝ) ≠ 0 := by exact_mod_cast NonzeroDisc.ne_zero (D := D)
    simp only [Units.val_mul, coe_symUnit]
    exact hilbertSymbol_real_mul_left _ _ _ u.ne_zero w.ne_zero hD)

theorem coe_realSym (u : ℝˣ) : (realSym D u : ℤ) = hilbertSymbol ℝ (u : ℝ) (D : ℝ) := rfl

/-- Helper: the Hasse invariant of a real form of discriminant $D$ is $(F(v), D)_\infty$ for a non-zero value. -/
theorem hasseC_real_of_value (F : RealForm D) {v : Fin 2 → ℝ} (hv : F.1.eval v ≠ 0) :
    hasseC F.1 = hilbertSymbol ℝ (F.1.eval v) (D : ℝ) :=
  hasseC_eq_of_represents_real (by exact_mod_cast NonzeroDisc.ne_zero (D := D)) F.2 hv ⟨v, rfl⟩

theorem realSym_ker (u : ℝˣ) (hu : u ∈ (principalData ℝ D).subgroup) : realSym D u = 1 := by
  have e : (QuotientGroup.mk u : ℝˣ ⧸ (principalData ℝ D).subgroup) = QuotientGroup.mk 1 :=
    ((principalData ℝ D).mk_eq_iff u 1).2 (by simpa using hu)
  have hex := fun w : ℝˣ => exists_isUnit_val_field (realFormOf D w).1
    (by rw [disc2_realForm]; exact_mod_cast NonzeroDisc.ne_zero (D := D))
  have hiso : IsometricGL (realFormOf D u).1 (realFormOf D 1).1 :=
    (cosetOf_eq_iff _ (by norm_num) halfProp_real (disc2_realForm D _) (disc2_realForm D _)
      (hex u) (hex 1)).1 (by
      have h1 := realCoset_realFormOf D u
      have h2 := realCoset_realFormOf D 1
      unfold realCoset at h1 h2
      rw [h1, h2, e])
  obtain ⟨T, hT⟩ := hiso.symm
  have hu0 : (realFormOf D u).1.eval ![1, 0] = (u : ℝ) := (principalData ℝ D).eval_unitForm u
  have h1v : (realFormOf D 1).1.eval ![1, 0] = 1 := by
    have := (principalData ℝ D).eval_unitForm 1
    exact this.trans (by simp)
  have hA := hasseC_real_of_value D (realFormOf D 1) (v := T.val.mulVec ![1, 0]) (by
    rw [hT, hu0]; exact u.ne_zero)
  have hB := hasseC_real_of_value D (realFormOf D 1) (v := ![1, 0]) (by rw [h1v]; exact one_ne_zero)
  rw [hT, hu0] at hA
  rw [h1v] at hB
  apply Units.ext
  rw [coe_realSym, ← hA, hB, hilbertSymbol_comm, hilbertSymbol_one_right]
  rfl

/-- **The Hasse–Minkowski invariant $c_\infty$ as a character of $\mathcal G_\infty$.** -/
noncomputable def realChar : RealGroup D →* ℤˣ :=
  QuotientGroup.lift _ (realSym D) (fun u hu => (MonoidHom.mem_ker).2 (realSym_ker D u hu))

/-- The character `realChar` is the Hasse–Minkowski invariant $c_\infty$ of the real class. -/
theorem realChar_realCoset (F : RealForm D) : (realChar D (realCoset D F) : ℤ) = hasseC F.1 := by
  obtain ⟨v, hv⟩ := exists_isUnit_val_field F.1
    (by rw [disc2_realForm]; exact_mod_cast NonzeroDisc.ne_zero (D := D))
  have e : realCoset D F = QuotientGroup.mk hv.unit :=
    cosetOf_eq _ (by norm_num) halfProp_real (disc2_realForm D F) _ hv
  rw [e, realChar, QuotientGroup.lift_mk, coe_realSym, hasseC_real_of_value D F hv.ne_zero, IsUnit.unit_spec]

end Chars

/-! ### The primes dividing $2D$ and $\mathcal G_p$ for $p \nmid 2D$ -/

section Main

variable (D : ℤ) [NonzeroDisc D]

/-- **The primes dividing $2D$**, as a finite set. -/
def PrimesDvd : Finset ℕ := (2 * D.natAbs).primeFactors

theorem mem_primesDvd (p : ℕ) : p ∈ PrimesDvd D ↔ p.Prime ∧ p ∣ 2 * D.natAbs := by
  have : 2 * D.natAbs ≠ 0 := mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.2 NonzeroDisc.ne_zero)
  simp [PrimesDvd, Nat.mem_primeFactors, this]

instance instFactPrimesDvd (p : PrimesDvd D) : Fact (p.1).Prime := ⟨((mem_primesDvd D p.1).1 p.2).1⟩

/-- Helper: for $p \nmid 2D$, $p$ is odd and $p \nmid D$. -/
theorem odd_not_dvd_of_not_mem (p : ℕ) [Fact p.Prime] (hp : p ∉ PrimesDvd D) :
    p ≠ 2 ∧ ¬ (p : ℤ) ∣ D := by
  rw [mem_primesDvd] at hp
  refine ⟨?_, fun h => hp ⟨Fact.out, dvd_mul_of_dvd_right (Int.natCast_dvd.1 h) 2⟩⟩
  rintro rfl
  exact hp ⟨Fact.out, dvd_mul_right 2 _⟩

/-- **$\mathcal G_p$ is trivial for $p \nmid 2D$** (Cassels, Ch. 14, Lemma 3.1 (i), p. 339, for the group
$\mathcal G_p$ of `localEquiv`). -/
@[kb "cassels1978" "Ch. 14, Lemma 3.1 (i), p. 339 (𝒢_p is trivial, for the group 𝒢_p)"]
theorem card_localGroup_of_not_mem (p : ℕ) [Fact p.Prime]
    (hp : p ∉ PrimesDvd D) : Nat.card (LocalGroup p D) = 1 := by
  obtain ⟨hp2, hpD⟩ := odd_not_dvd_of_not_mem D p hp
  rw [← Nat.card_congr (localEquiv p D)]
  exact card_localClasses_odd_of_not_dvd hp2 NonzeroDisc.mod_four hpD

/-- Helper: for $p \nmid 2D$ every primitive $\mathbb Z_p$-form of discriminant $D$ has Hasse invariant $1$. -/
theorem hasseC_eq_one_of_not_mem (p : ℕ) [Fact p.Prime]
    (hp : p ∉ PrimesDvd D) (F : LocalPrimForm p D) :
    hasseC (F.1.map PadicInt.Coe.ringHom) = 1 := by
  obtain ⟨g, hg1, hg2, hg3⟩ := principal_exists p NonzeroDisc.ne_zero (NonzeroDisc.mod_four (D := D))
  have hcard := card_localClasses_odd_of_not_dvd (odd_not_dvd_of_not_mem D p hp).1 NonzeroDisc.mod_four
    (odd_not_dvd_of_not_mem D p hp).2
  have hsub : Subsingleton (LocalClasses p D) := (Nat.card_eq_one_iff_unique.1 hcard).1
  have h : (Quotient.mk (localSetoid p D) F : LocalClasses p D) = Quotient.mk (localSetoid p D) ⟨g, hg1, hg2⟩ :=
    @Subsingleton.elim (LocalClasses p D) hsub _ _
  rw [Hanke2011Structure.hasseC_eq_of_isometricGL (localClasses_exact h)]
  exact hg3

/-- **The product $\prod_{p \mid 2D} \mathcal G_p \times \mathcal G_\infty$** (a finite product of finite abelian
groups). -/
abbrev LocalProd : Type := (∀ p : PrimesDvd D, LocalGroup p.1 D) × RealGroup D

/-- **The homomorphism (5.2)** (Cassels, Ch. 14, §5, p. 343): $\mathcal G \to \prod_{p \mid 2D} \mathcal G_p \times
\mathcal G_\infty$, whose components are the natural homomorphisms (3.1) `localHom`, `realHom`. -/
@[kb "cassels1978" "Ch. 14, §5, (5.2), p. 343 (the homomorphism 𝒢 → ∏ 𝒢_p)"]
noncomputable def globalToLocal : FormClass D →* LocalProd D :=
  (MonoidHom.pi fun p : PrimesDvd D => localHom p.1 D).prod (realHom D)

/-- **The character $\prod_p c_p$ on $\prod_{p \mid 2D} \mathcal G_p \times \mathcal G_\infty$** (the product of the
Hasse–Minkowski invariants, Cassels, Ch. 14, Corollary to Thm. 5.1, (5.4), p. 343–344). -/
noncomputable def hasseProd : LocalProd D →* ℤˣ :=
  (∏ p : PrimesDvd D, (hasseChar p.1 D).comp
      ((Pi.evalMonoidHom (fun q : PrimesDvd D => LocalGroup q.1 D) p).comp (MonoidHom.fst _ (RealGroup D)))) *
    (realChar D).comp (MonoidHom.snd _ _)

theorem coe_hasseProd (x : LocalProd D) :
    ((hasseProd D x : ℤˣ) : ℤ) =
      (∏ p : PrimesDvd D, ((hasseChar p.1 D (x.1 p) : ℤˣ) : ℤ)) * ((realChar D x.2 : ℤˣ) : ℤ) := by
  simp [hasseProd, MonoidHom.finsetProd_apply, Units.coe_prod]

/-- Helper: the product character computed from a family of forms representing the components. -/
theorem coe_hasseProd_eq (x : LocalProd D) (g : ∀ (p : ℕ) [Fact p.Prime], LocalPrimForm p D) (gInf : RealForm D)
    (hg : ∀ p : PrimesDvd D, x.1 p = localCoset p.1 D (g p.1)) (hgInf : x.2 = realCoset D gInf) :
    ((hasseProd D x : ℤˣ) : ℤ) =
      (∏ᶠ p : Nat.Primes, hasseAt (fun q _ => ((g q).1).map PadicInt.Coe.ringHom) p) * hasseC gInf.1 := by
  rw [coe_hasseProd, hgInf, realChar_realCoset]
  congr 1
  refine Eq.trans ?_ (finprod_eq_prod_of_mulSupport_subset _ (s := (PrimesDvd D).subtype Nat.Prime) ?_).symm
  · symm
    refine Finset.prod_bij (fun q hq => ⟨q.1, (Finset.mem_subtype.1 hq)⟩) (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Subtype.ext (Subtype.mk.inj h))
      (fun p _ => ⟨⟨p.1, ((mem_primesDvd D p.1).1 p.2).1⟩, Finset.mem_subtype.2 p.2, rfl⟩) ?_
    intro q hq
    rw [hg ⟨q.1, Finset.mem_subtype.1 hq⟩, hasseChar_localCoset]
    rfl
  · intro q hq
    by_contra hqS
    apply hq
    have hqS' : q.1 ∉ PrimesDvd D := fun h => hqS (Finset.mem_coe.2 (Finset.mem_subtype.2 h))
    have : Fact (q : ℕ).Prime := ⟨q.2⟩
    exact hasseC_eq_one_of_not_mem D q.1 hqS' (g q.1)

/-- Helper: every element of the product is the family of classes of a family of forms. -/
theorem exists_family (x : LocalProd D) :
    ∃ (g : ∀ (p : ℕ) [Fact p.Prime], LocalPrimForm p D) (gInf : RealForm D),
      (∀ p : PrimesDvd D, x.1 p = localCoset p.1 D (g p.1)) ∧ x.2 = realCoset D gInf := by
  have hall : ∀ (p : ℕ) [Fact p.Prime], ∃ g : LocalPrimForm p D,
      ∀ h : p ∈ PrimesDvd D, x.1 ⟨p, h⟩ = localCoset p D g := by
    intro p _
    by_cases h : p ∈ PrimesDvd D
    · obtain ⟨g, hg⟩ := Quotient.exists_rep ((localEquiv p D).symm (x.1 ⟨p, h⟩))
      refine ⟨g, fun h' => ?_⟩
      have := (localEquiv p D).apply_symm_apply (x.1 ⟨p, h⟩)
      rw [← hg] at this
      exact this.symm
    · exact ⟨localFormOf p D 1, fun h' => absurd h' h⟩
  choose g hg using hall
  obtain ⟨gInf, hgInf⟩ := Quotient.exists_rep ((realEquiv D).symm x.2)
  refine ⟨g, gInf, fun p => hg p.1 p.2, ?_⟩
  have := (realEquiv D).apply_symm_apply x.2
  rw [← hgInf] at this
  exact this.symm

theorem toLocalPrim_val (p : ℕ) [Fact p.Prime] (f : PrimForm D) :
    (toLocalPrim p D f).1 = f.1.map (Int.castRingHom ℤ_[p]) := rfl

/-- Helper: a global form $F$ that is locally equivalent to a family of forms maps to the family of their classes. -/
theorem globalToLocal_eq (x : LocalProd D) (g : ∀ (p : ℕ) [Fact p.Prime], LocalPrimForm p D) (gInf : RealForm D)
    (hg : ∀ p : PrimesDvd D, x.1 p = localCoset p.1 D (g p.1)) (hgInf : x.2 = realCoset D gInf)
    (F : PrimForm D)
    (hF : ∀ (p : ℕ) [Fact p.Prime], IsometricGL (F.1.map (Int.castRingHom ℤ_[p])) (g p).1)
    (hFInf : IsometricGL (F.1.map (Int.castRingHom ℝ)) gInf.1) :
    globalToLocal D (mk F) = x := by
  apply Prod.ext
  · funext p
    have e : (globalToLocal D (mk F)).1 p = localHom p.1 D (mk F) := rfl
    rw [e, hg p, localHom_mk]
    have h1 : IsometricGL (toLocalPrim p.1 D F).1 (g p.1).1 := by
      rw [toLocalPrim_val]; exact hF p.1
    exact congrArg (localEquiv p.1 D) (localClasses_sound h1)
  · have e : (globalToLocal D (mk F)).2 = realHom D (mk F) := rfl
    rw [e, hgInf, realHom_mk]
    have h2 : IsometricGL (toRealForm D F).1 gInf.1 := hFInf
    exact congrArg (realEquiv D) (Quotient.sound (s := realSetoid D) (a := toRealForm D F) (b := gInf) h2)

/-- **The image of $\mathcal G \to \prod_{p} \mathcal G_p$ is the kernel of $\prod_p c_p$** (Cassels, Ch. 14,
Theorem 5.1 and the proof of its Corollary, p. 343–344): a family of classes in the $\mathcal G_p$ ($p \mid 2D$ and
$p = \infty$) comes from a class of $\mathcal G$ iff the product of the Hasse–Minkowski invariants of its components
is $1$. (By `thm_5_1`, which handles the families of forms.) -/
@[kb "cassels1978" "Ch. 14, Thm. 5.1, p. 343; proof of the Cor., p. 344 (the image is the kernel of ∏ c_p)"]
theorem range_eq_ker : MonoidHom.range (G := FormClass D) (N := LocalProd D) (globalToLocal D) = MonoidHom.ker (G := LocalProd D) (hasseProd D) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨F, rfl⟩ := mk_surjective y
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [coe_hasseProd_eq D _ (fun q _ => toLocalPrim q D F) (toRealForm D F) (fun p => rfl) rfl]
    exact prod_hasse_eq_one_of_global NonzeroDisc.ne_zero F.1 F.2.2
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨g, gInf, hg, hgInf⟩ := exists_family D x
    have h1 := coe_hasseProd_eq D x g gInf hg hgInf
    rw [hx] at h1
    obtain ⟨F, hFp, hFd, hF, hFInf⟩ := (thm_5_1 NonzeroDisc.ne_zero (fun p _ => (g p).1)
      (fun p _ => (g p).2.1) (fun p _ => (g p).2.2) gInf.1 gInf.2).2 h1.symm
    exact ⟨mk ⟨F, hFp, hFd⟩, globalToLocal_eq D x g gInf hg hgInf ⟨F, hFp, hFd⟩ hF hFInf⟩

/-- **Cassels, Ch. 14, Theorem 5.1, the square case** (p. 343), *with the groups $\mathcal G_p$*: if $D$ is a perfect
square, the image of $\mathcal G \to \prod_{p \le \infty} \mathcal G_p$ is the entire group. Here the product is over
the primes dividing $2D$ and $\infty$ (the other $\mathcal G_p$ are trivial, `card_localGroup_of_not_mem`).
Unconditional. -/
@[kb "cassels1978" "Ch. 14, Thm. 5.1, p. 343 (D a perfect square: the image is the entire group, with the groups 𝒢_p)"]
theorem thm_5_1_square (hsq : IsSquare D) : Function.Surjective (globalToLocal D) := by
  intro x
  obtain ⟨g, gInf, hg, hgInf⟩ := exists_family D x
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by rintro rfl; exact NonzeroDisc.ne_zero (D := D) (by simpa using hr)
  have hr2 : D = r ^ 2 := by rw [hr]; ring
  obtain ⟨F, hFp, hFd, hF, hFInf⟩ := prod_hasse_eq_one_of_isSquare hr0 (fun p _ => (g p).1)
    (fun p _ => (g p).2.1) (fun p _ => by rw [(g p).2.2, hr2]) gInf.1
    (by rw [gInf.2, hr2])
  exact ⟨mk ⟨F, hFp, hFd.trans hr2.symm⟩, globalToLocal_eq D x g gInf hg hgInf ⟨F, hFp, hFd.trans hr2.symm⟩ hF hFInf⟩

/-- **Cassels, Ch. 14, Theorem 5.1, the non-square case** (p. 343), *with the groups $\mathcal G_p$*: if $D$ is not a
perfect square, the image of $\mathcal G \to \prod_{p \le \infty} \mathcal G_p$ is a subgroup of index $2$
(product over the primes dividing $2D$ and $\infty$, the other factors being trivial). Unconditional. -/
@[kb "cassels1978" "Ch. 14, Thm. 5.1, p. 343 (D not a square: the image has index 2, with the groups 𝒢_p)"]
theorem thm_5_1_nonsquare (hsq : ¬ IsSquare D) : (MonoidHom.range (G := FormClass D) (N := LocalProd D) (globalToLocal D)).index = 2 := by
  rw [range_eq_ker, Subgroup.index_ker]
  obtain ⟨f, fInf, hprim, hdet, hdetInf, hprod⟩ :=
    exists_prod_hasse_eq_neg_one NonzeroDisc.ne_zero NonzeroDisc.mod_four hsq
  let g : ∀ (p : ℕ) [Fact p.Prime], LocalPrimForm p D := fun p _ => ⟨f p, hprim p, hdet p⟩
  let gInf : RealForm D := ⟨fInf, hdetInf⟩
  let x : LocalProd D := (fun p => localCoset p.1 D (g p.1), realCoset D gInf)
  have hx : hasseProd D x = -1 := by
    apply Units.ext
    rw [coe_hasseProd_eq D x g gInf (fun p => rfl) rfl]
    exact hprod
  have htop : MonoidHom.range (G := LocalProd D) (N := ℤˣ) (hasseProd D) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact one_mem _
    · exact ⟨x, hx⟩
  rw [htop, Subgroup.card_top]
  rw [Nat.card_eq_two_iff]
  refine ⟨1, -1, by decide, ?_⟩
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact Int.units_eq_one_or z

end Main

end QuadFormsKB.Composition
