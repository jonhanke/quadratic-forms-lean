import QuadFormsKB.Binary.FormAut
import QuadFormsKB.Binary.LFactorization

/-!
# Representation numbers of binary forms and Dirichlet's formula

For a fundamental discriminant $D < 0$, a primitive positive definite form $f$ of discriminant $D$ and $m \ge 1$:

* **$r_f(m) = w \cdot \#\{\mathfrak b \subseteq \mathcal O_K : N\mathfrak b = m,\ [\mathfrak b] = [\mathfrak a_f]^{-1}\}$**
  (`repNum_eq`): $(x, y) \mapsto z = xa + y(k_f - \omega) \in \mathfrak a_f$ with $N z = a\,m$, and $(z) = \mathfrak a_f\mathfrak b$; the
  map $z \mapsto \mathfrak b$ is $w$-to-one ($w = \#\mathcal O_K^\times$).
* **Dirichlet's formula** (`sum_repNum_slClasses`): summing over the proper classes,
  $$\sum_{[f] \in \mathrm{SL}_2(\mathbb{Z})\backslash\{\text{forms}\}} r_f(m) = w \sum_{d \mid m}\chi_D(d).$$
* **The $\mathrm{GL}_2(\mathbb{Z})$-class version** (the library's convention, used by the genus averages,
  `sum_repNum_div_card_aut_glClasses`):
  $$\sum_{[f] \in \mathrm{GL}_2(\mathbb{Z})\backslash\{\text{forms}\}} \frac{r_f(m)}{|\mathrm{Aut}(f)|} = \frac12\sum_{d \mid m}\chi_D(d).$$

Sources: Cox, *Primes of the form $x^2 + ny^2$*, §7 [unverified locator]; Zagier,
*Zetafunktionen und quadratische Körper*, §8, Satz 3 [unverified locator]; Davenport, *Multiplicative Number Theory*,
Ch. 6.
-/

open QuadraticAlgebra NumberField Matrix
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF

variable {D : ℤ} [IsQuadDisc D]

/-- The algebra norm of $\mathbb{Z}[\omega]$ over $\mathbb{Z}$ is the quadratic norm $N(u + v\omega) = u^2 + b_D uv - a_D v^2$. -/
theorem algebraNorm_eq (z : QOrder D) : Algebra.norm ℤ z = norm z := by
  rw [Algebra.norm_apply]; exact det_toLinearMap_eq_norm z

/-- **$N((z)) = N(z)$** for $z \neq 0$ when $D < 0$ (the norm form is positive). -/
theorem absNorm_span_singleton_eq (hD : D < 0) {z : QOrder D} (hz : z ≠ 0) :
    (Ideal.absNorm (Ideal.span {z}) : ℤ) = norm z := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_eq, Int.natCast_natAbs,
    abs_of_pos (norm_pos_of_neg hD (IsQuadDisc.fund (D := D)).1 hz)]

/-- **The ideals of norm $m$ in a class** $C \in \mathrm{Cl}(\mathbb{Z}[\omega])$:
$\{\mathfrak b \subseteq \mathbb{Z}[\omega] : N\mathfrak b = m,\ [\mathfrak b] = C\}$. -/
def IdealsInClass (C : ClassGroup (QOrder D)) (m : ℕ) : Type :=
  {𝔟 : Ideal (QOrder D) // Ideal.absNorm 𝔟 = m ∧ ∃ h : 𝔟 ∈ (Ideal (QOrder D))⁰, ClassGroup.mk0 ⟨𝔟, h⟩ = C}

/-- The elements $z \in \mathfrak a_f$ with $N z = a m$. -/
def RepElts (f : BinQF) (m : ℕ) : Type := {z : QOrder D // z ∈ formIdeal D f ∧ norm z = f.a * m}

/-- **Representations are elements of $\mathfrak a_f$:** $(x, y) \mapsto xa + y(k_f - \omega)$ is a bijection from
$\{(x, y) : f(x, y) = m\}$ onto $\{z \in \mathfrak a_f : N z = a m\}$ (as $a\,f(x, y) = N(xa + y(k_f - \omega))$). -/
noncomputable def repSetEquiv (f : PrimPosForm D) (m : ℕ) :
    Siegel.repSet f.1 m ≃ RepElts (D := D) f.1 m := by
  have hf := isFormOf_formIdeal f.2.1
  have ha : f.1.a ≠ 0 := f.a_pos.ne'
  refine Equiv.ofBijective (fun x => ⟨x.1 0 • fα D f.1 + x.1 1 • fβ D f.1,
    (mem_formIdeal_iff_exists f.2.1 _).mpr ⟨_, _, rfl⟩, ?_⟩) ⟨?_, ?_⟩
  · rw [← hf, odet_fα_fβ f.2.1]
    have := x.2
    simp only [Siegel.repSet, Set.mem_ofPred_eq] at this
    rw [BinQF.eval, ← vec_two_eq, this]
  · intro x y h
    have h' := congrArg Subtype.val h
    obtain ⟨e0, e1⟩ := coeffs_eq_of ha h'
    apply Subtype.ext; funext i; fin_cases i
    · exact e0
    · exact e1
  · rintro ⟨z, hz, hN⟩
    obtain ⟨x, y, rfl⟩ := (mem_formIdeal_iff_exists f.2.1 z).mp hz
    refine ⟨⟨![x, y], ?_⟩, rfl⟩
    simp only [Siegel.repSet, Set.mem_ofPred_eq]
    have := hf x y
    rw [odet_fα_fβ f.2.1, hN] at this
    exact mul_left_cancel₀ ha this

/-- $\mathfrak b\,\mathfrak a_f \subseteq \mathfrak a_f$ and the absolute norm is multiplicative. -/
theorem absNorm_mul_formIdeal (f : PrimPosForm D) (𝔟 : Ideal (QOrder D)) :
    Ideal.absNorm (𝔟 * formIdeal D f.1) = Ideal.absNorm 𝔟 * f.1.a.natAbs := by
  rw [map_mul, absNorm_formIdeal f.2.1 f.a_pos.ne']

/-- **The section:** an ideal $\mathfrak b$ of norm $m$ in the class $[\mathfrak a_f]^{-1}$ gives $z \in \mathfrak a_f$ with
$(z) = \mathfrak b\,\mathfrak a_f$ and $N z = a m$. -/
theorem exists_gen (hD : D < 0) (f : PrimPosForm D) {m : ℕ} (𝔟 : IdealsInClass (idealClass f)⁻¹ m) :
    ∃ z : QOrder D, z ≠ 0 ∧ 𝔟.1 * formIdeal D f.1 = Ideal.span {z} ∧ z ∈ formIdeal D f.1 ∧
      norm z = f.1.a * m := by
  obtain ⟨hN, h0, hc⟩ := 𝔟.2
  have := (ClassGroup.mk0_eq_mk0_inv_iff (I := ⟨𝔟.1, h0⟩)
    (J := ⟨formIdeal D f.1, mem_nonZeroDivisors_of_ne_zero (formIdeal_ne_bot f.a_pos.ne')⟩)).mp hc
  obtain ⟨z, hz, hspan⟩ := this
  refine ⟨z, hz, hspan, ?_, ?_⟩
  · have : Ideal.span {z} ≤ formIdeal D f.1 := hspan ▸ Ideal.mul_le_right
    exact this (Ideal.mem_span_singleton_self z)
  · rw [← absNorm_span_singleton_eq hD hz, ← hspan, absNorm_mul_formIdeal, hN]
    push_cast
    rw [abs_of_pos f.a_pos]; ring

/-- **$r_f(m) = w \cdot \#\{\mathfrak b : N\mathfrak b = m,\ [\mathfrak b] = [\mathfrak a_f]^{-1}\}$** ($D < 0$ fundamental, $m \ge 1$,
$w = \#\mathbb{Z}[\omega]^\times$): the map $z \mapsto \mathfrak b$, $(z) = \mathfrak a_f\mathfrak b$, from
$\{z \in \mathfrak a_f : N z = a m\}$ is onto the ideals of norm $m$ in $[\mathfrak a_f]^{-1}$ and its fibers are the orbits
of the units. Source: Cox, §7 [unverified locator]; Zagier, §8 [unverified locator]. -/
@[kb "zagier1981" "§8 [unverified locator]"]
theorem repNum_eq (hD : D < 0) (f : PrimPosForm D) {m : ℕ} (hm : m ≠ 0) :
    Siegel.repNum f.1 m = Nat.card (IdealsInClass (idealClass f)⁻¹ m) * Nat.card (QOrder D)ˣ := by
  classical
  rw [Siegel.repNum, Nat.card_congr (repSetEquiv f m), ← Nat.card_prod]
  have ha : f.1.a ≠ 0 := f.a_pos.ne'
  have hI : formIdeal D f.1 ≠ ⊥ := formIdeal_ne_bot ha
  let s : IdealsInClass (idealClass f)⁻¹ m → QOrder D := fun 𝔟 => Classical.choose (exists_gen hD f 𝔟)
  have hs : ∀ 𝔟, s 𝔟 ≠ 0 ∧ 𝔟.1 * formIdeal D f.1 = Ideal.span {s 𝔟} ∧ s 𝔟 ∈ formIdeal D f.1 ∧
      norm (s 𝔟) = f.1.a * m := fun 𝔟 => Classical.choose_spec (exists_gen hD f 𝔟)
  refine (Nat.card_congr (Equiv.ofBijective (fun p : IdealsInClass (idealClass f)⁻¹ m × (QOrder D)ˣ =>
    (⟨s p.1 * p.2, Ideal.mul_mem_right _ _ (hs p.1).2.2.1, by
      rw [map_mul, (hs p.1).2.2.2, norm_unit_eq_one hD (IsQuadDisc.fund (D := D)).1, mul_one]⟩ :
      RepElts (D := D) f.1 m)) ⟨?_, ?_⟩)).symm
  · rintro ⟨𝔟, u⟩ ⟨𝔟', u'⟩ h
    have h' : s 𝔟 * u = s 𝔟' * u' := congrArg Subtype.val h
    have hspan : Ideal.span {s 𝔟} = Ideal.span {s 𝔟'} := by
      rw [Ideal.span_singleton_eq_span_singleton]
      have h1 : Associated (s 𝔟) (s 𝔟 * u) := associated_mul_unit_right _ _ u.isUnit
      have h2 : Associated (s 𝔟') (s 𝔟' * u') := associated_mul_unit_right _ _ u'.isUnit
      exact h1.trans (by rw [h']; exact h2.symm)
    have hb : 𝔟 = 𝔟' := by
      apply Subtype.ext
      have := (hs 𝔟).2.1.trans (hspan.trans (hs 𝔟').2.1.symm)
      exact mul_right_cancel₀ hI this
    subst hb
    have hu : (u : QOrder D) = u' := mul_left_cancel₀ (hs 𝔟).1 h'
    exact Prod.ext rfl (Units.ext hu)
  · rintro ⟨z, hz, hN⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [QuadraticAlgebra.norm_zero] at hN
      exact mul_ne_zero ha (by exact_mod_cast hm) hN.symm
    obtain ⟨𝔟, h𝔟⟩ : formIdeal D f.1 ∣ Ideal.span {z} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hz)
    have h𝔟0 : 𝔟 ≠ ⊥ := by
      rintro rfl
      rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at h𝔟
      exact hz0 h𝔟
    have hmem : 𝔟 ∈ (Ideal (QOrder D))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔟0
    have hN𝔟 : Ideal.absNorm 𝔟 = m := by
      have e := absNorm_span_singleton_eq hD hz0
      rw [h𝔟, mul_comm, absNorm_mul_formIdeal, hN] at e
      push_cast at e
      rw [abs_of_pos f.a_pos, mul_comm] at e
      exact_mod_cast mul_left_cancel₀ ha e
    let b : IdealsInClass (idealClass f)⁻¹ m := ⟨𝔟, hN𝔟, hmem, by
      rw [idealClass, ClassGroup.mk0_eq_mk0_inv_iff]
      exact ⟨z, hz0, by rw [mul_comm]; exact h𝔟.symm⟩⟩
    have hspan : Ideal.span {s b} = Ideal.span {z} := by
      rw [← (hs b).2.1, h𝔟, mul_comm]
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    exact ⟨(b, u), Subtype.ext hu⟩

/-! ### Summing over the classes: Dirichlet's formula -/

/-- **$r_f(m)$ as a function of the proper class** of $f$ (it is a $\mathrm{GL}_2(\mathbb{Z})$-, hence
$\mathrm{SL}_2(\mathbb{Z})$-invariant, `Siegel.repNum_eq_of_intEquiv`). -/
noncomputable def slClassRepNum (m : ℕ) : Quotient (slSetoid D) → ℕ :=
  Quotient.lift (fun f => Siegel.repNum f.1 m) fun _ _ h => Siegel.repNum_eq_of_intEquiv (SLEquiv.intEquiv h) _

/-- **$r_f(m)$ as a function of the $\mathrm{GL}_2(\mathbb{Z})$-class** of $f$ (the library's convention). -/
noncomputable def glClassRepNum (m : ℕ) : Quotient (glSetoid D) → ℕ :=
  Quotient.lift (fun f => Siegel.repNum f.1 m) fun _ _ h => Siegel.repNum_eq_of_intEquiv h _

/-- **$|\mathrm{Aut}(f)|$ as a function of the $\mathrm{GL}_2(\mathbb{Z})$-class** (`Siegel.card_aut_eq_of_intEquiv`). -/
noncomputable def glClassAutCard : Quotient (glSetoid D) → ℕ :=
  Quotient.lift (fun f => Nat.card (Siegel.Aut f.1)) fun _ _ h => Siegel.card_aut_eq_of_intEquiv h

noncomputable instance [Fact (D < 0)] : Fintype (Quotient (slSetoid D)) :=
  @Fintype.ofFinite _ (finite_slClasses (Fact.out))

noncomputable instance [Fact (D < 0)] : Fintype (Quotient (glSetoid D)) :=
  @Fintype.ofFinite _ (Finite.of_surjective (Quotient.map' id fun _ _ h => SLEquiv.intEquiv h :
    Quotient (slSetoid D) → Quotient (glSetoid D)) (by
      have := finite_slClasses (D := D) Fact.out
      intro x; induction x using Quotient.inductionOn with | h f => exact ⟨Quotient.mk _ f, rfl⟩))

/-- Every ideal of nonzero norm lies in exactly one class:
$\#\{\mathfrak b : N\mathfrak b = m\} = \sum_{C \in \mathrm{Cl}} \#\{\mathfrak b : N\mathfrak b = m, [\mathfrak b] = C\}$. -/
theorem card_ideals_eq_sum_classes [Fintype (ClassGroup (QOrder D))] {m : ℕ} (hm : m ≠ 0) :
    Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = m} =
      ∑ C : ClassGroup (QOrder D), Nat.card (IdealsInClass C m) := by
  classical
  set Y := {I : Ideal (QOrder D) // Ideal.absNorm I = m}
  have h0 : ∀ I : Y, I.1 ∈ (Ideal (QOrder D))⁰ := fun I => mem_nonZeroDivisors_of_ne_zero (by
    intro h; have := I.2; rw [h, map_zero] at this; exact hm this.symm)
  let cls : Y → ClassGroup (QOrder D) := fun I => ClassGroup.mk0 ⟨I.1, h0 I⟩
  have hfin : Finite Y := (Ideal.finite_setOfPred_absNorm_eq m).to_subtype
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv cls), Nat.card_sigma]
  refine Finset.sum_congr rfl fun C _ => Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨x.1.1, x.1.2, h0 x.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by obtain ⟨_, h, hC⟩ := x.2; exact hC⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

/-- The ideals of $\mathbb{Z}[\omega]$ and of $\mathcal O_{K_D}$ of norm $m$ correspond (`orderEquiv`). -/
theorem card_ideals_order_eq (m : ℕ) :
    Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = m} =
      Nat.card {I : Ideal (𝓞 (QField D)) // Ideal.absNorm I = m} := by
  set e := (orderEquiv D).toRingEquiv
  have hN : ∀ I : Ideal (QOrder D), Ideal.absNorm (I.map e) = Ideal.absNorm I := fun I => by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv).symm
  refine Nat.card_congr
    { toFun := fun I => ⟨I.1.map e, by rw [hN]; exact I.2⟩
      invFun := fun J => ⟨J.1.map e.symm, by
        have h1 := hN (J.1.map e.symm)
        have h2 : (J.1.map e.symm).map e = J.1 := by
          have := Ideal.map_of_equiv (I := J.1) e.symm
          rwa [RingEquiv.symm_symm] at this
        rw [h2] at h1; rw [← h1]; exact J.2⟩
      left_inv := fun I => Subtype.ext (Ideal.map_of_equiv e)
      right_inv := fun J => Subtype.ext (by
        have := Ideal.map_of_equiv (I := J.1) e.symm
        rwa [RingEquiv.symm_symm] at this) }

/-- **Dirichlet's formula** ($D < 0$ fundamental, $m \ge 1$): summing $r_f(m)$ over the proper
($\mathrm{SL}_2(\mathbb{Z})$-) classes of primitive positive definite forms of discriminant $D$,
$$\sum_{[f]} r_f(m) = w\,\#\{\mathfrak b \subseteq \mathcal O_{K_D} : N\mathfrak b = m\},$$
since $[f] \mapsto [\mathfrak a_f]^{-1}$ is a bijection onto $\mathrm{Cl}$ (`slClassEquivOrder`) and every ideal of norm $m$
lies in exactly one class. Source: Cox, §7 [unverified locator]; Zagier, §8, Satz 3 [unverified locator]. -/
@[kb "zagier1981" "§8 [unverified locator]"]
theorem sum_slClassRepNum_eq [Fact (D < 0)] {m : ℕ} (hm : m ≠ 0) :
    ∑ c : Quotient (slSetoid D), slClassRepNum m c =
      NumberField.Units.torsionOrder (QField D) *
        Nat.card {I : Ideal (𝓞 (QField D)) // Ideal.absNorm I = m} := by
  classical
  have hD : D < 0 := Fact.out
  have : Fintype (ClassGroup (QOrder D)) :=
    @Fintype.ofFinite _ (Finite.of_equiv _ (classGroupEquiv D).toEquiv.symm)
  rw [← card_ideals_order_eq, card_ideals_eq_sum_classes hm, Finset.mul_sum, ← card_units_eq_torsionOrder hD]
  let e : Quotient (slSetoid D) ≃ ClassGroup (QOrder D) := (slClassEquivOrder hD).trans (Equiv.inv _)
  refine Fintype.sum_equiv e _ _ fun c => ?_
  induction c using Quotient.inductionOn with
  | h f =>
    simp only [slClassRepNum, Quotient.lift_mk, e, Equiv.trans_apply, Equiv.inv_apply]
    rw [repNum_eq hD f hm, mul_comm]
    rfl

/-- **Dirichlet's formula with the Kronecker symbol** ($D < 0$ fundamental, $m \ge 1$):
$$\sum_{[f] \in \mathrm{SL}_2(\mathbb{Z})\text{-classes}} r_f(m) = w \sum_{d \mid m} \chi_D(d),$$
with $\chi_D$ = `kroneckerChar D` and $w$ = `torsionOrder` $(K_D)$ ($= 2, 4, 6$). Combines `sum_slClassRepNum_eq` with
`card_ideals_absNorm_eq`. Source: Dirichlet; Zagier, §8, Satz 3 [unverified locator]; Davenport, Ch. 6. -/
@[kb "zagier1981" "§8 [unverified locator]"]
theorem dirichlet_sum_repNum [Fact (D < 0)] {m : ℕ} (hm : m ≠ 0) :
    ((∑ c : Quotient (slSetoid D), slClassRepNum m c : ℕ) : ℂ) =
      NumberField.Units.torsionOrder (QField D) * ∑ d ∈ m.divisors, kroneckerChar D d := by
  rw [sum_slClassRepNum_eq hm, Nat.cast_mul, card_ideals_absNorm_eq hm]

/-- **Dirichlet's formula over $\mathbb{Z}$** (with the integer-valued $\chi_D$ = `kronZ D`). -/
theorem dirichlet_sum_repNum_int [Fact (D < 0)] {m : ℕ} (hm : m ≠ 0) :
    ((∑ c : Quotient (slSetoid D), slClassRepNum m c : ℕ) : ℤ) =
      NumberField.Units.torsionOrder (QField D) * ∑ d ∈ m.divisors, kronZ D (d : ZMod D.natAbs) := by
  rw [sum_slClassRepNum_eq hm, Nat.cast_mul, card_ideals_absNorm_eq_int hm]

/-! ### The $\mathrm{GL}_2(\mathbb{Z})$-class version (the library's convention) -/

/-- The map from proper classes to $\mathrm{GL}_2(\mathbb{Z})$-classes. -/
def slToGl : Quotient (slSetoid D) → Quotient (glSetoid D) :=
  Quotient.map' id fun _ _ h => SLEquiv.intEquiv h

/-- **A $\mathrm{GL}_2(\mathbb{Z})$-class $[f]$ contains the proper classes $[f]^+$ and $[\bar f]^+$ and no others.** -/
theorem slToGl_eq_iff (f : PrimPosForm D) (c : Quotient (slSetoid D)) :
    slToGl c = Quotient.mk (glSetoid D) f ↔
      c = Quotient.mk (slSetoid D) f ∨ c = Quotient.mk (slSetoid D) f.conj := by
  induction c using Quotient.inductionOn with
  | h g =>
    change Quotient.mk (glSetoid D) g = _ ↔ _
    rw [Quotient.eq, Quotient.eq, Quotient.eq]
    change Siegel.IntEquiv g.1 f.1 ↔ SLEquiv g.1 f.1 ∨ SLEquiv g.1 (conjForm f.1)
    constructor
    · intro h
      rcases (intEquiv_iff_sLEquiv_or _ _).mp (Siegel.IsometricGL.symm h) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact h.intEquiv
      · exact Siegel.IsometricGL.symm ((intEquiv_iff_sLEquiv_or _ _).mpr (Or.inr h.symm))

open Classical in
/-- **Fibers of $\mathrm{SL} \to \mathrm{GL}$ classes and automorphisms:** for every $\mathrm{GL}_2(\mathbb{Z})$-class $G$,
$\#\{\text{proper classes in } G\} \cdot |\mathrm{Aut}(G)| = 2w$ (an ambiguous class is one proper class with $2w$
automorphisms; otherwise two proper classes with $w$). -/
theorem card_fiber_mul_aut [Fact (D < 0)] (G : Quotient (glSetoid D)) :
    (Finset.univ.filter fun c => slToGl c = G).card * glClassAutCard G =
      2 * NumberField.Units.torsionOrder (QField D) := by
  classical
  have hD : D < 0 := Fact.out
  induction G using Quotient.inductionOn with
  | h f =>
    have hfib : (Finset.univ.filter fun c => slToGl c = Quotient.mk (glSetoid D) f) =
        {Quotient.mk (slSetoid D) f, Quotient.mk (slSetoid D) f.conj} := by
      ext c; simp [slToGl_eq_iff]
    rw [hfib]
    simp only [glClassAutCard, Quotient.lift_mk]
    rw [card_aut hD f]
    split_ifs with h
    · have : Quotient.mk (slSetoid D) f = Quotient.mk (slSetoid D) f.conj :=
        Quotient.sound (SLEquiv.symm h)
      rw [this, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.card_singleton]; ring
    · have : Quotient.mk (slSetoid D) f ≠ Quotient.mk (slSetoid D) f.conj := fun h' =>
        h (SLEquiv.symm (Quotient.exact h'))
      rw [Finset.card_pair this]; ring

/-- **Dirichlet's formula for $\mathrm{GL}_2(\mathbb{Z})$-classes weighted by $1/|\mathrm{Aut}|$** ($D < 0$ fundamental,
$m \ge 1$; the library's convention: classes
are $\mathrm{GL}_2(\mathbb{Z})$-classes, $\mathrm{Aut} \subseteq \mathrm{GL}_2(\mathbb{Z})$):
$$\sum_{[f] \in \mathrm{GL}_2(\mathbb{Z})\text{-classes}} \frac{r_f(m)}{|\mathrm{Aut}(f)|} = \frac12 \sum_{d \mid m} \chi_D(d).$$
The factor $\frac12$ is $\#\{\pm 1\}^{-1}$: the $\mathrm{GL}$-mass is half the $\mathrm{SL}$-mass. This is the form in which the
genus averages (Siegel's $\varepsilon = \frac12$) use it. -/
@[kb "zagier1981" "§8 [unverified locator]"]
theorem dirichlet_sum_repNum_div_aut [Fact (D < 0)] {m : ℕ} (hm : m ≠ 0) :
    ∑ G : Quotient (glSetoid D), (glClassRepNum m G : ℚ) / glClassAutCard G =
      (1 / 2 : ℚ) * ∑ d ∈ m.divisors, (kronZ D (d : ZMod D.natAbs) : ℚ) := by
  classical
  have hD : D < 0 := Fact.out
  set w := NumberField.Units.torsionOrder (QField D)
  have hw : (w : ℚ) ≠ 0 := by exact_mod_cast (NumberField.Units.torsionOrder_pos (QField D)).ne'
  have hdir := dirichlet_sum_repNum_int (D := D) hm
  have hdirQ : ((∑ c : Quotient (slSetoid D), slClassRepNum m c : ℕ) : ℚ) =
      w * ∑ d ∈ m.divisors, (kronZ D (d : ZMod D.natAbs) : ℚ) := by exact_mod_cast hdir
  have hr : ∀ c : Quotient (slSetoid D), slClassRepNum m c = glClassRepNum m (slToGl c) := fun c => by
    induction c using Quotient.inductionOn with | h f => rfl
  have hsum : ((∑ c : Quotient (slSetoid D), slClassRepNum m c : ℕ) : ℚ) =
      ∑ G : Quotient (glSetoid D),
        ((Finset.univ.filter fun c => slToGl c = G).card : ℚ) * glClassRepNum m G := by
    push_cast
    rw [← Finset.sum_fiberwise Finset.univ slToGl]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [Finset.sum_congr rfl fun c hc => by rw [hr, (Finset.mem_filter.mp hc).2], Finset.sum_const,
      nsmul_eq_mul]
  have haut : ∀ G : Quotient (glSetoid D), (glClassAutCard G : ℚ) ≠ 0 := fun G => by
    intro h0
    have := card_fiber_mul_aut G
    have h0' : glClassAutCard G = 0 := by exact_mod_cast h0
    rw [h0', mul_zero] at this
    exact hw (by exact_mod_cast (by omega : w = 0))
  have hfibQ : ∀ G : Quotient (glSetoid D),
      ((Finset.univ.filter fun c => slToGl c = G).card : ℚ) = 2 * w / glClassAutCard G := fun G => by
    rw [eq_div_iff (haut G)]; exact_mod_cast card_fiber_mul_aut G
  rw [hsum] at hdirQ
  simp_rw [hfibQ] at hdirQ
  have : ∑ G : Quotient (glSetoid D), (glClassRepNum m G : ℚ) / glClassAutCard G =
      (∑ G : Quotient (glSetoid D), 2 * (w : ℚ) / (glClassAutCard G : ℚ) * (glClassRepNum m G : ℚ)) /
        (2 * (w : ℚ)) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun G _ => ?_
    field_simp
  rw [this, hdirQ]
  field_simp

end QuadFormsKB.Binary
