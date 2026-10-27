import QuadFormsKB.Binary.GenusComposition
import QuadFormsKB.Siegel.ThetaCuspidal

/-!
# The mass of a genus of binary forms

For a fundamental discriminant $D < 0$ with $t$ prime factors, class number $h = h(D)$ and $w = |\mathcal O_{K_D}^\times|$
($= 6, 4, 2$), and a genus $\mathcal G$ of primitive positive definite forms of discriminant $D$:
$$\mathrm{Mass}(\mathcal G) = \sum_{[f] \in \mathcal G} \frac{1}{|\mathrm{Aut}(f)|} = \frac{h}{2^{t-1}} \cdot \frac{1}{2w}$$
(`mass_genus`), with the repo's `Siegel.mass` (the convention of this repository: $\mathrm{GL}_2(\mathbb{Z})$-classes,
$\mathrm{Aut}(f) \le \mathrm{GL}_2(\mathbb{Z})$). The chain (the list):

1. **The genus consists of primitive forms of discriminant $D$** (`mem_primPosForm_of_sameGenus`): positive
   definiteness and $\det H = -\operatorname{disc}$ are genus invariants (`Siegel.SameGenus.posDef`,
   `Siegel.SameGenus.det_hessian_eq`), and a form of fundamental discriminant is primitive (`isPrimitive_of_fund`).
   So `Siegel.genusClasses f` is the image of the $\mathrm{GL}_2(\mathbb{Z})$-classes of `PrimPosForm D` lying in
   $\mathcal G$ (`genusClasses_eq_image`).
2. **The $\mathrm{GL}/\mathrm{SL}$ fibre identity** (`card_fiber_mul_aut`):
   $\#\{\text{proper classes in a GL-class } G\}\cdot|\mathrm{Aut}(G)| = 2w$, so a $\frac{1}{|\mathrm{Aut}|}$-weighted
   sum over GL-classes is $\frac{1}{2w}$ times the plain sum over proper classes (`sum_div_aut_genus`).
3. **Each genus has $h/2^{t-1}$ proper classes** (`card_slClasses_in_genus`, unconditional by `isFormClassGroup`).

Sources: Siegel (1935), the mass in the binary case; Gauss, *Disq. Arith.* §252 [unverified]; Cox, §3.B (Thm. 3.15),
§7 [unverified locator]; Conway–Sloane, *SPLAG*, Ch. 16, §§4–7 (the mass as a sum of $1/|\mathrm{Aut}|$) [unverified].
-/

open QuadraticAlgebra NumberField
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF Siegel

variable {D : ℤ}

/-! ### Genus invariants -/

/-- **The two notions of positive definiteness for binary forms agree:** the repo's general `IntQF.PosDef`
($Q(\vec x) > 0$ for $\vec x \ne 0$) and `BinQF.PosDef` ($f(x, y) > 0$ for $(x, y) \ne (0, 0)$). -/
theorem intQF_posDef_iff (f : BinQF) : IntQF.PosDef f ↔ f.PosDef := by
  constructor
  · intro h x y hxy
    apply h ![x, y]
    intro h0
    apply hxy
    have h0' := congrFun h0 0
    have h1' := congrFun h0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0' h1'
    simp [h0', h1']
  · intro h x hx
    have := h (x 0) (x 1) (by
      intro h0
      simp only [Prod.mk.injEq] at h0
      apply hx
      funext i; fin_cases i
      · exact h0.1
      · exact h0.2)
    rwa [BinQF.eval, ← vec_two_eq] at this

variable [IsQuadDisc D]

/-- **The genus of a primitive positive definite form of fundamental discriminant $D$ consists of such forms:** if
$g$ is in the genus of $f$ (`Siegel.SameGenus`), then $\operatorname{disc} g = D$, $g$ is positive definite and $g$ is
primitive. Positive definiteness is read at the real place (`Siegel.SameGenus.posDef`), the discriminant
$= -\det H$ at every $p$ (`Siegel.SameGenus.det_hessian_eq`), and primitivity follows from $D$ fundamental
(`isPrimitive_of_fund`). -/
@[kb "cassels1978" "Ch. 9, §1 (discriminant and definiteness are genus invariants) [unverified]"]
theorem mem_primPosForm_of_sameGenus (f : PrimPosForm D) {g : BinQF} (h : SameGenus f.1 g) :
    g.disc = D ∧ g.PosDef ∧ g.IsPrimitive := by
  have hf : IntQF.PosDef f.1 := (intQF_posDef_iff _).mpr f.2.2.1
  have hdet := h.det_hessian_eq hf
  have hdisc : g.disc = D := by
    rw [disc_eq_neg_det_hessian, ← hdet, ← disc_eq_neg_det_hessian]; exact f.2.1
  exact ⟨hdisc, (intQF_posDef_iff _).mp (h.posDef hf), isPrimitive_of_fund IsQuadDisc.fund hdisc⟩

/-! ### $\mathrm{GL}_2(\mathbb{Z})$-classes in a genus -/

/-- **The genus of a $\mathrm{GL}_2(\mathbb{Z})$-class** of primitive positive definite forms of discriminant $D$. -/
def glGenus : Quotient (glSetoid D) → Genera D :=
  Quotient.lift (fun f => Quotient.mk (genusSetoid D) f.toPos) fun _ _ h => Quotient.sound (IntEquiv.sameGenus h)

/-- A $\mathrm{GL}_2(\mathbb{Z})$-class of `PrimPosForm D` as a class of the repo's `Siegel.QClass 2` (all integral
binary forms modulo `Siegel.IntEquiv`). -/
def glToQClass : Quotient (glSetoid D) → QClass 2 :=
  Quotient.lift (fun f => classOf f.1) fun _ _ h => classOf_eq_classOf_iff.mpr h

theorem glToQClass_injective : Function.Injective (glToQClass (D := D)) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h f =>
    induction y using Quotient.inductionOn with
    | h g => exact fun h => Quotient.sound (classOf_eq_classOf_iff.mp h)

/-- The proper class of a form lies in the same genus as its $\mathrm{GL}_2(\mathbb{Z})$-class. -/
theorem slGenus_eq_glGenus (c : Quotient (slSetoid D)) : slGenus c = glGenus (slToGl c) := by
  induction c using Quotient.inductionOn with | h f => rfl

/-- **The classes in the genus of $f$** (`Siegel.genusClasses`, all $\mathrm{GL}_2(\mathbb{Z})$-classes of integral binary
forms in the genus) are the $\mathrm{GL}_2(\mathbb{Z})$-classes of primitive positive definite forms of discriminant $D$ in
the genus of $f$ (`mem_primPosForm_of_sameGenus`). -/
theorem genusClasses_eq_image (f : PosForms D) :
    genusClasses f.1 = glToQClass '' {G | glGenus G = Quotient.mk (genusSetoid D) f} := by
  ext c
  induction c using Quotient.inductionOn with
  | h Q =>
    change classOf Q ∈ _ ↔ _
    rw [classOf_mem_genusClasses_iff]
    constructor
    · intro h
      obtain ⟨h1, h2, h3⟩ := mem_primPosForm_of_sameGenus f.toPrim h
      exact ⟨Quotient.mk _ ⟨Q, h1, h2, h3⟩, Quotient.sound h.symm, rfl⟩
    · rintro ⟨G, hG, hc⟩
      induction G using Quotient.inductionOn with
      | h g =>
        have hs : SameGenus g.1 f.1 := Quotient.exact hG
        exact hs.symm.trans (classOf_eq_classOf_iff.mp hc).sameGenus

open Classical in
/-- **A sum over the classes of a genus** (`finsum` over `Siegel.genusClasses f`) is a finite sum over the
$\mathrm{GL}_2(\mathbb{Z})$-classes of `PrimPosForm D` in the genus. -/
theorem finsum_genusClasses [Fact (D < 0)] (f : PosForms D) (φ : QClass 2 → ℝ) :
    ∑ᶠ c ∈ genusClasses f.1, φ c =
      ∑ G ∈ Finset.univ.filter (fun G => glGenus G = Quotient.mk (genusSetoid D) f), φ (glToQClass G) := by
  rw [genusClasses_eq_image, finsum_mem_image glToQClass_injective.injOn]
  have hs : {G : Quotient (glSetoid D) | glGenus G = Quotient.mk (genusSetoid D) f} =
      ↑(Finset.univ.filter (fun G => glGenus G = Quotient.mk (genusSetoid D) f)) := by
    ext G; simp
  rw [hs, finsum_mem_coe_finset]

open Classical in
/-- **$\frac1{|\mathrm{Aut}|}$-weighted sums over the GL-classes of a genus are sums over its proper classes**
($D < 0$ fundamental): for every genus $\mathcal G$ and every function $\varphi$ of $\mathrm{GL}_2(\mathbb{Z})$-classes,
$$\sum_{G \in \mathcal G} \frac{\varphi(G)}{|\mathrm{Aut}(G)|} = \frac{1}{2w}\sum_{c \in \mathcal G\ \text{proper}} \varphi([c]_{\mathrm{GL}}),$$
by the fibre identity $\#\{\text{proper classes in } G\}\cdot|\mathrm{Aut}(G)| = 2w$ (`card_fiber_mul_aut`). -/
theorem sum_div_aut_genus [Fact (D < 0)] (𝒢 : Genera D) (φ : Quotient (glSetoid D) → ℝ) :
    ∑ G ∈ Finset.univ.filter (fun G => glGenus G = 𝒢), φ G / glClassAutCard G =
      (∑ c ∈ Finset.univ.filter (fun c => slGenus c = 𝒢), φ (slToGl c)) /
        (2 * NumberField.Units.torsionOrder (QField D)) := by
  set w := NumberField.Units.torsionOrder (QField D)
  have hw : (w : ℝ) ≠ 0 := by exact_mod_cast (NumberField.Units.torsionOrder_pos (QField D)).ne'
  have haut : ∀ G : Quotient (glSetoid D), (glClassAutCard G : ℝ) ≠ 0 := fun G => by
    intro h0
    have := card_fiber_mul_aut G
    have h0' : glClassAutCard G = 0 := by exact_mod_cast h0
    rw [h0', mul_zero] at this
    exact hw (by exact_mod_cast (by omega : w = 0))
  have hfib : ∀ G : Quotient (glSetoid D), (1 : ℝ) / glClassAutCard G =
      ((Finset.univ.filter fun c => slToGl c = G).card : ℝ) / (2 * w) := fun G => by
    rw [div_eq_div_iff (haut G) (by positivity)]
    have := card_fiber_mul_aut G
    rw [one_mul]
    exact_mod_cast this.symm
  rw [← Finset.sum_fiberwise_of_maps_to (g := slToGl)
    (t := Finset.univ.filter (fun G => glGenus G = 𝒢)) (fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rwa [← slGenus_eq_glGenus]), Finset.sum_div]
  refine Finset.sum_congr rfl fun G hG => ?_
  rw [Finset.sum_congr rfl (fun c hc => by rw [(Finset.mem_filter.mp hc).2]), Finset.sum_const,
    nsmul_eq_mul]
  have hset : ((Finset.univ.filter fun c => slGenus c = 𝒢).filter fun c => slToGl c = G) =
      Finset.univ.filter fun c => slToGl c = G := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro h
    rw [slGenus_eq_glGenus, h]
    exact (Finset.mem_filter.mp hG).2
  rw [hset, div_eq_mul_one_div (φ G), hfib G]
  ring

/-! ### The mass -/

open Classical in
/-- **The mass of a genus of binary forms** ($D < 0$ fundamental, $t$ prime factors, $h = h(D)$ =
`classNumber (QField D)`, $w$ = `torsionOrder (QField D)` $= |\mathcal O_{K_D}^\times|$): for every primitive positive
definite form $f$ of discriminant $D$, with the repo's `Siegel.mass` ($\mathrm{GL}_2(\mathbb{Z})$-classes in the genus
of $f$, weights $1/|\mathrm{Aut}|$, $\mathrm{Aut} \le \mathrm{GL}_2(\mathbb{Z})$),
$$\mathrm{Mass}(f) = \sum_{[g] \in \mathrm{Gen}(f)} \frac{1}{|\mathrm{Aut}(g)|} = \frac{h}{2^{t-1}\cdot 2w}.$$
Every genus has the same mass, $\frac{1}{2^{t-1}}$ of the total $\mathrm{GL}$-mass $\frac{h}{2w}$ (Dirichlet's formula for the
$\mathrm{SL}$-mass is $h/w$). Source: Siegel's mass formula in the binary case; Conway–Sloane, *SPLAG*, Ch. 16
[unverified locator]; Cox, Thm. 3.15 [unverified locator]. -/
@[kb "gauss1801" "§252 (equal number of classes per genus) [unverified]"]
theorem mass_genus [Fact (D < 0)] (f : PosForms D) :
    Siegel.mass f.1 = (classNumber (QField D) : ℝ) /
      (2 ^ (D.natAbs.primeFactors.card - 1) * (2 * NumberField.Units.torsionOrder (QField D))) := by
  have hD : D < 0 := Fact.out
  rw [Siegel.mass, finsum_genusClasses f (fun c => ((c.autCard : ℕ) : ℝ)⁻¹)]
  have h1 : ∀ G : Quotient (glSetoid D), (((glToQClass G).autCard : ℕ) : ℝ)⁻¹ = 1 / glClassAutCard G := by
    intro G
    induction G using Quotient.inductionOn with
    | h g => simp [glToQClass, glClassAutCard]
  simp_rw [h1]
  rw [sum_div_aut_genus (Quotient.mk (genusSetoid D) f) (fun _ => 1)]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard := card_slClasses_in_genus hD (Quotient.mk (genusSetoid D) f)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcard
  rw [← hcard]
  push_cast
  have hw : (NumberField.Units.torsionOrder (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.Units.torsionOrder_pos (QField D)).ne'
  field_simp

/-- **The mass of a genus, explicitly** ($D < 0$ fundamental): $\mathrm{Mass} = \dfrac{h}{2^{t-1}\cdot 2w}$ with
$w = 6$ for $D = -3$, $w = 4$ for $D = -4$ and $w = 2$ for $D < -4$ (`torsionOrder_of_neg`). -/
theorem mass_genus_explicit [Fact (D < 0)] (f : PosForms D) :
    Siegel.mass f.1 = (classNumber (QField D) : ℝ) /
      (2 ^ (D.natAbs.primeFactors.card - 1) * (2 * (if D = -3 then 6 else if D = -4 then 4 else 2 : ℕ))) := by
  rw [mass_genus, torsionOrder_of_neg Fact.out]

end QuadFormsKB.Binary
