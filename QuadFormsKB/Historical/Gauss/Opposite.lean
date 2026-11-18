import QuadFormsKB.Historical.Gauss.Reduction
import QuadFormsKB.Historical.Gauss.Representations

/-!
# Opposite forms, improper equivalence, and proper representations (*Disquisitiones Arithmeticae*, Arts. 172, 177, 213-214, 224)

Four statements from the historical sources. Gauss's opposite form of $(a, b, c)$ is $(a, -b, c)$, the library's `conjForm`
(`conjForm_gaussForm`). A substitution $x = \alpha x' + \beta y'$, $y = \gamma x' + \delta y'$ is *proper* if
$\alpha\delta - \beta\gamma = 1$ and *improper* if $\alpha\delta - \beta\gamma = -1$ (Art. 158).

* (Arts. 213-214, end), proved: `conjForm_subst` ($\mathrm{subst}(\alpha, -\beta, \gamma, -\delta) f$ is the
  opposite of $\mathrm{subst}(\alpha, \beta, \gamma, \delta) f$), `subst_negOffDiagonal_iff` (the pointwise
  statement), `substTransformations_neg_eq_preimage` and `improperEquivProper` (the transformations of determinant
  $-e$ from $f$ to $F$ correspond bijectively to the transformations of determinant $e$ from $f$ to the opposite of
  $F$, by $(\alpha, \beta, \gamma, \delta) \mapsto (\alpha, -\beta, \gamma, -\delta)$), for every integer $e$.
* (Art. 177), proved: `improper_of_proper_opposite` and `proper_and_improper_of_both_modes`, for
  arbitrary binary forms (no sign condition on the determinant).
* (Art. 172, improper version), proved: `improperlyEquivalent_iff_sLEquiv_conjForm`,
  `improperlyEquivalent_cases` and the full Gauss condition `art172_improper_iff`, for reduced positive definite forms.
* (Art. 224), partly proved: properly equivalent forms primitively represent the same numbers
  (`hasPrimitiveRepresentation_iff_of_sLEquiv`) and the same set of values (roots $\sqrt{D} \pmod M$)
  (`primitiveRepresentationValues_eq_of_sLEquiv`). NOT proved (not in the library): the clause "representations by
  forms of different classes cannot belong to the same root" (Gauss, Art. 168-169: a root $N$ attached to a
  primitive representation of $M$ determines the proper class of $(M, N, (N^2 - D)/M)$), and the class-field
  reformulation.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-! ### Arts. 213-214: improper transformations via the opposite form -/

/-- **Reflecting the second column and the off-diagonal entries:** the opposite form of $f(\alpha x + \beta y,
\gamma x + \delta y)$ is $f(\alpha x - \beta y, \gamma x - \delta y)$, i.e.
`conjForm (subst α β γ δ f) = subst α (-β) γ (-δ) f`. -/
theorem conjForm_subst (α β γ δ : ℤ) (f : BinQF) :
    conjForm (subst α β γ δ f) = subst α (-β) γ (-δ) f := by
  rw [conjForm_eq_subst, subst_subst]
  simp

private theorem conjForm_inj_iff (X Y : BinQF) : conjForm X = conjForm Y ↔ X = Y :=
  ⟨fun h => by simpa [conjForm_conjForm] using congrArg conjForm h, fun h => by rw [h]⟩

/-- **Improper containment via the opposite form, pointwise** (*Disq. Arith.*
Arts. 213-214, end, via Art. 159): the substitution $(\alpha, \beta, \gamma, \delta)$ takes $f$ to $F$ iff the
substitution $(\alpha, -\beta, \gamma, -\delta)$ takes $f$ to the opposite form of $F$ (`conjForm F`), and the
determinant of the second is the negative of the determinant of the first. -/
@[kb "gauss1801" "Art. 213-214"]
theorem subst_negOffDiagonal_iff (f F : BinQF) (α β γ δ : ℤ) :
    subst α β γ δ f = F ↔ subst α (-β) γ (-δ) f = conjForm F := by
  rw [← conjForm_subst, conjForm_inj_iff]

/-- The determinant of $(\alpha, -\beta, \gamma, -\delta)$ is the negative of that of $(\alpha, \beta, \gamma,
\delta)$. -/
theorem det_negOffDiagonal (α β γ δ : ℤ) : α * (-δ) - (-β) * γ = -(α * δ - β * γ) := by ring

/-- **The set of transformations of a given determinant:** the integer quadruples $(\alpha, \beta, \gamma, \delta)$
of determinant $\alpha\delta - \beta\gamma = d$ with $f(\alpha x + \beta y, \gamma x + \delta y) = F$. -/
def substTransformations (f F : BinQF) (d : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {t | t.1 * t.2.2.2 - t.2.1 * t.2.2.1 = d ∧ subst t.1 t.2.1 t.2.2.1 t.2.2.2 f = F}

/-- The involution $(\alpha, \beta, \gamma, \delta) \mapsto (\alpha, -\beta, \gamma, -\delta)$ of the quadruples. -/
def negOffDiagonal : (ℤ × ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ × ℤ) where
  toFun t := (t.1, -t.2.1, t.2.2.1, -t.2.2.2)
  invFun t := (t.1, -t.2.1, t.2.2.1, -t.2.2.2)
  left_inv := by rintro ⟨a, b, c, d⟩; simp
  right_inv := by rintro ⟨a, b, c, d⟩; simp

/-- **Improper transformations of $f$ into $F$ are the reflections of the proper ones into the opposite of $F$**
(*Disq. Arith.* Arts. 213-214, end): for every integer $e$, a quadruple has determinant
$-e$ and takes $f$ to $F$ iff its image $(\alpha, -\beta, \gamma, -\delta)$ has determinant $e$ and takes $f$ to
the opposite form of $F$. Taking $e > 0$ and $F$ of determinant $e$ times that of $f$ this is Gauss's statement
(improper containment of $F$ in $f$ is proper containment of the opposite of $F$ in $f$). Proved for all
integers $e$ and all binary forms $f$, $F$. -/
@[kb "gauss1801" "Art. 213-214"]
theorem substTransformations_neg_eq_preimage (f F : BinQF) (e : ℤ) :
    substTransformations f F (-e) = negOffDiagonal ⁻¹' substTransformations f (conjForm F) e := by
  ext ⟨α, β, γ, δ⟩
  show (α * δ - β * γ = -e ∧ subst α β γ δ f = F) ↔
    (α * (-δ) - (-β) * γ = e ∧ subst α (-β) γ (-δ) f = conjForm F)
  rw [← subst_negOffDiagonal_iff, det_negOffDiagonal]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩

/-- **The bijection of Arts. 213-214:** $(\alpha, \beta, \gamma, \delta) \mapsto (\alpha, -\beta, \gamma, -\delta)$
is an equivalence between the transformations of determinant $-e$ from $f$ to $F$ and those of determinant $e$ from
$f$ to the opposite form of $F$ (*Disq. Arith.* Arts. 213-214, end). -/
@[kb "gauss1801" "Art. 213-214"]
def improperEquivProper (f F : BinQF) (e : ℤ) :
    substTransformations f F (-e) ≃ substTransformations f (conjForm F) e :=
  Equiv.subtypeEquiv negOffDiagonal (fun t => by
    have := Set.ext_iff.mp (substTransformations_neg_eq_preimage f F e) t
    simpa using this)

/-! ### Art. 177: improper transformations from the opposite form -/

/-- **Improper equivalence** (*Disq. Arith.* Art. 158): $g$ is obtained from $f$ by a substitution of
determinant $-1$. -/
def ImproperlyEquivalent (f g : BinQF) : Prop :=
  ∃ p q r s : ℤ, p * s - q * r = -1 ∧ subst p q r s f = g

/-- **An improper transformation from a proper one into the opposite form** (the historical sources;
*Disq. Arith.* Art. 177): if the proper transformation $x = \alpha p + \beta q$, $y = \gamma p + \delta q$ takes $F$
into the opposite form of $f$, then $x = \alpha t - \beta u$, $y = \gamma t - \delta u$ is an improper
transformation (determinant $-1$) of $F$ into $f$. Proved for arbitrary binary forms (Gauss's statement is for
negative determinant; the proof does not use it). -/
@[kb "gauss1801" "Art. 177"]
theorem improper_of_proper_opposite {f F : BinQF} {α β γ δ : ℤ} (hdet : α * δ - β * γ = 1)
    (h : subst α β γ δ F = conjForm f) :
    α * (-δ) - (-β) * γ = -1 ∧ subst α (-β) γ (-δ) F = f := by
  refine ⟨by rw [det_negOffDiagonal, hdet], ?_⟩
  rw [← conjForm_subst, h, conjForm_conjForm]

/-- **Equivalent in both modes** (*Disq. Arith.* Art. 177): if $F$ is properly equivalent
to $f$ and also to the opposite form of $f$, then there are both a proper (determinant $1$) and an improper
(determinant $-1$) transformation of $F$ into $f$. -/
@[kb "gauss1801" "Art. 177"]
theorem proper_and_improper_of_both_modes {f F : BinQF} (h1 : SLEquiv F f) (h2 : SLEquiv F (conjForm f)) :
    (∃ p q r s : ℤ, p * s - q * r = 1 ∧ subst p q r s F = f) ∧ ImproperlyEquivalent F f := by
  refine ⟨(sLEquiv_iff _ _).mp h1, ?_⟩
  obtain ⟨p, q, r, s, hd, h⟩ := (sLEquiv_iff _ _).mp h2
  exact ⟨p, -q, r, -s, (improper_of_proper_opposite hd h).1, (improper_of_proper_opposite hd h).2⟩

/-! ### Art. 172: improper equivalence of reduced forms -/

/-- **Improper equivalence is proper equivalence to the opposite form** (the historical sources;
*Disq. Arith.* Art. 172, parenthetical remark): $f$ is improperly equivalent to $g$ iff $f$ is properly equivalent to
the opposite form of $g$. Holds for arbitrary binary forms. -/
@[kb "gauss1801" "Art. 172"]
theorem improperlyEquivalent_iff_sLEquiv_conjForm (f g : BinQF) :
    ImproperlyEquivalent f g ↔ SLEquiv f (conjForm g) := by
  rw [sLEquiv_iff]
  constructor
  · rintro ⟨p, q, r, s, hd, h⟩
    exact ⟨p, -q, r, -s, by linear_combination -hd, by rw [← conjForm_subst, h]⟩
  · rintro ⟨p, q, r, s, hd, h⟩
    exact ⟨p, -q, r, -s, by linear_combination -hd, by rw [← conjForm_subst, h, conjForm_conjForm]⟩

/-- The opposite of a reduced form is reduced. -/
theorem isReduced_conjForm {f : BinQF} (hf : IsReduced f) : IsReduced (conjForm f) := by
  simpa [IsReduced, abs_neg] using hf

/-- Positive definiteness is preserved by the opposite form. -/
theorem posDef_conjForm {f : BinQF} (hf : f.PosDef) : (conjForm f).PosDef := by
  intro x y hxy
  have hne : (x, -y) ≠ (0, 0) := by
    intro h
    apply hxy
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by linarith [h.2]⟩
  have e : (conjForm f).eval x y = f.eval x (-y) := by
    simp only [eval_eq, a_conjForm, b_conjForm, c_conjForm]; ring
  rw [e]
  exact hf x (-y) hne

/-- **An ambiguous reduced form, or one with $a = c$, is properly equivalent to its opposite:** if $b = 0$, or
$|b| = a$, or $a = c$ (library coefficients $a x^2 + b x y + c y^2$, reduced), then
`SLEquiv f (conjForm f)`. The substitutions used: none ($b = 0$), $x \mapsto x \mp y$ ($|b| = a$), and
$(x, y) \mapsto (-y, x)$ ($a = c$). -/
theorem sLEquiv_conjForm_of_ambiguous {f : BinQF} (hfr : IsReduced f)
    (h : f.b = 0 ∨ |f.b| = f.a ∨ f.a = f.c) : SLEquiv f (conjForm f) := by
  have ha : 0 ≤ f.a := le_trans (abs_nonneg _) hfr.1
  rcases h with hb | hb | hac
  · have : conjForm f = f := ext_abc (by simp) (by simp [hb]) (by simp)
    rw [this]; exact SLEquiv.refl f
  · rcases (abs_eq ha).mp hb with hb | hb
    · refine (sLEquiv_iff _ _).mpr ⟨1, -1, 0, 1, by ring, ext_abc ?_ ?_ ?_⟩ <;>
        simp only [subst, a_mk, b_mk, c_mk, a_conjForm, b_conjForm, c_conjForm] <;> linarith
    · refine (sLEquiv_iff _ _).mpr ⟨1, 1, 0, 1, by ring, ext_abc ?_ ?_ ?_⟩ <;>
        simp only [subst, a_mk, b_mk, c_mk, a_conjForm, b_conjForm, c_conjForm] <;> linarith
  · refine (sLEquiv_iff _ _).mpr ⟨0, -1, 1, 0, by ring, ext_abc ?_ ?_ ?_⟩ <;>
      simp only [subst, a_mk, b_mk, c_mk, a_conjForm, b_conjForm, c_conjForm] <;> linarith

/-- **Reduced forms are improperly equivalent only to themselves or their opposites** (the historical sources;
*Disq. Arith.* Art. 172): for reduced positive definite $f$, $g$, if $f$ is improperly equivalent to $g$ then
$g = f$ or $g$ is the opposite of $f$. -/
@[kb "gauss1801" "Art. 172"]
theorem improperlyEquivalent_cases {f g : BinQF} (hf : f.PosDef) (hfr : IsReduced f) (hgr : IsReduced g)
    (h : ImproperlyEquivalent f g) : g = f ∨ g = conjForm f := by
  rw [improperlyEquivalent_iff_sLEquiv_conjForm] at h
  by_cases e : f = conjForm g
  · right; rw [e, conjForm_conjForm]
  · left
    have := (art172_eq_or_opposite hf hfr (isReduced_conjForm hgr) h e).1
    simpa [conjForm_conjForm] using congrArg conjForm this

/-- **Proper equivalence of reduced forms** (last clause; *Disq. Arith.* Art. 172): for
reduced positive definite $f$, $g$, if $f$ is properly equivalent to $g$ then $g = f$ or $g$ is the opposite of
$f$. So reduced forms that are neither identical nor opposite are in no way equivalent (together with
`improperlyEquivalent_cases`). -/
@[kb "gauss1801" "Art. 172"]
theorem sLEquiv_cases {f g : BinQF} (hf : f.PosDef) (hfr : IsReduced f) (hgr : IsReduced g)
    (h : SLEquiv f g) : g = f ∨ g = conjForm f := by
  by_cases e : f = g
  · exact Or.inl e.symm
  · exact Or.inr (art172_eq_or_opposite hf hfr hgr h e).1

/-- **Improper equivalence of reduced forms, Gauss's condition** (*Disq. Arith.*
Art. 172, improper version): for reduced positive definite forms $f$, $g$ (library coefficients $a x^2 + b x y +
c y^2$, so Gauss's $(A, B, C)$ has $b = 2B$), $f$ is improperly equivalent to $g$ iff $g$ is the opposite of $f$,
or $g = f$ and $f$ is ambiguous ($b = 0$ or $|b| = a$, Gauss's $2B = 0$ or $\pm A$) or has $a = c$. In particular,
for $g$ not opposite to $f$ (and $g \ne f$ when $f$ is not its own opposite) the form $g$ is improperly equivalent to
$f$ iff identical to $f$ and ambiguous or with $a = c$. (When $g$ is the opposite of $f$, improper equivalence
is trivial: it is the substitution $(1, 0, 0, -1)$.) -/
@[kb "gauss1801" "Art. 172"]
theorem art172_improper_iff {f g : BinQF} (hf : f.PosDef) (hfr : IsReduced f) (hgr : IsReduced g) :
    ImproperlyEquivalent f g ↔
      g = conjForm f ∨ (g = f ∧ (f.b = 0 ∨ |f.b| = f.a ∨ f.a = f.c)) := by
  rw [improperlyEquivalent_iff_sLEquiv_conjForm]
  constructor
  · intro h
    by_cases e : f = conjForm g
    · left; rw [e, conjForm_conjForm]
    · right
      obtain ⟨h1, h2⟩ := art172_eq_or_opposite hf hfr (isReduced_conjForm hgr) h e
      have hg : g = f := by simpa [conjForm_conjForm] using congrArg conjForm h1
      refine ⟨hg, ?_⟩
      rcases h2 with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
  · rintro (rfl | ⟨rfl, hamb⟩)
    · rw [conjForm_conjForm]; exact SLEquiv.refl _
    · exact sLEquiv_conjForm_of_ambiguous hfr hamb

/-! ### Art. 224: proper equivalence and primitive representations -/

/-- **Primitive representation:** $M$ is represented by $f$ primitively (properly) if $f(m, n) = M$ for
coprime integers $m$, $n$. -/
def HasPrimitiveRepresentation (f : BinQF) (M : ℤ) : Prop :=
  ∃ m n : ℤ, Int.gcd m n = 1 ∧ f.eval m n = M

private theorem hasPrimitiveRepresentation_of_sLEquiv {f g : BinQF} (h : SLEquiv f g) {M : ℤ}
    (hg : HasPrimitiveRepresentation g M) : HasPrimitiveRepresentation f M := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp h
  obtain ⟨m, n, hmn, hM⟩ := hg
  exact ⟨p * m + q * n, r * m + s * n, by
    rw [gcd_substVector p q r s m n (Or.inl hd)]; exact hmn, by rw [← eval_subst]; exact hM⟩

/-- **Properly equivalent forms primitively represent the same numbers** (*Disq. Arith.*
Art. 224, first clause): if $f$ and $g$ are properly equivalent then $M$ is represented by $f$ with coprime
variables iff it is represented by $g$ with coprime variables. -/
@[kb "gauss1801" "Art. 224"]
theorem hasPrimitiveRepresentation_iff_of_sLEquiv {f g : BinQF} (h : SLEquiv f g) (M : ℤ) :
    HasPrimitiveRepresentation f M ↔ HasPrimitiveRepresentation g M :=
  ⟨hasPrimitiveRepresentation_of_sLEquiv h.symm, hasPrimitiveRepresentation_of_sLEquiv h⟩

/-- **The values (roots) of the primitive representations of $M$ by $(a, b, c)$** (*Disq. Arith.* Arts. 155, 168):
the set of integers $v = \mu (m b + n c) - \nu (m a + n b)$ (`art155Value`) over all $m$, $n$, $\mu$, $\nu$ with
$\mu m + \nu n = 1$ (so $\gcd(m, n) = 1$) and $a m^2 + 2 b m n + c n^2 = M$. Each is a root of $x^2 \equiv b^2 - ac
\pmod M$ (`art155_value_sq`), and by `art155Value_modEq_of_bezout`, `exists_bezout_art155Value_eq` the set is a union
of residue classes modulo $M$. -/
def primitiveRepresentationValues (a b c M : ℤ) : Set ℤ :=
  {v | ∃ m n μ ν : ℤ, μ * m + ν * n = 1 ∧ (gaussForm a b c).eval m n = M ∧ art155Value a b c m n μ ν = v}

private theorem values_subset_of_subst {a b c a' b' c' p q r s : ℤ} (hd : p * s - q * r = 1)
    (h : subst p q r s (gaussForm a b c) = gaussForm a' b' c') (M : ℤ) :
    primitiveRepresentationValues a' b' c' M ⊆ primitiveRepresentationValues a b c M := by
  rintro v ⟨m, n, μ, ν, hb, hM, hv⟩
  refine ⟨p * m + q * n, r * m + s * n, μ * s - ν * r, ν * p - μ * q,
    by linear_combination (μ * m + ν * n) * hd + hb, ?_, ?_⟩
  · rw [← h, eval_subst] at hM; exact hM
  · rw [← hv]
    rw [subst_gaussForm] at h
    obtain ⟨rfl, rfl, rfl⟩ := gaussForm_inj h.symm
    unfold art155Value
    ring

/-- **Properly equivalent forms have the same roots** (*Disq. Arith.* Art. 224, with
Art. 167): if $(a, b, c)$ and $(a', b', c')$ are properly equivalent, then the set of values (roots of
$x^2 \equiv b^2 - ac \pmod M$) of the primitive representations of $M$ is the same for both. In fact the proper
transformation carries a primitive representation with Bezout pair $(\mu, \nu)$ to one with the **identical**
value (not merely congruent modulo $M$): see the proof of `primitiveRepresentationValues_eq_of_sLEquiv`.
Not proved here: that representations by forms of different classes cannot belong to the same root (proved in
`RootForms.lean` as `art224_sLEquiv_of_modEq` and `art224_iff`). -/
@[kb "gauss1801" "Art. 224"]
theorem primitiveRepresentationValues_eq_of_sLEquiv {a b c a' b' c' : ℤ}
    (h : SLEquiv (gaussForm a b c) (gaussForm a' b' c')) (M : ℤ) :
    primitiveRepresentationValues a b c M = primitiveRepresentationValues a' b' c' M := by
  obtain ⟨p, q, r, s, hd, h1⟩ := (sLEquiv_iff _ _).mp h
  obtain ⟨p', q', r', s', hd', h2⟩ := (sLEquiv_iff _ _).mp h.symm
  exact Set.Subset.antisymm (values_subset_of_subst hd' h2 M) (values_subset_of_subst hd h1 M)

end QuadFormsKB.Historical.Gauss
