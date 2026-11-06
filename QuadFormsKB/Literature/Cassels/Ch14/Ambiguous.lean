/-
# Cassels, Chapter 14, §4: ambiguous forms and classes

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §1, p. 332, §4, pp. 341–343, and §6, p. 345.

For a discriminant $D \ne 0$ and the group $\mathcal G$ = `FormClass D` (`Ch14/Group.lean`):

* a class $\mathfrak C$ is *ambiguous* if $\mathfrak C^2 = \mathfrak E$ (4.1) (`IsAmbiguous`); these are exactly the
  classes whose forms are improperly equivalent to themselves (14.r7, (1.13), `isAmbiguous_iff_improper`), and they
  form the subgroup $\mathcal A$ of elements of order dividing $2$ (14.r10 (i), `ambiguousSubgroup`);
* the *ambiguous forms* of the first and second kind are $[a, 0, c]$ and $[a, a, c]$ ((4.6)–(4.7), `IsAmbiguousForm`);
  they are ambiguous (p. 332, `isAmbiguous_of_isAmbiguousForm`), and every ambiguous class contains one (Lemma 4.1,
  `exists_ambiguousForm`);

The counts of ambiguous forms (Lemma 4.2) are in `Ch14/AmbiguousForms.lean`.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Group
import QuadFormsKB.Literature.Cassels.Ch14.AmbiguousForms

namespace QuadFormsKB.Composition

open BinQF Binary FormClass

variable {D : ℤ}

/-! ### Ambiguous classes -/

/-- **Ambiguous classes** (Cassels, Ch. 14, (1.13), p. 332, and (4.1), p. 341): $\mathfrak C^2 = \mathfrak E$, i.e.
$\mathfrak C = \mathfrak C^{-1}$. -/
@[kb "cassels1978" "Ch. 14, §4, (4.1), p. 341 (ambiguous classes)"]
def IsAmbiguous [NonzeroDisc D] (C : FormClass D) : Prop := C ^ 2 = 1

/-- **The group $\mathcal A$ of ambiguous classes** (Cassels, Ch. 14, p. 332 and §4, p. 341): the kernel of
$\mathfrak C \mapsto \mathfrak C^2$, i.e. the elements of order $2$ together with $\mathfrak E$ (§6, p. 345, (i)). -/
@[kb "cassels1978" "Ch. 14, §4, p. 341; §6, p. 345 (i) (the group 𝒜 of ambiguous classes)"]
noncomputable def ambiguousSubgroup [NonzeroDisc D] : Subgroup (FormClass D) := (powMonoidHom 2 : FormClass D →* FormClass D).ker

private theorem subst_conjForm (p q r s : ℤ) (f : BinQF) :
    BinQF.subst p q r s (conjForm f) = BinQF.subst p q (-r) (-s) f := by
  apply ext_abc <;> simp [BinQF.subst, conjForm]; ring

theorem mem_ambiguousSubgroup [NonzeroDisc D] (C : FormClass D) : C ∈ ambiguousSubgroup ↔ IsAmbiguous C := by
  rw [ambiguousSubgroup, MonoidHom.mem_ker, powMonoidHom_apply]
  rfl

/-- **An ambiguous class is one whose forms are improperly equivalent to themselves** (Cassels, Ch. 14, p. 332, after
(1.13), and §4, p. 341): $\mathfrak C^2 = \mathfrak E$ iff $f = f \circ T$ for some $T \in \mathrm{GL}_2(\mathbb Z)$
with $\det T = -1$ (here $T = \begin{pmatrix} p & q \\ r & s \end{pmatrix}$). -/
@[kb "cassels1978" "Ch. 14, §1, p. 332 (after (1.13)); §4, p. 341"]
theorem isAmbiguous_iff_improper [NonzeroDisc D] (f : PrimForm D) :
    IsAmbiguous (mk f) ↔ ∃ p q r s : ℤ, p * s - q * r = -1 ∧ BinQF.subst p q r s f.1 = f.1 := by
  have h1 : IsAmbiguous (mk f) ↔ mk f = (mk f)⁻¹ := by
    unfold IsAmbiguous
    rw [pow_two, mul_eq_one_iff_eq_inv]
  rw [h1, mk_inv]
  refine eq_comm.trans (mk_eq_mk.trans ((sLEquiv_iff _ _).trans ?_))
  constructor
  · rintro ⟨p, q, r, s, h, e⟩
    refine ⟨p, q, -r, -s, by linarith, ?_⟩
    rw [← subst_conjForm]; exact e
  · rintro ⟨p, q, r, s, h, e⟩
    refine ⟨p, q, -r, -s, by linarith, ?_⟩
    rw [subst_conjForm]; simpa using e

/-! ### Ambiguous forms -/

/-- **Ambiguous forms are ambiguous** (Cassels, Ch. 14, p. 332: "the forms of the shape (1.14) and (1.15) are clearly
ambiguous"): $[a, 0, c]$ is fixed by $y \mapsto -y$ and $[a, a, c]$ by $x \mapsto x + y$, $y \mapsto -y$. -/
@[kb "cassels1978" "Ch. 14, §1, (1.14)–(1.15), pp. 332–333"]
theorem isAmbiguous_of_isAmbiguousForm [NonzeroDisc D] (f : PrimForm D) (h : IsAmbiguousForm f.1) :
    IsAmbiguous (mk f) := by
  rw [isAmbiguous_iff_improper]
  rcases h with h | h
  · exact ⟨1, 0, 0, -1, by norm_num, by
      apply ext_abc <;> simp [BinQF.subst, h]⟩
  · exact ⟨1, 1, 0, -1, by norm_num, by
      apply ext_abc <;> simp [BinQF.subst, h]; ring⟩

/-- **Cassels, Ch. 14, Lemma 4.1** (p. 341): *every ambiguous class contains at least one ambiguous form.* -/
@[kb "cassels1978" "Ch. 14, Lemma 4.1, p. 341"]
theorem exists_ambiguousForm [NonzeroDisc D] (C : FormClass D) (hC : IsAmbiguous C) :
    ∃ f : PrimForm D, mk f = C ∧ IsAmbiguousForm f.1 := by
  obtain ⟨f, rfl⟩ := mk_surjective C
  obtain ⟨p, q, r, s, h, e⟩ := (isAmbiguous_iff_improper f).1 hC
  obtain ⟨g, hg, hamb⟩ := exists_sLEquiv_ambiguousForm (by rw [f.2.2]; exact NonzeroDisc.ne_zero) ⟨p, q, r, s, h, e⟩
  exact ⟨⟨g, QuadFormsKB.Composition.SLEquiv.isPrimitive hg f.2.1,
    (QuadFormsKB.Composition.SLEquiv.disc_eq hg).symm.trans f.2.2⟩, mk_eq_mk.2 hg.symm, hamb⟩

end QuadFormsKB.Composition
