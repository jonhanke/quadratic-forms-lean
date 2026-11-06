/-
# Conway–Sloane, Ch. 15, §3.5: spinor genera of binary forms (Estes–Pall)

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §3.5, p. 366
(`conwaysloane1999`): *Estes and Pall [Est1] have given a full investigation of spinor genera in the binary case and
have shown in particular that two forms are in the same spinor genus if and only if their quotient is a fourth power
in the group* (D. R. Estes and G. Pall, *Spinor genera of binary quadratic forms*, J. Number Theory **5** (1973),
421–432).

**Conventions (book $\to$ Lean).**
* A form is `QuadForm ℤ n`; a binary form of discriminant $D$ is Cassels' `Composition.PrimForm D` (primitive
  $[a, b, c] = ax^2 + bxy + cy^2$ with $b^2 - 4ac = D$), and "the group" is Cassels' group $\mathcal G$ =
  `Composition.FormClass D` of **proper** classes under Dirichlet composition (Cassels, Ch. 14, Thm. 2.1), with
  $[a, b, c]^{-1} = [a, -b, c]$ (`Composition.FormClass.mk_inv`).
* The lattice-level proper spinor genus is O'Meara's $\operatorname{spn}^+$ (`Lattices.SameProperSpinorGenus`, §102A:
  $M = \sigma\Sigma L$ with $\sigma \in O^+(V)$ and $\Sigma$ in the adelic spinor kernel $J'_V$).
* **The form-level proper spinor genus** (`SameProperSpinorGenusForm f g`): there is $\gamma \in \mathrm{GL}_n(\mathbb Q)$
  with $\det\gamma = 1$ and $f(\gamma x) = g(x)$, such that the lattice $\gamma\mathbb Z^n$ (whose Gram form in the basis
  of the columns of $\gamma$ is $g$) lies in $\operatorname{spn}^+(\mathbb Z^n)$ in the space $(\mathbb Q^n, f)$. The
  requirement $\det\gamma = 1$ carries the orientation: a lattice does not remember whether its Gram form is $g$ or the
  improperly equivalent form, but a basis of determinant $1$ relative to the standard one does.
* The **improper** (lattice-level) reading, `SameSpinorGenusForm`, drops $\det\gamma = 1$ and uses $\operatorname{spn}$.

**Which reading.** The book's statement is about the group of *proper* classes, so it must be read with the proper
spinor genus. Under the improper reading it is false whenever $\mathcal G^2 \ne \mathcal G^4$: a form $f$ and its
improperly equivalent form $\bar f = [a, -b, c]$ give the same lattice, so they are always in the same improper spinor
genus (`sameSpinorGenusForm_conjForm`), while $[f][\bar f]^{-1} = [f]^2$; hence the improper reading would force
$\mathcal G^2 = \mathcal G^4$ (`sq_mem_fourth_powers_of_improper`). This fails for instance for $D = -56$, where
$\mathcal G \cong \mathbb Z/4$ (classes $[1,0,14], [3,2,5], [2,0,7], [3,-2,5]$; the class-group computation is not
formalized here). The hypothesis "$D$ not a square" is Estes–Pall's setting (the binary space is anisotropic over
$\mathbb Q$), not printed in the book.

**Proves**
* `SameProperSpinorGenusForm`, `SameSpinorGenusForm` (definitions); `SameProperSpinorGenusForm.refl`;
  `SameProperSpinorGenusForm.sameSpinorGenusForm`;
* `SameProperSpinorGenusForm.sameGenus`: forms in the same proper spinor genus are in the same genus
  (`Siegel.SameGenus`; unconditional, from O'Meara's $\operatorname{spn}^+ \subseteq \operatorname{gen}^+$);
* `EstesPallStatement` (**named statement**, the book's claim in the proper reading) and its consequences
  `EstesPallStatement.sameGenus_of_fourth`, `EstesPallStatement.fourth_of_sameGenus_iff`;
* `sameSpinorGenusForm_conjForm`, `sq_mem_fourth_powers_of_improper`: the improper reading forces
  $\mathcal G^2 = \mathcal G^4$ (why the proper reading is the right one).

**Proved later.** `EstesPallStatement` is a theorem, `EstesPall.estesPallStatement` (`Section3EstesPallOnlyIf.lean`,
both directions, for every $D \ne 0$). The original plan noted here: it needs the dictionary between proper classes in a proper spinor genus
of binary lattices and the class group (the action of the idèles of the quadratic algebra
$\mathbb Q(\sqrt D)$; $O^+(V) \cong E^\times/\mathbb Q^\times$ via $\alpha \mapsto \alpha/\bar\alpha$ and the spinor norm
of $\alpha/\bar\alpha$ is $N(\alpha)$), which the library does not have.
-/
import QuadFormsKB.Tamagawa.RatBridge
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Literature.Cassels.Ch14.GenusCosets
import QuadFormsKB.Tamagawa.BinaryNormOne

open NumberField Matrix

noncomputable section

namespace QuadFormsKB.ConwaySloane.EstesPall

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.Tamagawa.RatBridge

variable {n : ℕ}

/-- **The form-level proper spinor genus** (Conway–Sloane, Ch. 15, §3.5, p. 366, in the proper reading; O'Meara
§102A for lattices): $g$ is in the proper spinor genus of $f$ if $g(x) = f(\gamma x)$ for some $\gamma \in
\mathrm{GL}_n(\mathbb Q)$ with $\det\gamma = 1$ such that $\gamma\mathbb Z^n \in \operatorname{spn}^+(\mathbb Z^n)$ in
$(\mathbb Q^n, f)$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (spinor genus of binary forms, proper reading)"]
def SameProperSpinorGenusForm (f g : QuadForm ℤ n) : Prop :=
  ∃ γ : GL (Fin n) ℚ, γ.val.det = 1 ∧ (∀ x : Fin n → ℚ, f.evalIn ℚ (γ.val *ᵥ x) = g.evalIn ℚ x) ∧
    SameProperSpinorGenus (formF (up f)) Lattices.stdLat ⟨latOf γ, latOf_isLattice γ⟩

/-- **The form-level spinor genus, improper (lattice) reading**: $g(x) = f(\gamma x)$ for some $\gamma \in
\mathrm{GL}_n(\mathbb Q)$ (any determinant) with $\gamma\mathbb Z^n \in \operatorname{spn}(\mathbb Z^n)$ in
$(\mathbb Q^n, f)$. Recorded to show that the book's statement needs the proper reading. -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (spinor genus of binary forms, improper reading)"]
def SameSpinorGenusForm (f g : QuadForm ℤ n) : Prop :=
  ∃ γ : GL (Fin n) ℚ, (∀ x : Fin n → ℚ, f.evalIn ℚ (γ.val *ᵥ x) = g.evalIn ℚ x) ∧
    SameSpinorGenus (formF (up f)) Lattices.stdLat ⟨latOf γ, latOf_isLattice γ⟩

theorem isIntegral_latOf {f g : QuadForm ℤ n} {γ : GL (Fin n) ℚ}
    (hfg : ∀ x : Fin n → ℚ, f.evalIn ℚ (γ.val *ᵥ x) = g.evalIn ℚ x) :
    IsIntegral (formF (up f)) (latOf γ) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_glImage.mp hy
  obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hz
  have h1 : (formF (up f)).evalIn ℚ (γ.val *ᵥ intCoe x) = f.evalIn ℚ (γ.val *ᵥ intCoe x) :=
    Siegel.formF_toOQ_eval f _
  rw [h1, hfg, evalIn_intCoe_rat]
  exact ⟨_, rfl⟩

/-- The Gram form of $\gamma\mathbb Z^n$ is $g$ when $f(\gamma x) = g(x)$. -/
theorem down_gramZ_eq {f g : QuadForm ℤ n} {γ : GL (Fin n) ℚ}
    (hfg : ∀ x : Fin n → ℚ, f.evalIn ℚ (γ.val *ᵥ x) = g.evalIn ℚ x) :
    down (gramZ (formF (up f)) γ (isIntegral_latOf hfg)) = g := by
  conv_rhs => rw [← down_up g]
  congr 1
  refine QuadForm.ext_eval fun x => ?_
  apply IsFractionRing.injective (𝓞 ℚ) ℚ
  rw [algebraMap_eval_gramZ, ← evalIn_intCoe_rat]
  have h1 := Siegel.formF_toOQ_eval f (γ.val *ᵥ intCoe x)
  simp only [QuadForm.eval] at h1 ⊢
  rw [h1, hfg]

theorem latOf_one_eq : (⟨latOf (1 : GL (Fin n) ℚ), latOf_isLattice 1⟩ : Lat ℚ n) = Lattices.stdLat :=
  Subtype.ext (glImage_one _)

/-- Every form is in its own proper spinor genus. -/
theorem SameProperSpinorGenusForm.refl (f : QuadForm ℤ n) : SameProperSpinorGenusForm f f := by
  refine ⟨1, by simp, fun x => by simp, ?_⟩
  rw [latOf_one_eq]
  exact SameProperSpinorGenus.refl _ _

/-- The proper spinor genus is contained in the (improper) spinor genus. -/
theorem SameProperSpinorGenusForm.sameSpinorGenusForm {f g : QuadForm ℤ n} (h : SameProperSpinorGenusForm f g) :
    SameSpinorGenusForm f g := by
  obtain ⟨γ, -, hfg, hspn⟩ := h
  exact ⟨γ, hfg, hspn.sameSpinorGenus _⟩

/-- **Forms in the same proper spinor genus are in the same genus** (equivalent over $\mathbb R$ and every
$\mathbb Z_p$; from O'Meara's $\operatorname{spn}^+L \subseteq \operatorname{gen}^+L$, §102A, p. 299). -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (a spinor genus lies in a genus)"]
theorem SameProperSpinorGenusForm.sameGenus {f g : QuadForm ℤ n} (h : SameProperSpinorGenusForm f g) :
    Siegel.SameGenus f g := by
  obtain ⟨γ, -, hfg, hspn⟩ := h
  have hs : Lattices.SameGenus (formF (up f)) intVec (latOf γ) :=
    (hspn.sameProperGenus _).sameGenus _
  have := sameGenus_down_gramZ f γ hs (isIntegral_latOf hfg)
  rwa [down_gramZ_eq hfg] at this

/-! ### The Estes–Pall theorem -/

open QuadFormsKB.Composition

/-- **Estes–Pall** (Conway–Sloane, Ch. 15, §3.5, p. 366, citing Estes–Pall 1973), as a **named statement**, in the
proper reading: for a discriminant $D \ne 0$ that is not a square and primitive forms $f, g$ of discriminant $D$, $g$ is
in the proper spinor genus of $f$ if and only if $[g] = [f]\,\mathfrak S^4$ for a class $\mathfrak S$ of Cassels' group
$\mathcal G$ of proper classes. Proved: `estesPallStatement` (`Section3EstesPallOnlyIf.lean`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (Estes–Pall: same spinor genus iff the quotient is a fourth power; stated)"]
structure EstesPallStatement : Prop where
  iff : ∀ (D : ℤ) [NonzeroDisc D], ¬ IsSquare D → ∀ f g : PrimForm D,
    SameProperSpinorGenusForm f.1 g.1 ↔ ∃ S : FormClass D, FormClass.mk g = FormClass.mk f * S ^ 4

/-- Under Estes–Pall, the quotient of two forms in one proper spinor genus is a square, as it must be (Cassels'
genus theorem): a consistency check between the named statement and `SameProperSpinorGenusForm.sameGenus`. -/
theorem EstesPallStatement.exists_sq (h : EstesPallStatement) {D : ℤ} [NonzeroDisc D] (hD : ¬ IsSquare D)
    {f g : PrimForm D} (hfg : SameProperSpinorGenusForm f.1 g.1) : ∃ S : FormClass D, FormClass.mk g = FormClass.mk f * S ^ 2 := by
  obtain ⟨S, hS⟩ := (h.iff D hD f g).mp hfg
  exact ⟨S ^ 2, by rw [hS, ← pow_mul]⟩

/-- Under Estes–Pall, a fourth-power quotient implies the same genus (via Cassels' Corollary to Thm. 3.1). -/
theorem EstesPallStatement.sameGenus_of_fourth (h : EstesPallStatement) {D : ℤ} [NonzeroDisc D] (hD : ¬ IsSquare D)
    {f g : PrimForm D} (S : FormClass D) (hS : FormClass.mk g = FormClass.mk f * S ^ 4) : Siegel.SameGenus f.1 g.1 :=
  ((h.iff D hD f g).mpr ⟨S, hS⟩).sameGenus

/-! ### Why the proper reading -/

/-- $\bar f(x, y) = f(x, -y)$ for $\bar f = [a, -b, c]$. -/
theorem evalIn_conjForm (f : BinQF) (x : Fin 2 → ℚ) :
    (Binary.conjForm f).evalIn ℚ x = f.evalIn ℚ (!![1, 0; 0, -1] *ᵥ x) := by
  simp [QuadForm.evalIn, Binary.conjForm, BinQF.mk, QuadForm.ofUpper, Fin.sum_univ_two, mulVec, dotProduct,
    BinQF.a, BinQF.b, BinQF.c]

/-- **A form and its improperly equivalent form are in the same improper spinor genus**: $\bar f(x) = f(\gamma x)$ with
$\gamma = \mathrm{diag}(1, -1)$, and $\gamma\mathbb Z^2 = \mathbb Z^2$. -/
theorem sameSpinorGenusForm_conjForm (f : BinQF) : SameSpinorGenusForm f (Binary.conjForm f) := by
  let γ : GL (Fin 2) ℚ := ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by simp [Matrix.one_fin_two], by
    simp [Matrix.one_fin_two]⟩
  refine ⟨γ, fun x => (evalIn_conjForm f x).symm, ?_⟩
  have hL : (⟨latOf γ, latOf_isLattice γ⟩ : Lat ℚ 2) = Lattices.stdLat := by
    apply Subtype.ext
    show glImage γ intVec = intVec
    have hint : ∀ i j, γ.val i j ∈ (algebraMap (𝓞 ℚ) ℚ).range := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨1, by simp [γ]⟩
      · exact ⟨0, by simp [γ]⟩
      · exact ⟨0, by simp [γ]⟩
      · exact ⟨-1, by simp [γ]⟩
    refine Tamagawa.BinaryNormOne.glImage_intVec_eq hint ?_
    intro i j
    have : (γ⁻¹).val = γ.val := rfl
    rw [this]
    exact hint i j
  rw [hL]
  exact SameSpinorGenus.refl _ _

/-- **The improper reading forces $\mathcal G^2 = \mathcal G^4$**: if for all primitive $f, g$ of discriminant $D$,
being in the same improper spinor genus were equivalent to $[g] \in [f]\,\mathcal G^4$, then every square class would
be a fourth power. Since $\mathcal G^2 \ne \mathcal G^4$ for some $D$ (e.g. $D = -56$, $\mathcal G \cong \mathbb Z/4$),
the book's statement must be read with the proper spinor genus (`EstesPallStatement`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (the improper reading of Estes–Pall forces 𝒢² = 𝒢⁴)"]
theorem sq_mem_fourth_powers_of_improper {D : ℤ} [NonzeroDisc D]
    (h : ∀ f g : PrimForm D, SameSpinorGenusForm f.1 g.1 ↔ ∃ S : FormClass D, FormClass.mk g = FormClass.mk f * S ^ 4)
    (C : FormClass D) : ∃ S : FormClass D, C ^ 2 = S ^ 4 := by
  obtain ⟨f, rfl⟩ := FormClass.mk_surjective C
  let g : PrimForm D := ⟨Binary.conjForm f.1, Binary.isPrimitive_conjForm f.2.1,
    (Binary.disc_conjForm f.1).trans f.2.2⟩
  obtain ⟨S, hS⟩ := (h f g).mp (sameSpinorGenusForm_conjForm f.1)
  have hg : FormClass.mk g = (FormClass.mk f)⁻¹ := (FormClass.mk_inv f).symm
  refine ⟨S⁻¹, ?_⟩
  rw [hg] at hS
  have : (FormClass.mk f) ^ 2 * S ^ 4 = 1 := by
    calc (FormClass.mk f) ^ 2 * S ^ 4 = FormClass.mk f * (FormClass.mk f * S ^ 4) := by rw [pow_two, mul_assoc]
      _ = 1 := by rw [← hS, mul_inv_cancel]
  rw [inv_pow, eq_inv_iff_mul_eq_one, this]

end QuadFormsKB.ConwaySloane.EstesPall
