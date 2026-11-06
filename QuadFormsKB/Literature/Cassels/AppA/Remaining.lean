/-
# Cassels, Appendix A: three remaining small items

Cassels, *Rational Quadratic Forms* (1978), Appendix A, pp. 362-365. **Layer:** as in `Sec2.lean`, `Sec3.lean` and
`Watson.lean`: a form $Q$ on $\mathbb Q^n$ is `QuadForm ℚ n`, a lattice is an `𝓞 ℚ`-submodule of `Fin n → ℚ`, and
$\mathbb Z^n$ is `LatZ n`; integral forms are `QuadForm ℤ n`, viewed over $\mathbb Q$ by `QQ`. Variables are
$x_0, \dots, x_{n-1}$ (Cassels' $x_1, \dots, x_n$ are shifted by one).

**Proved.**
* `eisensteinForm_indecomposable` (§2, p. 362): the lattice $\mathbb Z^2$ with the form $x_0^2 + x_0 x_1 + x_1^2$ is
  indecomposable (the example whose formula is lost in the machine-read text of `Sec2.lean`);
* `exists_scale_integerValued` (§2, proof of Theorem 2.1, p. 363): on a finitely generated lattice a rational form becomes
  integer-valued after multiplication by a positive integer;
* `isIntEquiv_watsonDerived_smul` (§3, footnote on p. 365): if $p \nmid \det H$, every Watson-derived form of $Q$ at $p$
  is integrally equivalent to $pQ$; `encard_genusClasses_smul` (scaling by a prime preserves the number of classes of a
  genus, reusing the scaling lemmas of `Binary/SiegelNonPrimitive.lean`) and `encard_genusClasses_watsonDerived` give the
  consequence for class numbers.

*Update (footnote ${\ddagger}$, p. 365).* Cassels' footnote says that the genus $\mathcal G_1$ of $(\Lambda_1, \phi_1)$,
$\phi_1 = p^{-1}\phi$, equals the genus $\mathcal G$ of $(\Lambda, \phi)$ unless $p = 2$ or $p$ divides the determinant.
Literally this holds only up to the rescaling $\phi \mapsto p\phi$: for $p \nmid 2\det$ one has $\Lambda_1 = p\Lambda$
(`mem_watsonSub_iff_of_not_dvd`), and $x \mapsto px$ is an isometry $(\Lambda, p\phi) \to (p\Lambda, p^{-1}\phi)$, so
$\mathcal G_1$ is the genus of $p\phi$, which is a different genus from that of $\phi$ (it is not even a genus of forms
that represent the same integers). The class numbers of $\mathcal G_1$ and $\mathcal G$ do agree
(`encard_genusClasses_watsonDerived`), which is all that the proof of Theorem 3.1 uses.
-/
import QuadFormsKB.Literature.Cassels.AppA.Watson
import QuadFormsKB.Siegel.NeighborGenus
import QuadFormsKB.Binary.SiegelNonPrimitive

open NumberField Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### §2, p. 362: the binary lattice $x_0^2 + x_0 x_1 + x_1^2$ -/

/-- Helper: the integral form $x_0^2 + x_0 x_1 + x_1^2$ in two variables (the form of the example on p. 362,
with Cassels' $x_1, x_2$ shifted to $x_0, x_1$). -/
def eisensteinQF : QuadForm ℤ 2 := QuadForm.ofUpper ![![1, 1], ![0, 1]]

/-- Helper: the value of `eisensteinQF` is $x_0^2 + x_0 x_1 + x_1^2$. -/
theorem eisensteinQF_eval (x : Fin 2 → ℤ) :
    eisensteinQF.eval x = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 := by
  simp [eisensteinQF, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]
  ring

/-- Helper: the form `eisensteinQF` is positive definite. -/
theorem eisensteinQF_posDef : IntQF.PosDef eisensteinQF := by
  intro x hx
  rw [eisensteinQF_eval]
  have : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    apply hx
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  rcases this with h | h
  · have := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 1)]
  · have := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0)]

/-- **Cassels, Appendix A, §2, p. 362 (example).** The binary lattice $\mathbb Z^2$ (basis $b_0, b_1$, the standard
unit vectors) with the form $Q(x_0 b_0 + x_1 b_1) = x_0^2 + x_0 x_1 + x_1^2$, viewed over $\mathbb Q$
(`DefiniteForms.QQ eisensteinQF`, with `DefiniteForms.LatZ 2` the lattice), is indecomposable: it is non-zero and is not
an orthogonal sum of two non-zero sublattices. *Proof:* both unit vectors take the value $1$ and have non-zero polar
form $B(b_0, b_1) = 1$, so `DefiniteForms.indecomposable_of_graph` applies. -/
@[kb "cassels1978" "App. A, §2, p. 362 (example: x₁² + x₁x₂ + x₂² is indecomposable)"]
theorem eisensteinForm_indecomposable :
    IsIndecomposable (DefiniteForms.QQ eisensteinQF) (DefiniteForms.LatZ 2) := by
  refine DefiniteForms.indecomposable_of_graph (by norm_num) eisensteinQF_posDef ?_ ?_
  · intro i
    rw [eisensteinQF_eval]
    fin_cases i <;> simp
  · have h01 : eisensteinQF.hessian 0 1 ≠ 0 := by
      simp [QuadForm.hessian, eisensteinQF, QuadForm.ofUpper]
    have r1 : Relation.ReflTransGen (fun a b : Fin 2 => eisensteinQF.hessian a b ≠ 0) 0 1 :=
      Relation.ReflTransGen.single h01
    intro j
    fin_cases j
    · exact Relation.ReflTransGen.refl
    · exact r1

/-! ### §2, proof of Theorem 2.1, p. 363: scaling to an integer-valued form -/

/-- **Cassels, Appendix A, §2, proof of Theorem 2.1, p. 363.** For a finitely generated lattice $L \subseteq \mathbb Q^n$
(`hL`) and a rational form $Q$ in $n$ variables there is a positive integer $c$ with $c\,Q(x) \in \mathbb Z$ for all
$x \in L$; that is, $cQ$ is integer-valued on $L$. *Proof:* by the O'Meara scaling lemma (`omeara105_scale`) some
non-zero integer $k$ makes $k\,B(x, y)$ integral on $L$; take $c = 2|k|$, since $B(x, x) = 2Q(x)$. -/
@[kb "cassels1978" "App. A, §2, proof of Thm. 2.1, p. 363 (scaling φ to be integer-valued on Λ)"]
theorem exists_scale_integerValued {n : ℕ} (Q : QuadForm ℚ n) {L : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hL : L.FG) : ∃ c : ℕ, 0 < c ∧ ∀ x ∈ L, ∃ z : ℤ, (c : ℚ) * Q.eval x = z := by
  obtain ⟨k, hk, h⟩ := omeara105_scale (Q := Q) hL
  refine ⟨2 * k.natAbs, by omega, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := h x hx x hx
  obtain ⟨m, hm⟩ := exists_intCast_ringOfIntegers_rat a
  have hb : bil Q x x = 2 * Q.eval x := bil_self Q x
  have hka : (k : ℚ) * bil Q x x = m := by
    rw [← ha, ← hm]; simp
  obtain ⟨t, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · refine ⟨m, ?_⟩
    rw [← hka, hb]
    simp only [Int.natAbs_natCast, Int.cast_natCast]
    push_cast; ring
  · refine ⟨-m, ?_⟩
    have h2 : -((t : ℚ) * bil Q x x) = m := by push_cast at hka; linarith
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    push_cast
    rw [← h2, hb]; ring

end QuadFormsKB.Lattices

namespace QuadFormsKB.DefiniteForms

open Siegel

variable {n : ℕ}

/-! ### §3, footnote on p. 365: the derived form at a prime not dividing the determinant -/

/-- Helper: if every column of the integer matrix `g` is `p` times an integer vector and the columns of `g` span
`p` times the standard lattice, then `g = p • H` with `H` unimodular. Arguments: `p` a prime, `g` the matrix,
`hrange` the statement that the range of `g` is the set of vectors `p • c'`. -/
theorem exists_unimodular_of_range_smul {p : ℤ} (hp : p ≠ 0) (g : Matrix (Fin n) (Fin n) ℤ)
    (hcol : ∀ i, ∃ c' : Fin n → ℤ, g *ᵥ Pi.single i 1 = p • c')
    (hsurj : ∀ y : Fin n → ℤ, ∃ x, g *ᵥ x = p • y) :
    ∃ U : GL (Fin n) ℤ, g = p • U.val := by
  classical
  choose c hc using hcol
  set H : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun j i => c i j with hH
  have hgH : g = p • H := by
    ext j i
    have := congrFun (hc i) j
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hH] using this
  have hHsurj : ∀ y : Fin n → ℤ, ∃ x, H *ᵥ x = y := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨x, ?_⟩
    rw [hgH, Matrix.smul_mulVec] at hx
    exact smul_right_injective _ hp hx
  choose x hx using fun i : Fin n => hHsurj (Pi.single i 1)
  set H' : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun j i => x i j with hH'
  have h1 : H * H' = 1 := by
    ext i k
    have := congrFun (hx k) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hH', Matrix.one_apply, Pi.single_apply, eq_comm]
      using this
  have h2 : H' * H = 1 := mul_eq_one_comm.mp h1
  exact ⟨⟨H, H', h1, h2⟩, hgH⟩

/-- **Cassels, Appendix A, §3, footnote ${\ddagger}$ on p. 365 (up to scaling).** If $p$ is a prime that does not divide
the determinant $\det H_Q$ of the Hessian of $Q$, then every Watson-derived form $Q'$ of $Q$ at $p$ (`IsWatsonDerived`:
the form $p^{-1}Q$ on $\Lambda_p$ in a basis) is integrally equivalent to $pQ$ (the form `(p : ℤ) • Q`), via the basis
change $x \mapsto px$ followed by a change of basis of $\Lambda_p = p\Lambda$. *Proof:* $\Lambda_p = p\mathbb Z^n$
(`mem_watsonSub_iff_of_not_dvd`), so the basis matrix is $pU$ with $U \in \mathrm{GL}_n(\mathbb Z)$ and
$pQ'(x) = Q(pUx) = p^2 Q(Ux)$.

*Update:* the footnote's "$\mathcal G_1 = \mathcal G$" holds up to the rescaling $\phi \mapsto p\phi$: $\mathcal G_1$ is
the genus of $p\phi$, not of $\phi$. The hypothesis $p \nmid \det H_Q$ is implied by "$p \nmid 2\det H_Q$"
and is all that is needed. -/
@[kb "cassels1978" "App. A, §3, footnote ‡ on p. 365 (𝒢₁ = 𝒢 unless p = 2 or p ∣ d, up to scaling)"]
theorem isIntEquiv_watsonDerived_smul {Q Q' : QuadForm ℤ n} {p : ℕ} (h : IsWatsonDerived Q p Q')
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) : IntEquiv ((p : ℤ) • Q) Q' := by
  obtain ⟨hp, g, hg, hrange, hQg⟩ := h
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p : ℤ) ≠ 0 := hpp.ne_zero
  have hmem : ∀ c : Fin n → ℤ, c ∈ watsonSub Q (p : ℤ) ↔ ∃ c', c = (p : ℤ) • c' :=
    mem_watsonSub_iff_of_not_dvd hpp hdet
  have hcol : ∀ i, ∃ c' : Fin n → ℤ, g *ᵥ Pi.single i 1 = (p : ℤ) • c' := by
    intro i
    refine (hmem _).mp ?_
    rw [← SetLike.mem_coe, ← hrange]
    exact ⟨Pi.single i 1, rfl⟩
  have hsurj : ∀ y : Fin n → ℤ, ∃ x, g *ᵥ x = (p : ℤ) • y := by
    intro y
    have : (p : ℤ) • y ∈ (Set.range g.mulVec) := by
      rw [hrange]; exact (hmem _).mpr ⟨y, rfl⟩
    exact this
  obtain ⟨U, hU⟩ := exists_unimodular_of_range_smul hp0 g hcol hsurj
  refine ⟨U, fun x => ?_⟩
  have h1 := hQg x
  rw [hU, Matrix.smul_mulVec, Siegel.Kneser.eval_smul_gen] at h1
  rw [Siegel.Kneser.eval_smul_form]
  have h3 : (p : ℤ) * ((p : ℤ) * Q.eval (U.val *ᵥ x)) = (p : ℤ) * Q'.eval x := by
    rw [← h1]; ring
  exact mul_left_cancel₀ hp0 h3

/-! ### Scaling by a prime: classes of a genus

Scaling by a non-zero integer $c$ preserves equivalence and genus in both directions
(`Binary.intEquiv_smul_iff`, `Binary.sameGenus_smul_iff`), maps classes injectively (`Binary.scaleClass`), and every
form in the genus of $cQ$ has all its values divisible by $c$ (`Binary.dvd_eval_of_sameGenus`); these are reused from
`Binary/SiegelNonPrimitive.lean`. What is added here is that such a form is $c$ times an integral form. -/

/-- Helper: the value of an integral form at a unit vector is the diagonal coefficient. -/
theorem eval_single_one (R : QuadForm ℤ n) (i : Fin n) : R.eval (Pi.single i 1) = R.coeff i i := by
  have := R.evalIn_eq_dotProduct ℤ (Pi.single i 1)
  simpa [QuadForm.eval] using this

/-- Helper: if an integral form takes only values divisible by $p$ on $\mathbb Z^n$, then all its coefficients are
divisible by $p$. Arguments: `R` the form, `hdvd` the divisibility of all values. -/
theorem dvd_coeff_of_dvd_eval {R : QuadForm ℤ n} {p : ℤ} (hdvd : ∀ v : Fin n → ℤ, p ∣ R.eval v)
    (i j : Fin n) : p ∣ R.coeff i j := by
  rcases lt_trichotomy i j with h | h | h
  · have hpol := R.polar_eq_hessian ℤ (Pi.single i 1) (Pi.single j 1)
    have hH : (R.coeff i j : ℤ) = R.eval (Pi.single i 1 + Pi.single j 1) - R.eval (Pi.single i 1)
        - R.eval (Pi.single j 1) := by
      have h2 : R.eval (Pi.single i 1 + Pi.single j 1) - R.eval (Pi.single i 1) - R.eval (Pi.single j 1)
          = R.coeff i j + R.coeff j i := by
        simpa [QuadForm.hessian, Matrix.mulVec_single_one, dotProduct_single] using hpol
      rw [h2, R.upper h]
      ring
    rw [hH]
    exact dvd_sub (dvd_sub (hdvd _) (hdvd _)) (hdvd _)
  · subst h
    rw [← eval_single_one]
    exact hdvd _
  · rw [R.upper h]
    exact dvd_zero _

/-- Helper: a form in the genus of $pQ$ ($p$ prime) is $p$ times an integral form (all its values on $\mathbb Z^n$
are divisible by $p$, because they are so over $\mathbb Z_p$). Arguments: `hp` the primality of `p`, `h` the genus
relation between `(p : ℤ) • Q` and `R`. -/
theorem exists_eq_smul_of_sameGenus {Q R : QuadForm ℤ n} {p : ℕ} (hp : p.Prime)
    (h : SameGenus ((p : ℤ) • Q) R) : ∃ R' : QuadForm ℤ n, R = (p : ℤ) • R' := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hc : ∀ i j, (p : ℤ) ∣ R.coeff i j :=
    dvd_coeff_of_dvd_eval (Binary.dvd_eval_of_sameGenus hp0 h)
  choose c hc' using hc
  refine ⟨⟨Matrix.of c, fun i j hij => ?_⟩, ?_⟩
  · have h0 := R.upper hij
    have := hc' i j
    rw [h0] at this
    simp only [Matrix.of_apply]
    exact (mul_eq_zero.mp this.symm).resolve_left hp0
  · ext i j
    simp [hc' i j]

/-- **Scaling by a prime preserves the number of classes in a genus.** For a prime $p$, the genus of $pQ$ has exactly
as many classes as the genus of $Q$: the map $[R] \mapsto [pR]$ is injective on classes (`Binary.scaleClass_injective`) and maps
the classes of the genus of $Q$ onto those of the genus of $pQ$ (`Binary.sameGenus_smul_iff`,
`exists_eq_smul_of_sameGenus`). Arguments: `hp` the primality of `p`, `Q` the form. -/
theorem encard_genusClasses_smul {p : ℕ} (hp : p.Prime) (Q : QuadForm ℤ n) :
    (genusClasses ((p : ℤ) • Q)).encard = (genusClasses Q).encard := by
  have hc : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hinj := Binary.scaleClass_injective (n := n) hc
  have himg : genusClasses ((p : ℤ) • Q) = Binary.scaleClass (p : ℤ) hc '' genusClasses Q := by
    ext c
    induction c using Quotient.inductionOn with
    | h R =>
      change classOf R ∈ _ ↔ _
      rw [classOf_mem_genusClasses_iff]
      constructor
      · intro hR
        obtain ⟨R', rfl⟩ := exists_eq_smul_of_sameGenus hp hR
        exact ⟨classOf R', classOf_mem_genusClasses_iff.mpr ((Binary.sameGenus_smul_iff hc Q R').mp hR), rfl⟩
      · rintro ⟨c', hc', hcR⟩
        induction c' using Quotient.inductionOn with
        | h R' =>
          have h1 : classOf R = classOf ((p : ℤ) • R') := hcR.symm
          have h2 : SameGenus Q R' := classOf_mem_genusClasses_iff.mp hc'
          exact ((Binary.sameGenus_smul_iff hc Q R').mpr h2).trans (classOf_eq_classOf_iff.mp h1.symm).sameGenus
  rw [himg, hinj.encard_image]

/-- **Cassels, Appendix A, §3, footnote ${\ddagger}$ on p. 365, in terms of class numbers.** If $p$ is a prime not
dividing $\det H_Q$ and $Q'$ is a Watson-derived form of $Q$ at $p$, then the genus of $Q'$ has exactly as many classes
as the genus of $Q$. (The genera themselves differ by the scaling $\phi \mapsto p\phi$,
`isIntEquiv_watsonDerived_smul`.)

*Update:* the footnote's "$\mathcal G_1 = \mathcal G$" holds up to the rescaling $\phi \mapsto p\phi$; the class
numbers of $\mathcal G_1$ and $\mathcal G$ agree. Arguments: `h` the derived-form relation, `hdet` the non-divisibility
of the determinant of the Hessian by `p`. -/
@[kb "cassels1978" "App. A, §3, footnote ‡ on p. 365 (𝒢₁ and 𝒢 have the same number of classes unless p = 2 or p ∣ d)"]
theorem encard_genusClasses_watsonDerived {Q Q' : QuadForm ℤ n} {p : ℕ} (h : IsWatsonDerived Q p Q')
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) : (genusClasses Q').encard = (genusClasses Q).encard := by
  rw [← genusClasses_eq_of_sameGenus (isIntEquiv_watsonDerived_smul h hdet).sameGenus]
  exact encard_genusClasses_smul h.1 Q

end QuadFormsKB.DefiniteForms
