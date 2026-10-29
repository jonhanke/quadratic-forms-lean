/-
# Finitely many proper classes in the genus, every signature

**Layer:** number fields; the library's adelic groups (`Lattices/ClassSet.lean`, `Tamagawa/Measure/AdelicSO.lean`) and the
double cosets `DC Q₀` of `ClassicalSetup.lean`.

Let $F$ be a number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $n$ variables (any signature),
$V = F^n$ with $Q = Q_0\otimes F$, $L = \mathcal O_F^n$.

**Proves** (all unconditional, standard axioms only)
* `finite_orbits_of_nondegenerate`: for every nondegenerate $Q$ over $F$ and every lattice $L$,
  $O(V)(F)\backslash O(V)(\mathbb A_f)/O(\hat L)$ is finite (the orbits inject into the classes in the genus of $L$,
  `orbitToClass_injective`, which are finite by O'Meara 103:4, `ClassFin.genusClasses_finite_nf`); this removes the
  hypotheses `IsTotallyPosDef` and integrality of `finite_orbits`;
* `finite_orbits_SO_of_nondegenerate`: $SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ is finite (as in the definite
  `finite_orbits_SO`: $SO(V)(\mathbb A_f)/SO(\hat L)\to O(V)(\mathbb A_f)/O(\hat L)$ is injective and $SO(V)(F)$ has index
  at most $2$ in $O(V)(F)$, so each $O(V)(F)$-orbit is the union of at most two $SO(V)(F)$-orbits);
* **`finite_DC`**: the proper classes in the genus, `DC Q₀` $= SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$, form a
  finite set.
-/
import QuadFormsKB.Tamagawa.Indefinite.ClassicalSetup
import QuadFormsKB.Lattices.ClassFinite

open MulAction NumberField IsDedekindDomain

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

/-! ### The orthogonal group: every nondegenerate form -/

section Orth

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- **Finitely many double cosets for every nondegenerate $Q$** (any signature, any lattice $L$):
$O(V)(F)\backslash O(V)(\mathbb A_f)/O(\hat L)$ is finite. The orbits inject into the classes in the genus of $L$
(`orbitToClass_injective`, `orbitToClass_image`), and there are finitely many of those (O'Meara 103:4,
`ClassFin.genusClasses_finite_nf`). -/
theorem finite_orbits_of_nondegenerate {Q : QuadForm F n} (hQ : Q.Nondegenerate) (L : Lat F n) :
    Finite (orbitRel.Quotient (ratPoints Q) (OAf Q ⧸ locStab Q L)) := by
  have h := ((ClassFin.genusClasses_finite_nf Q hQ L).subset (orbitToClass_image Q L)).of_finite_image
    (orbitToClass_injective Q L).injOn
  exact Set.finite_univ_iff.mp h

end Orth

/-! ### The special orthogonal group -/

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- $SO(V)(F)$ has finite index in $O(V)(F)$ (index $2$ for $n > 0$, `index_soAf_ratPoints`; for $n = 0$ the groups
agree, since every $0\times 0$ determinant is $1$). -/
theorem finiteIndex_soAf_ratPoints (hQ : Q₀.Nondegenerate) :
    ((soAf QF).subgroupOf (ratPoints QF)).FiniteIndex := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · haveI : IsEmpty (Fin n) := by rw [h0]; infer_instance
    have htop : (soAf QF).subgroupOf (ratPoints QF) = ⊤ := by
      ext x
      simp only [Subgroup.mem_top, iff_true, Subgroup.mem_subgroupOf]
      intro v
      exact Matrix.det_isEmpty
    rw [htop]
    infer_instance
  · exact ⟨by rw [index_soAf_ratPoints Q₀ hQ hn]; norm_num⟩

/-- **Finitely many $SO$-classes for every nondegenerate $Q_0$** (any signature):
$\Gamma_f\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ is finite, $\Gamma_f = SO(V)(F)$ = `GammaSOf Q₀`. The map
$SO(V)(\mathbb A_f)/SO(\hat L) \to O(V)(\mathbb A_f)/O(\hat L)$ is injective and equivariant for $SO(V)(F)$, which has
finite index in $O(V)(F)$ (`finiteIndex_soAf_ratPoints`); the $O(V)(F)$-orbits are finite
(`finite_orbits_of_nondegenerate`), hence so are the orbits of the subgroup (`finite_orbits_of_finiteIndex`). -/
theorem finite_orbits_SO_of_nondegenerate (hQ : Q₀.Nondegenerate) :
    Finite (orbitRel.Quotient (GammaSOf Q₀) (SOAf Q₀ ⧸ KSO Q₀)) := by
  have := finite_orbits_of_nondegenerate (nondegenerate_map Q₀ hQ) (stdLat F n)
  set H' : Subgroup (ratPoints QF) := (soAf QF).subgroupOf (ratPoints QF)
  have : H'.FiniteIndex := finiteIndex_soAf_ratPoints Q₀ hQ
  have hfin := finite_orbits_of_finiteIndex (X := OAf QF ⧸ locStab QF (stdLat F n)) H'
  let ι : SOAf Q₀ ⧸ KSO Q₀ → OAf QF ⧸ locStab QF (stdLat F n) :=
    Quotient.map' (fun a : SOAf Q₀ => (a : OAf QF)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact hab)
  have hι : ∀ a : SOAf Q₀, ι (QuotientGroup.mk a) = QuotientGroup.mk (a : OAf QF) := fun _ => rfl
  have hιinj : Function.Injective ι := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [hι, hι, QuotientGroup.eq] at hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hab
  let e : GammaSOf Q₀ → H' := fun γ => ⟨⟨((γ : SOAf Q₀) : OAf QF), γ.2⟩, (γ : SOAf Q₀).2⟩
  have hcomm : ∀ (γ : GammaSOf Q₀) (y : SOAf Q₀ ⧸ KSO Q₀), ι (γ • y) = e γ • ι y := by
    intro γ y
    induction y using QuotientGroup.induction_on with | H a => rfl
  let Φ : orbitRel.Quotient (GammaSOf Q₀) (SOAf Q₀ ⧸ KSO Q₀) →
      orbitRel.Quotient H' (OAf QF ⧸ locStab QF (stdLat F n)) :=
    Quotient.map' ι (fun a b hab => by
      have hab' : a ∈ orbit (GammaSOf Q₀) b := hab
      obtain ⟨γ, rfl⟩ := hab'
      show ι (γ • b) ∈ orbit H' (ι b)
      exact ⟨e γ, (hcomm γ b).symm⟩)
  refine Finite.of_injective Φ ?_
  intro p q hpq
  induction p using Quotient.inductionOn' with | h a => ?_
  induction q using Quotient.inductionOn' with | h b => ?_
  have h1 : ι a ∈ orbit H' (ι b) := Quotient.exact' hpq
  obtain ⟨h, hh⟩ := h1
  apply Quotient.sound'
  show a ∈ orbit (GammaSOf Q₀) b
  let γ : GammaSOf Q₀ := ⟨⟨((h : ratPoints QF) : OAf QF), h.2⟩, (h : ratPoints QF).2⟩
  exact ⟨γ, hιinj (by rw [hcomm]; exact hh)⟩

/-- The finite part of a diagonal element of $SO(V)(\mathbb A)$ lies in $\Gamma_f = SO(V)(F)$. -/
theorem snd_mem_GammaSOf {γ : SOAdele Q₀} (hγ : γ ∈ GammaSOAdele Q₀) : γ.2 ∈ GammaSOf Q₀ := by
  obtain ⟨g, rfl⟩ := hγ
  exact ⟨(g : orthGroup QF F), rfl⟩

/-- Every element of $\Gamma_f = SO(V)(F)$ is the finite part of a diagonal element of $SO(V)(\mathbb A)$ (a rational
isometry in $SO(V)(\mathbb A_f)$ has determinant $1$). -/
theorem exists_GammaSOAdele_snd {x : SOAf Q₀} (hx : x ∈ GammaSOf Q₀) :
    ∃ γ ∈ GammaSOAdele Q₀, γ.2 = x := by
  obtain ⟨γ, hγ⟩ := hx
  obtain ⟨v₀⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)))
  have hγ' : diagF QF γ = (x : OAf QF) := hγ
  have hdet : (γ : GL (Fin n) F).val.det = 1 := by
    have : (((x : OAf QF) v₀ : orthGroup QF _) : GL (Fin n) (v₀.adicCompletion F)).val.det = 1 := x.2 v₀
    rw [← hγ', det_diagF] at this
    exact (algebraMap F (v₀.adicCompletion F)).injective (by rw [this, map_one])
  exact ⟨_, ⟨⟨γ, hdet⟩, rfl⟩, Subtype.ext hγ'⟩

/-- **The proper classes in the genus are finite in number** (O'Meara 103:4: "in particular, the number of proper
classes in a genus is finite"), for every nondegenerate quadratic form $Q_0$ over $\mathcal O_F$, every number field
$F$ and every signature: the double coset space
$$SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L),\qquad V = F^n,\ Q = Q_0\otimes F,\ L = \mathcal O_F^n,$$
(`DC Q₀`) is finite. It injects into the $SO(V)(F)$-orbits on $SO(V)(\mathbb A_f)/SO(\hat L)$, which are finite
(`finite_orbits_SO_of_nondegenerate`). -/
@[kb "omeara1963" "§103, 103:4, p. 309 ('in particular, the number of proper classes in a genus is finite')"]
theorem finite_DC (hQ : Q₀.Nondegenerate) : Finite (DC Q₀) := by
  have := finite_orbits_SO_of_nondegenerate Q₀ hQ
  let Ψ : DC Q₀ → orbitRel.Quotient (GammaSOf Q₀) (SOAf Q₀ ⧸ KSO Q₀) :=
    Quotient.lift (fun b : SOAf Q₀ => (Quotient.mk'' (QuotientGroup.mk b : SOAf Q₀ ⧸ KSO Q₀) :
        orbitRel.Quotient (GammaSOf Q₀) (SOAf Q₀ ⧸ KSO Q₀))) (fun b b' h => by
      obtain ⟨γ, hγ, k, hk, rfl⟩ := h
      apply Quotient.sound'
      show (QuotientGroup.mk b : SOAf Q₀ ⧸ KSO Q₀) ∈ orbit (GammaSOf Q₀) (QuotientGroup.mk (γ.2 * b * k))
      refine ⟨⟨γ.2⁻¹, (GammaSOf Q₀).inv_mem (snd_mem_GammaSOf Q₀ hγ)⟩, ?_⟩
      beta_reduce
      rw [Subgroup.smul_def, MulAction.Quotient.smul_coe, smul_eq_mul]
      rw [show (γ.2⁻¹ * (γ.2 * b * k) : SOAf Q₀) = b * k by group, QuotientGroup.mk_mul_of_mem _ hk])
  refine Finite.of_injective Ψ ?_
  intro p q hpq
  induction p using Quotient.inductionOn with | h b => ?_
  induction q using Quotient.inductionOn with | h b' => ?_
  have h1 : (QuotientGroup.mk b : SOAf Q₀ ⧸ KSO Q₀) ∈ orbit (GammaSOf Q₀) (QuotientGroup.mk b') :=
    Quotient.exact' hpq
  obtain ⟨x, hx⟩ := h1
  obtain ⟨γ, hγ, hγx⟩ := exists_GammaSOAdele_snd Q₀ x.2
  beta_reduce at hx
  rw [Subgroup.smul_def, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq] at hx
  apply Quotient.sound
  refine ⟨γ⁻¹, (GammaSOAdele Q₀).inv_mem hγ, ((x * b')⁻¹ * b)⁻¹, (KSO Q₀).inv_mem hx, ?_⟩
  rw [Prod.snd_inv, hγx]
  group

end QuadFormsKB.Tamagawa.Indefinite
