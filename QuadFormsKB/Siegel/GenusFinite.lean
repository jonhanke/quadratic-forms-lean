/-
# Finiteness of the class number of a positive definite genus

**Proves** the former cited input `GenusFinite Q` (`Siegel/Mass.lean`) for every positive definite integral form $Q$
(`genusFinite`): the genus of $Q$ contains only finitely many $\mathrm{GL}_n(\mathbb{Z})$-classes.

*Proof.* $\det H$ is a genus invariant (`SameGenus.det_hessian_eq`) and positive definiteness is a genus invariant
(`SameGenus.posDef`). By Hermite's reduction (`Hermite.exists_reduced`, `Siegel/HermiteReduction.lean`), applied to the
Hessian $H'$ of a form $Q'$ in the genus, $Q'$ is $\mathbb{Z}$-equivalent to a form whose Hessian has all entries bounded by
$E_n(\det H)$ (`exists_intEquiv_hessian_bounded`). A form is determined by its Hessian (`hessian_injective`), so these forms
make up a finite set (`finite_setOf_hessian_bounded`), and the classes in the genus are among their classes.

*Related work (consulted, not imported):* lean-categories (D. Zack Garza) `genus_finite`
(`LeanCategories/Lattices/Valued/ReducedBasis.lean`), for abstract lattices; Tau Ceti `IntegralLattice/PosDef`.
-/
import QuadFormsKB.Siegel.HermiteReduction
import QuadFormsKB.Siegel.ThetaCuspidal

open Matrix

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-- **The Hessian of a positive definite form is a positive definite integral symmetric matrix**
($H = C + C^{\mathsf T}$ is symmetric and $x^{\mathsf T}Hx = 2Q(x) > 0$ for $x \ne 0$). -/
theorem hessian_isPosDefInt {Q : IntQF n} (hQ : Q.PosDef) : Hermite.IsPosDefInt Q.hessian := by
  refine ⟨?_, fun x hx => ?_⟩
  · unfold IsSymm
    rw [QuadForm.hessian, transpose_add, transpose_transpose, add_comm]
  · rw [← LocalDensity.two_mul_eval_eq_hessian]
    have := hQ x hx
    omega

/-- **A form is determined by its Hessian:** $C$ is upper triangular, $C_{ij} = H_{ij}$ for $i < j$ and $2C_{ii} = H_{ii}$. -/
theorem hessian_injective : Function.Injective (fun Q : QuadForm ℤ n => Q.hessian) := by
  intro Q1 Q2 h
  have h' : Q1.hessian = Q2.hessian := h
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := congrFun (congrFun h' i) j
    simp only [QuadForm.hessian, Matrix.add_apply, transpose_apply] at this
    rw [Q1.upper hij, Q2.upper hij] at this
    simpa using this
  · have := congrFun (congrFun h' i) i
    simp only [QuadForm.hessian, Matrix.add_apply, transpose_apply] at this
    omega
  · rw [Q1.upper hij, Q2.upper hij]

/-- **Every symmetric integral matrix with even diagonal is a Hessian:** $N = H$ for the form with $C_{ii} = N_{ii}/2$ and
$C_{ij} = N_{ij}$ ($i < j$). -/
theorem exists_hessian_eq (N : Matrix (Fin n) (Fin n) ℤ) (hN : N.IsSymm) (hev : ∀ i, Even (N i i)) :
    ∃ Q : QuadForm ℤ n, Q.hessian = N := by
  refine ⟨QuadForm.ofUpper (fun i j => if i = j then N i i / 2 else N i j), ?_⟩
  ext i j
  simp only [QuadForm.hessian, QuadForm.ofUpper, Matrix.add_apply, transpose_apply, of_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hij.le, not_le.mpr hij, hij.ne]
  · obtain ⟨k, hk⟩ := hev i
    simp only [le_refl, ↓reduceIte]
    omega
  · simp [hij.le, not_le.mpr hij, hij.ne, hN.apply i j]

/-- **Reduction of a positive definite form:** $Q$ is $\mathbb{Z}$-equivalent to a form $Q'$ whose Hessian has all entries
bounded by $E_n(\det H)$ (`Hermite.entryBound`), $H$ the Hessian of $Q$. -/
@[kb "cassels1978" "Ch. 9, Thm. 1.1, proof by reduction (Hermite) [unverified]"]
theorem exists_intEquiv_hessian_bounded {Q : IntQF n} (hQ : Q.PosDef) :
    ∃ Q' : QuadForm ℤ n, IntEquiv Q Q' ∧
      ∀ i j, |Q'.hessian i j| ≤ Hermite.entryBound n Q.hessian.det := by
  obtain ⟨g, -, hb⟩ := Hermite.exists_reduced n _ (hessian_isPosDefInt hQ)
  have hsym := ((hessian_isPosDefInt hQ).conj g).1
  have hev : ∀ i, Even ((g.valᵀ * Q.hessian * g.val) i i) := fun i => by
    rw [Hermite.conj_apply, ← LocalDensity.two_mul_eval_eq_hessian]
    exact even_two_mul _
  obtain ⟨Q', hQ'⟩ := exists_hessian_eq _ hsym hev
  exact ⟨Q', ⟨g, (eval_mulVec_eq_iff_hessian Q Q' g.val).mpr hQ'.symm⟩, fun i j => hQ' ▸ hb i j⟩

/-- **Finitely many forms with bounded Hessian entries:** $\{Q' : |H'_{ij}| \le B\ \forall i, j\}$ is finite. -/
theorem finite_setOf_hessian_bounded (B : ℤ) :
    {Q' : QuadForm ℤ n | ∀ i j, |Q'.hessian i j| ≤ B}.Finite := by
  have hM : {M : Fin n → Fin n → ℤ | ∀ i, M i ∈ {r : Fin n → ℤ | ∀ j, r j ∈ Set.Icc (-B) B}}.Finite :=
    Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => Set.finite_Icc _ _
  refine (hM.preimage hessian_injective.injOn).subset fun Q' hQ' => ?_
  intro i j
  exact abs_le.mp (hQ' i j)

/-- **Finiteness of the class number** (Hermite; Cassels 1978, Ch. 9, Thm. 1.1 [unverified]): for every positive definite
integral form $Q$, the genus of $Q$ contains only finitely many $\mathrm{GL}_n(\mathbb{Z})$-classes, i.e. `GenusFinite Q`.
This discharges the input `GenusFinite` wherever it is assumed (e.g. `thm_6_3_quaternary'`). -/
@[kb "cassels1978" "Ch. 9, Thm. 1.1, finiteness of the class number [unverified]"]
theorem genusFinite {Q : IntQF n} (hQ : Q.PosDef) : GenusFinite Q := by
  refine ⟨((finite_setOf_hessian_bounded (Hermite.entryBound n Q.hessian.det)).image classOf).subset ?_⟩
  rintro c ⟨Q'', rfl, hg⟩
  obtain ⟨Q3, he, hb⟩ := exists_intEquiv_hessian_bounded (hg.posDef hQ)
  refine ⟨Q3, fun i j => ?_, (classOf_eq_classOf_iff.mpr he).symm⟩
  rw [SameGenus.det_hessian_eq hQ hg]
  exact hb i j

end QuadFormsKB.Siegel
