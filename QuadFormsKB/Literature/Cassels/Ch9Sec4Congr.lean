/-
# Cassels, Chapter 9, Lemma 4.3: congruent forms are in one genus

**Layer:** classically integral forms `f g : QuadForm ℤ n` (`IsClassicallyIntegral`) with Cassels' entries
$f_{ij} = H_{ij}/2$ (`casselsMat`) and determinant $d = \det H/2^n$; the genus `Siegel.SameGenus`; local forms over
`ℤ_[p]`.

**Proves** Lemma 4.3 (`sameGenus_of_congr`): forms of the same determinant $d \ne 0$, equivalent over $\mathbb R$, with
$f_{ij} \equiv g_{ij} \pmod{4d}$, are in the same genus.

*Proof.* Cassels refers to Chapter 8, Lemma 5.2 (not formalized in the library). Here, prime by prime, the local
statement `CongrLocal.meq_of_congr` (`Ch9Sec4LocalPadic.lean`): symmetric matrices $A, B$ over $\mathbb Z_p$ with
$\det A \ne 0$, $\det A \mid c$, $B \equiv A \pmod{4c}$ and $\det B / \det A$ a unit square are congruent. It is applied
to Cassels' matrices with $c = d$; a congruence of Cassels' matrices is an equivalence of the forms
(`isometricGL_of_meq_casselsMat`).
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec4LocalPadic
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Tamagawa.Measure.LerayPadic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-- **From congruent Cassels matrices to equivalent forms** over a domain $R$ of characteristic $0$ (e.g.
$\mathbb Z_p$, $\mathbb R$): if $T^{\mathsf T}(f_{ij})T = (g_{ij})$ over $R$ with $\det T$ a unit, then $f \cong g$
over $R$. -/
theorem isometricGL_of_meq_casselsMat' {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {f g : QuadForm ℤ n}
    (hf : IsClassicallyIntegral f) (hg : IsClassicallyIntegral g)
    (h : CongrLocal.MEq ((casselsMat f).map (Int.castRingHom R)) ((casselsMat g).map (Int.castRingHom R))) :
    IsometricGL (f.map (Int.castRingHom R)) (g.map (Int.castRingHom R)) := by
  obtain ⟨T, hT, hTe⟩ := h
  have hH : ∀ q : QuadForm ℤ n, IsClassicallyIntegral q →
      (q.map (Int.castRingHom R)).hessian = (2 : R) • (casselsMat q).map (Int.castRingHom R) := by
    intro q hq
    rw [hessian_map, hessian_eq_two_smul_casselsMat hq]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat]
  have hc : ((f.map (Int.castRingHom R)).compMat T).hessian = (g.map (Int.castRingHom R)).hessian := by
    rw [QuadForm.hessian_compMat, hH f hf, hH g hg, Matrix.mul_smul, Matrix.smul_mul, hTe]
  have he := Tamagawa.Measure.LerayPadic.QuadForm.eq_of_hessian_eq hc
  refine ⟨Matrix.nonsingInvUnit T hT, fun x => ?_⟩
  rw [← he, QuadForm.eval_compMat]
  rfl

/-- **From congruent Cassels matrices to equivalent forms over $\mathbb Z_p$** (`isometricGL_of_meq_casselsMat'`). -/
theorem isometricGL_of_meq_casselsMat (p : ℕ) [Fact p.Prime] {f g : QuadForm ℤ n} (hf : IsClassicallyIntegral f)
    (hg : IsClassicallyIntegral g)
    (h : CongrLocal.MEq ((casselsMat f).map (Int.castRingHom ℤ_[p])) ((casselsMat g).map (Int.castRingHom ℤ_[p]))) :
    IsometricGL (f.map (Int.castRingHom ℤ_[p])) (g.map (Int.castRingHom ℤ_[p])) :=
  isometricGL_of_meq_casselsMat' hf hg h

/-- Cassels' determinant: $\det H/2^n = \det(f_{ij})$ for classically integral $f$. -/
theorem hessian_det_div (f : QuadForm ℤ n) (hf : IsClassicallyIntegral f) :
    f.hessian.det / 2 ^ n = (casselsMat f).det := by
  rw [hessian_eq_two_smul_casselsMat hf, det_smul, Fintype.card_fin]
  exact Int.mul_ediv_cancel_left _ (pow_ne_zero _ two_ne_zero)

/-- **Lemma 4.3 from the local statement:** the global assembly, for a local statement `hloc` in dimension $n$. -/
theorem sameGenus_of_congr_of_local
    (hloc : ∀ (p : ℕ) [Fact p.Prime] (A B : Matrix (Fin n) (Fin n) ℤ_[p]) (c : ℤ_[p]), Aᵀ = A → Bᵀ = B →
      A.det ≠ 0 → A.det ∣ c → CongrLocal.MDvd (4 * c) (B - A) → (∃ s, IsUnit s ∧ B.det = s ^ 2 * A.det) →
      CongrLocal.MEq A B)
    (f g : QuadForm ℤ n) (hf : IsClassicallyIntegral f) (hg : IsClassicallyIntegral g)
    (hdet : f.hessian.det = g.hessian.det) (hd0 : f.hessian.det ≠ 0)
    (hreal : IsometricGL (f.map (Int.castRingHom ℝ)) (g.map (Int.castRingHom ℝ)))
    (hcong : ∀ i j, 4 * (f.hessian.det / 2 ^ n) ∣ f.hessian i j / 2 - g.hessian i j / 2) :
    SameGenus f g := by
  refine ⟨fun p _ => ?_, hreal⟩
  have hdf := hessian_det_div f hf
  have hdg := hessian_det_div g hg
  have hd : (casselsMat g).det = (casselsMat f).det := by rw [← hdf, ← hdg, hdet]
  have hd0' : (casselsMat f).det ≠ 0 := by
    intro h0; apply hd0
    rw [hessian_eq_two_smul_casselsMat hf, det_smul, h0, mul_zero]
  apply isometricGL_of_meq_casselsMat p hf hg
  have hsym : ∀ q : QuadForm ℤ n, ((casselsMat q).map (Int.castRingHom ℤ_[p]))ᵀ =
      (casselsMat q).map (Int.castRingHom ℤ_[p]) := fun q => by
    rw [← transpose_map, (casselsMat_isSymm q).eq]
  have hmap : ∀ M : Matrix (Fin n) (Fin n) ℤ, (M.map (Int.castRingHom ℤ_[p])).det = (M.det : ℤ_[p]) :=
    fun M => (RingHom.map_det _ M).symm
  refine hloc p _ _ ((casselsMat f).det : ℤ_[p]) (hsym f) (hsym g) ?_ ?_ ?_ ⟨1, isUnit_one, ?_⟩
  · rw [hmap]; exact_mod_cast hd0'
  · rw [hmap]
  · intro i j
    have h1 := (hcong i j).neg_right
    rw [hdf, neg_sub] at h1
    have h2 := map_dvd (Int.castRingHom ℤ_[p]) h1
    simpa [casselsMat] using h2
  · rw [hmap, hmap, hd, one_pow, one_mul]

/-- **Cassels, Lemma 4.3** (Ch. 9, p. 141): *let $f(\mathbf x), g(\mathbf x)$ be integral forms of determinant
$d \ne 0$. Suppose that they are real-equivalent, and that $f_{ij} \equiv g_{ij} \pmod{4d}$ (all $i, j$). Then $f, g$
are in the same genus.*

Here `f g : QuadForm ℤ n` are integral in Cassels' (classical) sense (`IsClassicallyIntegral`), with Cassels' entries
$f_{ij} = H_{ij}/2$ (`f.hessian i j / 2`, an exact division) and determinant $d = \det H/2^n$; the hypotheses are
`hdet` (equal determinants), `hd0` ($d \ne 0$), `hreal` (equivalence over $\mathbb R$) and `hcong` (the congruences
modulo $4d$). *Proof:* not Cassels' reference to Chapter 8, Lemma 5.2, but the local statement
`CongrLocal.meq_of_congr` at every prime (module docstring). -/
@[kb "cassels1978" "Ch. 9, Lemma 4.3, p. 141"]
theorem sameGenus_of_congr (f g : QuadForm ℤ n) (hf : IsClassicallyIntegral f) (hg : IsClassicallyIntegral g)
    (hdet : f.hessian.det = g.hessian.det) (hd0 : f.hessian.det ≠ 0)
    (hreal : IsometricGL (f.map (Int.castRingHom ℝ)) (g.map (Int.castRingHom ℝ)))
    (hcong : ∀ i j, 4 * (f.hessian.det / 2 ^ n) ∣ f.hessian i j / 2 - g.hessian i j / 2) :
    SameGenus f g :=
  sameGenus_of_congr_of_local (fun p _ => CongrLocal.meq_of_congr (p := p) (Fin n)) f g hf hg hdet hd0 hreal hcong

end QuadFormsKB.Siegel
