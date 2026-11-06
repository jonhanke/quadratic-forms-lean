/-
# Hanke 2005, Lemma 6.1: masses of two lattices on the same space, totally definite case

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $F$ totally real, $Q_0$ totally positive definite over $\mathcal O_F$, lattices $L$, $M$ on $V = (F^n, Q_0)$ of any
Steinitz class (`Lat F n`), not necessarily integral, the mass `Lattices.mass` and the stabilizers $O(\hat L)$ (`locStab`).

**Proves** `lemma61_definite`: $\mathrm{Mass}(L) = \mathrm{Mass}(M)\,r(O(\hat M), O(\hat L))$, i.e. Hanke's
$\mathrm{Mass}(\Lambda)/\mathrm{Mass}(\Lambda') = \mathrm{vol}(D'_h)/\mathrm{vol}(D_h)$.
-/
import QuadFormsKB.Tamagawa.LatticeChangeGlobal
import QuadFormsKB.Literature.Hanke2005.Sec6Defs
import QuadFormsKB.Lattices.ClassFinite

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {n : ℕ}


section Scaling

open Matrix

/-- The scalar matrix $c\cdot 1 \in \mathrm{GL}_n(F)$. -/
def scalGLF (c : F) (hc : c ≠ 0) : GL (Fin n) F :=
  Units.map (Matrix.scalar (Fin n) : F →+* Matrix (Fin n) (Fin n) F).toMonoidHom (Units.mk0 c hc)

theorem scalGLF_mulVec (c : F) (hc : c ≠ 0) (y : Fin n → F) : (scalGLF c hc).val *ᵥ y = c • y := by
  ext i
  simp [scalGLF]

theorem compMat_scalGLF (Q : QuadForm F n) (c : F) (hc : c ≠ 0) :
    ((c⁻¹) ^ 2 • Q.compMat (scalGLF c hc).val) = Q := by
  apply QuadForm.ext_eval
  intro x
  have h := QuadFormsKB.Tamagawa.evalIn_compMat_gl (Q₁ := Q) (scalGLF c hc) F x
  show (_ • _ : QuadForm F n).evalIn F x = Q.evalIn F x
  have hs : ∀ (a : F) (R : QuadForm F n), (a • R).evalIn F x = a * R.evalIn F x := fun a R => by
    rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, QuadForm.smul_coeff]
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [hs, h, show (scalGLF c hc).val.map (algebraMap F F) = (scalGLF c hc).val from by ext i j; simp,
    scalGLF_mulVec, evalIn_smul']
  field_simp

/-- Scaling a lattice by a nonzero scalar does not change the mass. -/
theorem mass_scal (Q : QuadForm F n) (c : F) (hc : c ≠ 0) (L : Lat F n) :
    mass Q (Lat.image (scalGLF c hc) L) = mass Q L := by
  have h := QuadFormsKB.Tamagawa.LatChange.mass_similar Q (c := (c⁻¹) ^ 2) (pow_ne_zero _ (inv_ne_zero hc))
    (scalGLF c hc) L
  rw [compMat_scalGLF] at h
  exact h.symm

/-- Scaling a lattice by a nonzero scalar does not change its local stabilizer. -/
theorem locStab_scal (Q : QuadForm F n) (c : F) (hc : c ≠ 0) (L : Lat F n) :
    locStab Q (Lat.image (scalGLF c hc) L) = locStab Q L := by
  ext h
  have key : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      locAct v ((h v : orthGroup Q _) : GL (Fin n) _) (loc v (Lat.image (scalGLF c hc) L).1) =
        loc v (Lat.image (scalGLF c hc) L).1 ↔
      locAct v ((h v : orthGroup Q _) : GL (Fin n) _) (loc v L.1) = loc v L.1 := by
    intro v
    set g := GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (scalGLF c hc) with hg
    have hcomm : ∀ k : GL (Fin n) (v.adicCompletion F), k * g = g * k := by
      intro k
      ext1
      rw [Units.val_mul, Units.val_mul]
      have : g.val = Matrix.scalar (Fin n) (algebraMap F (v.adicCompletion F) c) := by
        ext i j; by_cases hij : i = j <;> simp [hg, scalGLF, Matrix.scalar_apply, hij]
      rw [this]
      exact ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq).symm
    show locAct v _ (loc v (glImage (scalGLF c hc) L.1)) = loc v (glImage (scalGLF c hc) L.1) ↔ _
    rw [loc_glImage, ← locAct_mul, hcomm, locAct_mul]
    constructor
    · intro e
      rw [locAct_eq_iff, locAct_inv_locAct] at e
      exact e
    · intro e; rw [e]
  exact forall_congr' key

/-- If $aQ$ is integral on $L$ ($a\ne0$), a nonzero integer $d$ makes $(de)^2Q(y)$ integral on $L$ for all integers $e$. -/
theorem exists_scale_int (Q : QuadForm F n) {L : Lat F n} {a : F} (ha : a ≠ 0)
    (hL : IsIntegral (a • Q) L.1) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ (e : 𝓞 F), ∀ y ∈ L.1,
      (algebraMap (𝓞 F) F (d * e)) ^ 2 * Q.evalIn F y ∈ (algebraMap (𝓞 F) F).range := by
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
  have hq' : (algebraMap (𝓞 F) F q) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hq)
  have hp : p ≠ 0 := by
    rintro rfl
    apply ha
    rw [← hpq]; simp
  refine ⟨p * q, mul_ne_zero hp (mem_nonZeroDivisors_iff_ne_zero.mp hq), fun e y hy => ?_⟩
  have h1 := hL y hy
  have hs : (a • Q).evalIn F y = a * Q.evalIn F y := by
    rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, QuadForm.smul_coeff]
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [hs] at h1
  obtain ⟨t, ht⟩ := h1
  have : (algebraMap (𝓞 F) F (p * q * e)) ^ 2 * Q.evalIn F y =
      algebraMap (𝓞 F) F (p * q ^ 3 * e ^ 2 * t) := by
    simp only [map_mul, map_pow]
    rw [ht, ← hpq]
    field_simp
  rw [this]
  exact ⟨_, rfl⟩

theorem isIntegral_scal (Q : QuadForm F n) (c : F) (hc : c ≠ 0) (L : Lat F n)
    (h : ∀ y ∈ L.1, c ^ 2 * Q.evalIn F y ∈ (algebraMap (𝓞 F) F).range) :
    IsIntegral Q (Lat.image (scalGLF c hc) L).1 := by
  rintro x ⟨y, hy, rfl⟩
  show Q.evalIn F ((scalGLF c hc).val *ᵥ y) ∈ _
  rw [scalGLF_mulVec, evalIn_smul']
  exact h y hy

end Scaling

/-- **Lemma 6.1, totally definite case** (Hanke thesis, p. 20): for two lattices $L$, $M$ on $V$,
$\mathrm{Mass}(L)\,\mathrm{vol}(O(\hat L)) = \mathrm{Mass}(M)\,\mathrm{vol}(O(\hat M))$, i.e.
$\mathrm{Mass}(L) = \mathrm{Mass}(M)\cdot r(O(\hat M), O(\hat L))$. -/
@[kb "hanke2005crelle" "Lemma 6.1, p. 20 (totally definite case)"]
theorem lemma61_definite [IsTotallyReal F] (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (L M : Lat F n) :
    mass (Q₀.map (algebraMap (𝓞 F) F)) L =
      mass (Q₀.map (algebraMap (𝓞 F) F)) M *
        relRatio (locStab (Q₀.map (algebraMap (𝓞 F) F)) M) (locStab (Q₀.map (algebraMap (𝓞 F) F)) L) := by
  set Q := Q₀.map (algebraMap (𝓞 F) F) with hQdef
  obtain ⟨aL, haL, hLi⟩ := QuadFormsKB.Lattices.ClassFin.exists_smul_isIntegral Q L.2
  obtain ⟨aM, haM, hMi⟩ := QuadFormsKB.Lattices.ClassFin.exists_smul_isIntegral Q M.2
  obtain ⟨dL, hdL, hL⟩ := exists_scale_int Q haL hLi
  obtain ⟨dM, hdM, hM⟩ := exists_scale_int Q haM hMi
  have hc : (algebraMap (𝓞 F) F (dL * dM)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (mul_ne_zero hdL hdM)
  set c := algebraMap (𝓞 F) F (dL * dM) with hcdef
  have hL' : IsIntegral Q (Lat.image (scalGLF c hc) L).1 :=
    isIntegral_scal Q c hc L fun y hy => by
      have := hL dM y hy
      rwa [hcdef]
  have hM' : IsIntegral Q (Lat.image (scalGLF c hc) M).1 :=
    isIntegral_scal Q c hc M fun y hy => by
      have := hM dL y hy
      rw [hcdef, mul_comm dL dM]; exact this
  have key := QuadFormsKB.Tamagawa.LatChange.mass_eq_mass_mul_relRatio hpd
    (Lat.image (scalGLF c hc) L) (Lat.image (scalGLF c hc) M) hL' hM'
  rw [mass_scal, mass_scal, locStab_scal, locStab_scal] at key
  have hpos : relRatio (locStab Q L) (locStab Q M) ≠ 0 :=
    (relRatio_pos (A := locStab Q L) (B := locStab Q M)
      ⟨(commensurable_locStab Q L M).1.relIndex_ne_zero, (commensurable_locStab Q L M).2.relIndex_ne_zero⟩).ne'
  rw [QuadFormsKB.Tamagawa.LatChange.relRatio_symm' (locStab Q L) (locStab Q M), key]
  field_simp

end QuadFormsKB.Hanke2005
