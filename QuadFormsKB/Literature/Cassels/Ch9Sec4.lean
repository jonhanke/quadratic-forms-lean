/-
# Cassels, Chapter 9, §4: genera, elementary properties

**Layer:** integer-valued forms `Q : QuadForm ℤ n`, the genus `Siegel.SameGenus` (equivalence over every
$\mathbb Z_p$ and over $\mathbb R$), $H$ the Hessian ($\det H = 2^nd$, Cassels' $d = d(f)$ for classically integral
forms).

**Proves**
* Lemma 4.1 for every form (`SameGenus.hessian_det_eq`; the library had it for positive definite forms,
  `SameGenus.det_hessian_eq`): forms in one genus have the same determinant;
* Corollary 1 for every nondegenerate form (`genusClasses_finite`; the library had it for positive definite forms,
  `Siegel.genusFinite`): a genus contains only finitely many classes. *Proof:* not Cassels' (Theorem 1.1, which the
  library has for positive definite forms only), but the finiteness of the classes of lattices in the genus of
  $\mathbb Z^n$ in $(\mathbb Q^n, f)$ (`Lattices.ClassFin.genusClasses_finite_nf`, O'Meara 103:4): a form of the genus is
  rationally equivalent to $f$ (Hasse–Minkowski, `Lattices.isometricGL_rat_of_sameGenus`), hence the Gram form of a
  lattice of that genus.
-/
import QuadFormsKB.Siegel.ThetaCuspidal
import QuadFormsKB.Literature.Cassels.Ch11Sec6Genus
import QuadFormsKB.Lattices.ClassFinite
import QuadFormsKB.Tamagawa.RatBridge

open NumberField Matrix
open QuadFormsKB.HilbertModular (formF)
open QuadFormsKB.Tamagawa.RatBridge (up down evalIn_map_rat evalIn_intCoe_rat toOQ_eq_cast down_up)

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-- **Cassels, Lemma 4.1** (Ch. 9, p. 139): *two forms in the same genus have the same determinant.* For every
integer-valued form (definite, indefinite or degenerate), with $\det H = 2^nd$. *Proof (Cassels'):* $d(f) =
(\det T_p)^2 d(g)$ with $\det T_p$ a unit of $\mathbb Z_p$ for every $p$ (here: modulo every $c \ge 1$,
`det_hessian_zmod`), so $\lvert\det H\rvert = \lvert\det H'\rvert$; and the real equivalence gives the same sign. -/
@[kb "cassels1978" "Ch. 9, Lemma 4.1, p. 139"]
theorem SameGenus.hessian_det_eq {Q Q' : QuadForm ℤ n} (h : SameGenus Q Q') :
    Q.hessian.det = Q'.hessian.det := by
  -- the sign (and the vanishing) from the real equivalence
  obtain ⟨g, hg⟩ := h.2.hessian_eq
  have hreal : (Q'.hessian.det : ℝ) = g.val.det ^ 2 * (Q.hessian.det : ℝ) := by
    have hd := congrArg Matrix.det hg
    rw [hessian_map, hessian_map, det_mul, det_mul, det_transpose] at hd
    have e : ∀ M : Matrix (Fin n) (Fin n) ℤ, (M.map (Int.castRingHom ℝ)).det = (M.det : ℝ) :=
      fun M => by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [e, e] at hd
    rw [← hd]; ring
  have hg0 : 0 < g.val.det ^ 2 := by
    have : g.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
    positivity
  by_cases h0 : Q.hessian.det = 0
  · rw [h0, Int.cast_zero, mul_zero] at hreal
    rw [h0]; exact_mod_cast hreal.symm
  have h0' : Q'.hessian.det ≠ 0 := by
    intro h'; rw [h', Int.cast_zero] at hreal
    exact h0 (by exact_mod_cast (mul_eq_zero.mp hreal.symm).resolve_left hg0.ne')
  -- divisibility both ways, from the equivalence modulo `c`
  have hdvd : ∀ {c : ℕ}, c ≠ 0 → ((c : ℤ) ∣ Q.hessian.det ↔ (c : ℤ) ∣ Q'.hessian.det) := by
    intro c hc
    obtain ⟨u, hu, he⟩ := det_hessian_zmod h hc
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, he]
    constructor
    · intro h0; rw [h0, mul_zero]
    · intro h0; exact (hu.pow 2).mul_right_eq_zero.mp h0
  have h1 : Q.hessian.det ∣ Q'.hessian.det := by
    have := (hdvd (c := Q.hessian.det.natAbs) (by omega)).mp (by simp)
    simpa using this
  have h2 : Q'.hessian.det ∣ Q.hessian.det := by
    have := (hdvd (c := Q'.hessian.det.natAbs) (by omega)).mpr (by simp)
    simpa using this
  have habs : Q.hessian.det.natAbs = Q'.hessian.det.natAbs :=
    Nat.dvd_antisymm (Int.natAbs_dvd_natAbs.mpr h1) (Int.natAbs_dvd_natAbs.mpr h2)
  rcases Int.natAbs_eq_natAbs_iff.mp habs with e | e
  · exact e
  · -- opposite signs contradict the real equivalence
    exfalso
    have hr : (Q'.hessian.det : ℝ) = -(Q.hessian.det : ℝ) := by rw [e]; push_cast; ring
    rw [hr] at hreal
    have hq : (Q.hessian.det : ℝ) ≠ 0 := by exact_mod_cast h0
    have : (1 + g.val.det ^ 2) * (Q.hessian.det : ℝ) = 0 := by linear_combination -hreal
    rcases mul_eq_zero.mp this with h3 | h3
    · nlinarith
    · exact hq h3

open Tamagawa.RatBridge in
/-- Every form in the genus of `f` (`det H ≠ 0`) is the Gram form of a lattice in the genus of $\mathbb Z^n$ in
$(\mathbb Q^n, f)$ (the version of `exists_latOf_of_sameGenus` without positivity, via `isometricGL_rat_of_sameGenus`). -/
theorem exists_latOf_of_sameGenus' {Q Q' : QuadForm ℤ n} (hQ : Q.hessian.det ≠ 0) (hg : SameGenus Q Q') :
    ∃ (γ : GL (Fin n) ℚ) (h : Lattices.IsIntegral (formF (up Q)) (Lattices.latOf γ)),
      Lattices.SameGenus (formF (up Q)) Lattices.intVec (Lattices.latOf γ) ∧
        down (Lattices.gramZ (formF (up Q)) γ h) = Q' := by
  obtain ⟨P, hP, hPe⟩ := (isometricGL_iff_isometricIn _ _).mp
    (Lattices.isometricGL_rat_of_sameGenus Q Q' hg.hessian_det_eq hQ hg)
  set γ : GL (Fin n) ℚ := ((Matrix.isUnit_iff_isUnit_det P).mpr hP).unit
  have hγP : γ.val = P := rfl
  have hval : ∀ x : Fin n → 𝓞 ℚ,
      (formF (up Q)).eval (γ.val *ᵥ Lattices.intCoe x) = algebraMap (𝓞 ℚ) ℚ ((up Q').eval x) := by
    intro x
    have := hPe (Lattices.intCoe x)
    rw [evalIn_map_rat, evalIn_map_rat] at this
    rw [formF_toOQ_eval, hγP, this, evalIn_intCoe_rat]
  have hint : Lattices.IsIntegral (formF (up Q)) (Lattices.latOf γ) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Lattices.mem_glImage.mp hy
    obtain ⟨x, rfl⟩ := Lattices.mem_intVec_iff_exists.mp hw
    exact ⟨(up Q').eval x, (hval x).symm⟩
  have hG : Lattices.gramZ (formF (up Q)) γ hint = up Q' :=
    Lattices.QuadForm.ext_eval fun x => IsFractionRing.injective (𝓞 ℚ) ℚ (by rw [Lattices.algebraMap_eval_gramZ, hval])
  refine ⟨γ, hint, ?_, by rw [hG, down_up]⟩
  have h1 := (Lattices.sameGenus_latOf_iff (formF (up Q)) 1 γ (HilbertModular.isIntegral_latOf_one (up Q)) hint).mpr (by
    rw [HilbertModular.gramZ_one, hG]
    have e : ∀ R : QuadForm ℤ n, R.map Lattices.toOQ = up R := fun R => by rw [toOQ_eq_cast]
    rw [← e, ← e]
    exact (Lattices.formSameGenus_rat_iff Q Q').mpr hg)
  rwa [HilbertModular.latOf_one] at h1

/-- **Cassels, Lemma 1.1** (Ch. 9, p. 127): *two $\mathbb Z$-equivalent forms have the same determinant* (for every
integer-valued form, $\det H = 2^nd$; equivalent forms are in one genus, `IntEquiv.sameGenus`). -/
@[kb "cassels1978" "Ch. 9, Lemma 1.1, p. 127"]
theorem IntEquiv.hessian_det_eq {Q Q' : QuadForm ℤ n} (h : IntEquiv Q Q') : Q.hessian.det = Q'.hessian.det :=
  h.sameGenus.hessian_det_eq

/-- **Cassels, Lemma 4.1, Corollary 1** (Ch. 9, p. 139): *the number of equivalence classes in a genus is finite.* For
every integer-valued form with $\det H \ne 0$, definite or indefinite (`genusClasses` is the set of
$\mathrm{GL}_n(\mathbb Z)$-classes of the genus). -/
@[kb "cassels1978" "Ch. 9, Lemma 4.1, Cor. 1, p. 139"]
theorem genusClasses_finite {f : QuadForm ℤ n} (hf : f.hessian.det ≠ 0) : (genusClasses f).Finite := by
  have hnd : (formF (Tamagawa.RatBridge.up f)).Nondegenerate := by
    rw [Tamagawa.RatBridge.formF_up]; exact Lattices.nondegenerate_map_of_det_ne_zero f hf
  refine ((Lattices.ClassFin.genusClasses_finite_nf _ hnd Lattices.stdLat).image
    (fun c : Lattices.LatClass (formF (Tamagawa.RatBridge.up f)) =>
      classOf (Tamagawa.RatBridge.zForm f c.out))).subset ?_
  rintro c ⟨f', rfl, hg⟩
  obtain ⟨γ, hi, hs, hQ'⟩ := exists_latOf_of_sameGenus' hf hg
  set M : Lattices.Lat ℚ n := ⟨Lattices.latOf γ, Lattices.latOf_isLattice γ⟩
  have hc : (Quotient.mk _ M : Lattices.LatClass (formF (Tamagawa.RatBridge.up f))) ∈
      Lattices.genusClasses (formF (Tamagawa.RatBridge.up f)) Lattices.stdLat := ⟨M, rfl, hs⟩
  refine ⟨_, hc, ?_⟩
  obtain ⟨γ', hγ', hi', -⟩ : ∃ γ' : GL (Fin n) ℚ, (Quotient.mk _ M :
      Lattices.LatClass (formF (Tamagawa.RatBridge.up f))).out.1 = Lattices.latOf γ' ∧
      Lattices.IsIntegral (formF (Tamagawa.RatBridge.up f)) (Lattices.latOf γ') ∧ True := by
    have hs' := HilbertModular.sameGenus_out hc
    obtain ⟨γ', hγ', hi'⟩ := Tamagawa.RatBridge.exists_free_of_sameGenus f _ hs'
    exact ⟨γ', hγ', hi', trivial⟩
  have hiso : Lattices.IsIsometric (formF (Tamagawa.RatBridge.up f)) (Lattices.latOf γ') (Lattices.latOf γ) := by
    rw [← hγ']
    exact Quotient.exact (Quotient.out_eq (Quotient.mk (Lattices.latSetoid (formF (Tamagawa.RatBridge.up f))) M))
  refine classOf_eq_classOf_iff.mpr ?_
  refine IsometricGL.trans (Tamagawa.RatBridge.zForm_intEquiv f _ γ' hγ' hi') ?_
  rw [← hQ']
  exact (Tamagawa.RatBridge.intEquiv_down_gramZ_iff f γ' γ hi' hi).mpr (Lattices.IsIsometric.symm _ hiso)

end QuadFormsKB.Siegel
