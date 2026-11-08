/-
# Cassels, Chapter 11, Example 11: the analogue of Chapter 10, Example 3

**Layer** (as in `Ch10/Example3.lean` and `Ch11Examples3.lean`): $V = \mathbb Q^3$ with the form $Q$ = `Q : QuadForm ℚ 3`;
the lattice $\Lambda$ = `L : Lat ℚ 3`; the primes $p$ are `v : HeightOneSpectrum (𝓞 ℚ)`; $\Lambda_p$ = `loc v L.1`;
$O^+(\Lambda_p)$ = `locStabV Q v L ⊓ Tamagawa.soSub Q _`; $\theta(O^+(\Lambda_p))$ = `localSpinorNormGroup`;
$p\Lambda_p$ = `pLat v L`.

**Proves** `ex11_of_units`: the proof of `ch10_example3` with `strongApproximationSpinAt` (approximation at all primes
$w \ne q$, $Q$ isotropic at $q$) in place of `strongApproximationSpin` (which needs $Q$ indefinite), and
`exists_evalIn_eq_mul_of_isSquare` in place of `exists_evalIn_eq_mul` (the element $t$ is chosen positive, so it is
a square at the real place). It keeps hypothesis (iii) of Chapter 10, Example 3 (`hU`: every $p$-adic unit is a spinor norm
of $O^+(\Lambda_p)$, for every prime $p$), which the printed Example 11 does not state; it is used at the primes $w$ outside
$P^*$ to choose local rotations $\sigma_w \in O^+(\Lambda_w)$ of the spinor norm of $t$ (Example 1 only covers $w \in P^*$).

**What is proved, and a gap.** The congruence is proved locally, $\alpha b - \eta_p b \in p\Lambda_p$ for $p \in P^*$ (as in
Cassels' mod-$p\Lambda_p$ reading), together with $\alpha\Lambda_w = \Lambda_w$ for $w \ne q$. The global form of
`Ex11Statement` ($\alpha b - \eta_p b \in p\Lambda$) additionally needs $\alpha b \in \Lambda_q$, and the approximation theorem
gives no control at $q$; this is not proved here (see `ex11_of_units`).
-/
import QuadFormsKB.Literature.Cassels.Ch10.Example3
import QuadFormsKB.Literature.Cassels.Ch11Examples3
import QuadFormsKB.Literature.OMeara.Sec101BD

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- Helper (file-local): as in `Ch10/Example3.lean`, use the library's algebra structure on $\mathbb Q_p$. -/
local instance (priority := high) algAdicEx11Q (w : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (w.adicCompletion ℚ) := algAdicEx3 ℚ w

/-- Helper: an element of a number field that is nonnegative at every real place is a square at every infinite place.
Arguments: `w` the infinite place, `t` the element, `ht` its nonnegativity at `w` if `w` is real. -/
theorem isSquare_algebraMap_infinite_of_nonneg {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) {t : F}
    (ht : ∀ hw : w.IsReal, 0 ≤ InfinitePlace.embedding_of_isReal hw t) :
    IsSquare (algebraMap F w.Completion t) := by
  by_cases hw : w.IsReal
  · exact (isSquare_algebraMap_real_iff w hw t).mpr (ht hw)
  · exact isSquare_completion_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.mp hw) _

section Approx11

variable (Q : QuadForm ℚ 3)

/-- Helper: **global rotation and strong approximation away from $q$** (the global half of the proof of Example 11).
Arguments: `Q` a nondegenerate (`hQ`) ternary form over $\mathbb Q$ isotropic at the prime `q` (`hq`), `L` a lattice, `t` a
positive rational (`ht`), `σ` a family of local rotations $\sigma_w \in O^+(\Lambda_w)$ (`hσL`, `hσso`) all of spinor norm
the class of `t` (`hσθ`). Then there is a rational rotation $\beta \in O^+(V)$ with $\beta_w^{-1}\sigma_w \in O^+(\Lambda_w)$ of
spinor norm $1$ at every prime $w \ne q$. (Proof as `exists_rotation_approx`, with $\rho = \tau_x\tau_y$ from
`exists_evalIn_eq_mul_of_isSquare` and `strongApproximationSpinAt`.) -/
theorem exists_rotation_approx_at (hQ : Q.Nondegenerate) (q : HeightOneSpectrum (𝓞 ℚ))
    (hq : Q.IsotropicIn (q.adicCompletion ℚ)) (L : Lat ℚ 3) {t : ℚ} (ht : 0 < t)
    (σ : ∀ w : HeightOneSpectrum (𝓞 ℚ), orthGroup Q (w.adicCompletion ℚ))
    (hσL : ∀ w, σ w ∈ locStabV Q w L) (hσso : ∀ w, σ w ∈ Tamagawa.soSub Q (w.adicCompletion ℚ))
    (hσθ : ∀ w, spinorNorm Q (w.adicCompletion ℚ) (σ w) = sqClassOf (algebraMap ℚ (w.adicCompletion ℚ) t)) :
    ∃ β ∈ Tamagawa.soSub Q ℚ, ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ q →
      (orthMap Q (w.adicCompletion ℚ) β)⁻¹ * σ w ∈ locStabV Q w L ⊓ Tamagawa.soSub Q (w.adicCompletion ℚ) ∧
      spinorNorm Q (w.adicCompletion ℚ) ((orthMap Q (w.adicCompletion ℚ) β)⁻¹ * σ w) = 1 := by
  classical
  have ht' : t ≠ 0 := ht.ne'
  obtain ⟨x, y, hy, hxy⟩ := exists_evalIn_eq_mul_of_isSquare Q hQ (le_refl 3) ht'
    (fun w => Or.inr (isSquare_algebraMap_infinite_of_nonneg w fun hw => by
      rw [eq_ratCast (InfinitePlace.embedding_of_isReal hw) t]
      exact_mod_cast ht.le))
  have hx0 : Q.evalIn ℚ x ≠ 0 := by rw [hxy]; exact mul_ne_zero ht' hy
  set ρ : orthGroup Q ℚ := symm Q ℚ x * symm Q ℚ y with hρ
  have hρso : ρ ∈ Tamagawa.soSub Q ℚ := by
    rw [Tamagawa.mem_soSub, hρ, Subgroup.coe_mul, Units.val_mul, det_mul, symm_det Q ℚ hx0, symm_det Q ℚ hy]
    norm_num
  have hρθ : ∀ w : HeightOneSpectrum (𝓞 ℚ), spinorNorm Q (w.adicCompletion ℚ) (orthMap Q _ ρ) =
      sqClassOf (algebraMap ℚ (w.adicCompletion ℚ) t) := by
    intro w
    rw [hρ, spinorNorm_orthMap_symm_mul Q hQ w hx0 hy, hxy, map_mul, map_mul]
    have hyv : algebraMap ℚ (w.adicCompletion ℚ) (Q.evalIn ℚ y) ≠ 0 := (map_ne_zero _).mpr hy
    have htv : algebraMap ℚ (w.adicCompletion ℚ) t ≠ 0 := (map_ne_zero _).mpr ht'
    rw [mul_assoc, sqClassOf_mul htv (mul_ne_zero hyv hyv),
      (sqClassOf_eq_one_iff (mul_ne_zero hyv hyv)).mpr ⟨_, rfl⟩, mul_one]
  let A : OAf Q := ⟨σ, by
    filter_upwards [loc_eventually_std L.2] with w hw
    exact (locStabV_eq_stdStab Q w L hw).mp (hσL w)⟩
  set h : OAf Q := (diagF Q ρ)⁻¹ * A with hh
  have hhw : ∀ w, h w = (orthMap Q (w.adicCompletion ℚ) ρ)⁻¹ * σ w := fun w => rfl
  have hhK : h ∈ spinorKernelAf Q := by
    intro w
    rw [hhw, spinorKernel_eq_ker Q _ hQ, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker,
      map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hρθ, hσθ, inv_mul_cancel]
    refine ⟨rfl, ?_⟩
    have h1 := orthMap_mem_soSub Q (w.adicCompletion ℚ) hρso
    have h2 := (Tamagawa.soSub Q (w.adicCompletion ℚ)).mul_mem ((Tamagawa.soSub Q _).inv_mem h1) (hσso w)
    exact Units.ext h2
  obtain ⟨δ, hδK, hδL⟩ := strongApproximationSpinAt.approx Q (le_refl 3) hQ q hq L h hhK
  refine ⟨ρ * δ, (Tamagawa.soSub Q ℚ).mul_mem hρso (spinorKernel_le_soSub Q ℚ hδK), fun w hwq => ?_⟩
  have hexp : (orthMap Q (w.adicCompletion ℚ) (ρ * δ))⁻¹ * σ w =
      ((diagF Q δ)⁻¹ * h) w := by
    rw [map_mul, _root_.mul_inv_rev]
    rw [show ((diagF Q δ)⁻¹ * h) w = (orthMap Q (w.adicCompletion ℚ) δ)⁻¹ * h w from rfl, hhw]
    group
  rw [hexp]
  have hmem : ((diagF Q δ)⁻¹ * h) w ∈ locStabV Q w L := hδL w hwq
  have hδw : orthMap Q (w.adicCompletion ℚ) δ ∈ spinorKernel Q (w.adicCompletion ℚ) :=
    orthMap_mem_spinorKernel Q w hδK
  have hhw' : h w ∈ spinorKernel Q (w.adicCompletion ℚ) := hhK w
  have hk : ((diagF Q δ)⁻¹ * h) w ∈ spinorKernel Q (w.adicCompletion ℚ) :=
    (spinorKernel Q _).mul_mem ((spinorKernel Q _).inv_mem hδw) hhw'
  refine ⟨⟨hmem, spinorKernel_le_soSub Q _ hk⟩, ?_⟩
  exact (Subgroup.mem_inf.mp ((spinorKernel_eq_ker Q (w.adicCompletion ℚ) hQ).le hk)).1

end Approx11

section Example11Main

variable (Q : QuadForm ℚ 3)

/-- **Cassels, Ch. 11, Example 11** (p. 253), with hypothesis (iii) of Chapter 10, Example 3 added (`hU`). Arguments as in
`Ex11Statement.holds` (`Q`, `hQ`, `L`, `hint`, `q`, `hq`, `Pstar`, `h2`, `hani`, `hdet`, `b`, `hb`, `hbv`, `η`, `hη`) plus
`hU`: for every prime $p$ every $p$-adic unit is a spinor norm of $O^+(\Lambda_p)$ (`localSpinorNormGroup`). Conclusion: a
rotation $\alpha \in O^+(V)$ with $\alpha\Lambda_w = \Lambda_w$ for all primes $w \ne q$ and, for $p \in P^*$, the congruence
$\alpha b \equiv \eta_p b \pmod{p\Lambda_p}$ in the localization (`locVec v (α b) - η v • locVec v b ∈ pLat v L`).

*Note on the printed statement.* The printed Example 11 omits (iii) and indefiniteness of $Q$. The proof needs (iii) to
choose, at the primes $w \notin P^*$ (including $w$ dividing $2\det$), a local rotation of $\Lambda_w$ whose spinor norm is the
class of $t = \prod_{\eta_p = -1} p$ (a unit there); without it $\theta(O^+(\Lambda_w))$ may not contain that class and the
argument gives nothing at such $w$. Whether the printed statement is false without (iii) is not decided here. The global
congruence $\alpha b - \eta_p b \in p\Lambda$ of `Ex11Statement` is stronger than the one proved: it also needs
$\alpha b \in \Lambda_q$, and strong approximation away from $q$ gives no control at $q$ (for $Q$ indefinite use
`ch10_example3`).

*Proof* as `ch10_example3` (see its docstring), with $t$ taken positive (the absolute value of a product of prime
generators), $q \notin P^*$ ($Q$ is isotropic at $q$ but anisotropic on $P^*$), `exists_rotation_approx_at` for the global
rotation, and `local_congruence` at $p \in P^*$ (here $p \ne q$). -/
@[kb "cassels1978" "Ch. 11, Ex. 11, p. 253 (with hypothesis (iii) of Ch. 10, Ex. 3)"]
theorem ex11_of_units (hQ : Q.Nondegenerate) (L : Lat ℚ 3)
    (hint : ∀ x ∈ L.1, ∃ z : ℤ, Q.eval x = z)
    (q : HeightOneSpectrum (𝓞 ℚ)) (hq : Q.IsotropicIn (q.adicCompletion ℚ))
    (hU : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 → u ∈ localSpinorNormGroup Q hQ v L)
    (Pstar : Set (HeightOneSpectrum (𝓞 ℚ)))
    (h2 : ∀ v ∈ Pstar, (2 : 𝓞 ℚ) ∉ v.asIdeal)
    (hani : ∀ v ∈ Pstar, ¬ Q.IsotropicIn (v.adicCompletion ℚ))
    (hdet : ∀ v ∈ Pstar, ∃ γ : GL (Fin 3) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧
      Valued.v (locGram Q v γ).det = exp (-1 : ℤ))
    (b : Fin 3 → ℚ) (hb : b ∈ L.1)
    (hbv : ∀ v ∈ Pstar, Valued.v (Q.evalIn (v.adicCompletion ℚ) (locVec v b)) = exp (-1 : ℤ))
    (η : HeightOneSpectrum (𝓞 ℚ) → ℚ) (hη : ∀ v ∈ Pstar, η v = 1 ∨ η v = -1) :
    ∃ α ∈ Tamagawa.soSub Q ℚ,
      (∀ v ∈ Pstar, ((orthMap Q (v.adicCompletion ℚ) α : orthGroup Q _) : GL (Fin 3) (v.adicCompletion ℚ)).val *ᵥ
          locVec v b - algebraMap ℚ (v.adicCompletion ℚ) (η v) • locVec v b ∈ pLat v L) ∧
      ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ q →
        locAct w ((orthMap Q (w.adicCompletion ℚ) α : orthGroup Q _) : GL (Fin 3) (w.adicCompletion ℚ))
          (loc w L.1) = loc w L.1 := by
  classical
  have hfin : Pstar.Finite := (finite_setOf_det_valued_eq Q hQ L).subset fun v hv => hdet v hv
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := hfin.toFinset.filter (fun v => η v = -1) with hS
  have hSP : ∀ v ∈ S, v ∈ Pstar := fun v hv => hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hSη : ∀ v ∈ S, η v = -1 := fun v hv => (Finset.mem_filter.mp hv).2
  set ε : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun _ => 1 with hε
  set t0 : 𝓞 ℚ := ∏ w ∈ S, primeGen w ^ ε w with ht0
  set t1 : ℚ := algebraMap (𝓞 ℚ) ℚ t0 with ht1
  set t : ℚ := |t1| with ht
  have ht1ne : t1 ≠ 0 := by
    refine (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) ℚ)).mpr ?_
    exact Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (primeGen_ne_zero w)
  have htpos : 0 < t := abs_pos.mpr ht1ne
  have htv_abs : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap ℚ (v.adicCompletion ℚ) t) = Valued.v (algebraMap ℚ (v.adicCompletion ℚ) t1) := by
    intro v
    rcases abs_choice t1 with h | h
    · rw [ht, h]
    · rw [ht, h, map_neg, Valuation.map_neg]
  have htin : ∀ v ∈ S, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) t) = exp (-1 : ℤ) := by
    intro v hv
    rw [htv_abs, ht1, ← IsScalarTower.algebraMap_apply, ht0, valued_prod_primeGen_of_mem v ε hv]
    simp [hε]
  have htout : ∀ v ∉ S, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) t) = 1 := by
    intro v hv
    rw [htv_abs, ht1, ← IsScalarTower.algebraMap_apply, ht0]
    exact valued_prod_primeGen_of_not_mem v ε hv
  have htv0 : ∀ v : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (v.adicCompletion ℚ) t ≠ 0 := fun v =>
    (map_ne_zero _).mpr htpos.ne'
  have hloc : ∀ w : HeightOneSpectrum (𝓞 ℚ), ∃ σ : orthGroup Q (w.adicCompletion ℚ),
      σ ∈ locStabV Q w L ⊓ Tamagawa.soSub Q (w.adicCompletion ℚ) ∧
      spinorNorm Q (w.adicCompletion ℚ) σ = sqClassOf (algebraMap ℚ (w.adicCompletion ℚ) t) := by
    intro w
    have hmem : Units.mk0 _ (htv0 w) ∈ localSpinorNormGroup Q hQ w L := by
      by_cases hw : w ∈ Pstar
      · obtain ⟨γ, hγ, hd⟩ := hdet w hw
        have := localSpinorNormGroup_eq_top_of_det Q w hQ (h2 w hw) L γ hγ (loc_evalIn_le_one Q L w hint) hd
        rw [this]; exact Subgroup.mem_top _
      · exact hU w _ (htout w fun hS' => hw (hSP w hS'))
    obtain ⟨σ, hσ, hθ⟩ := (mem_localSpinorNormGroup Q hQ w L).mp hmem
    exact ⟨σ, hσ, by rw [hθ, sqClassOf_of_ne_zero (htv0 w)]⟩
  choose σ hσ hσθ using hloc
  obtain ⟨β, hβso, hβ⟩ := exists_rotation_approx_at Q hQ q hq L htpos σ (fun w => (hσ w).1)
    (fun w => (hσ w).2) hσθ
  have hβstab : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ q → orthMap Q (w.adicCompletion ℚ) β ∈ locStabV Q w L := by
    intro w hw
    have h1 := (hβ w hw).1.1
    have h2' : orthMap Q (w.adicCompletion ℚ) β = σ w * ((orthMap Q (w.adicCompletion ℚ) β)⁻¹ * σ w)⁻¹ := by
      group
    rw [h2']
    exact (locStabV Q w L).mul_mem (hσ w).1 ((locStabV Q w L).inv_mem h1)
  refine ⟨β, hβso, fun v hv => ?_, fun w hw => hβstab w hw⟩
  have hvq : v ≠ q := fun h => hani v hv (h ▸ hq)
  obtain ⟨γ, hγ, hd⟩ := hdet v hv
  set K := v.adicCompletion ℚ with hK
  have hbmem : locVec v b ∈ loc v L.1 := locVec_mem_loc v hb
  have hβu : orthMap Q K β = σ v * ((orthMap Q K β)⁻¹ * σ v)⁻¹ := by group
  have hηv := hη v hv
  rw [hβu]
  refine local_congruence v Q hQ (h2 v hv) L γ hγ (loc_evalIn_le_one Q L v hint) hd (hani v hv) (hσ v)
    (hβ v hvq).1 (hβ v hvq).2 (hσθ v) (algebraMap ℚ K (η v)) ?_ hbmem (hbv v hv)
  rcases hηv with h | h
  · left
    refine ⟨by rw [h, map_one], htout v fun hvS => ?_⟩
    have := hSη v hvS
    rw [h] at this
    norm_num at this
  · right
    refine ⟨by rw [h, map_neg, map_one], htin v ?_⟩
    exact Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hv, h⟩

end Example11Main

end QuadFormsKB.Lattices
