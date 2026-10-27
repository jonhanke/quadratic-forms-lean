/-
# O'Meara §101B–§101D: the orthogonal group over a global field

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n`; $O(V)$ = `orthGroup Q F`,
$O^+(V)$ = `Tamagawa.soSub Q F`, the spinor kernel $O'(V)$ = `spinorKernel Q F` (`Lattices/SpinorKernel.lean`), the
spinor norm $\theta$ = `spinorNormHom` (`Lattices/SpinorNorm.lean`); the localization $\sigma \mapsto \sigma_\mathfrak p$
is `orthMap Q F_𝔭` (O'Meara's notation, Conventions 101:5).

**Proves**
* `isSquare_of_eventually_isSquare`: an element of $F$ which is a square in $F_\mathfrak p$ for almost all finite
  $\mathfrak p$ is a square (the Global Square Theorem, in the form used in the proof of 101:12; from the Dedekind
  density argument of `Literature/LocalGlobal/SquaresLocalGlobal.lean`);
* Proposition 101:12 for the spinor kernel (`mem_spinorKernel_iff_forall`, `mem_spinorKernel_iff_eventually`): a rotation
  $\sigma \in O^+(V)$ lies in $O'(V)$ if and only if $\sigma_\mathfrak p \in O'(V_\mathfrak p)$ at every finite
  $\mathfrak p$ (even: at almost all $\mathfrak p$).

**Defines** (§101D, p. 296) the group $D = \theta(O^+(V))$, as the subgroup `spinorNormGroup Q hQ` of $F^\times$ of the
$\alpha$ with $\alpha F^{\times 2} \in \theta(O^+(V))$; it contains $F^{\times 2}$ (`sq_mem_spinorNormGroup`).

*Deviation in 101:12.* O'Meara's 101:12 is about $\Omega_n(V)$, the commutator subgroup of $O_n(V)$; the library has
no $\Omega_n$, and the statement here is about the spinor kernel $O'_n(V)$. This is exactly the first step of
O'Meara's proof ("So $\sigma \in O'_n(V)$. In particular this proves the proposition when $1 \le n \le 3$", p. 294, where
$\Omega_n = O'_n$); the case $n \ge 4$ of the book's statement, which needs 95:2 and Lemma 101:11, is not
formalized. Only finite spots are used: the archimedean conditions are not needed for $O'$.
-/
import QuadFormsKB.Literature.LocalGlobal.SquaresLocalGlobal
import QuadFormsKB.Lattices.SACorrection
import QuadFormsKB.Tamagawa.LocalVolume

open NumberField IsDedekindDomain Matrix Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### The Global Square Theorem at almost all finite places -/

/-- **An element of $F$ which is a square at almost all finite places is a square** (the Global Square Theorem,
O'Meara 1973, 65:15, in the form used in the proof of 101:12). The proof is that of
`SqLG.isSquare_iff_everywhere`: if $a$ were not a square, almost every prime would split in $F(\sqrt a)$, against
`SqLG.not_almost_all_split`. -/
theorem isSquare_of_eventually_isSquare (a : F)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IsSquare (algebraMap F (v.adicCompletion F) a)) :
    IsSquare a := by
  classical
  by_contra hd
  have ha0 : a ≠ 0 := by rintro rfl; exact hd ⟨0, by simp⟩
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
  have hy0 : (y : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  set b : 𝓞 F := x * y with hbdef
  have hb : (b : F) = algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y * (y : F) ^ 2 := by
    simp only [hbdef]
    push_cast
    change (x : F) * (y : F) = (x : F) / (y : F) * (y : F) ^ 2
    field_simp
  have hbd : ¬ IsSquare (b : F) := by
    rintro ⟨r, hr⟩
    apply hd
    refine ⟨r / y, ?_⟩
    have e : algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y
        = (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y * (y : F) ^ 2) / ((y : F) * (y : F)) := by
      field_simp
    rw [e, ← hb, hr]
    field_simp
  have hb0 : b ≠ 0 := by
    intro h0
    apply hbd
    rw [h0]
    exact ⟨0, by simp⟩
  have hfin : {v : HeightOneSpectrum (𝓞 F) | 2 * b ∈ v.asIdeal}.Finite := by
    have h2 : (2 * b : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hb0
    have := Ideal.finite_factors (R := 𝓞 F) (I := Ideal.span {2 * b}) (by simpa using h2)
    convert this using 2 with v
    simp [Ideal.dvd_span_singleton]
  have hfin' := Filter.eventually_cofinite.mp h
  obtain ⟨L, _, _, _, s, hs, hspan⟩ := QuadFormsKB.Lam.exists_quadExt (b : F) hbd
  apply SqLG.not_almost_all_split (b : F) hbd s hs hspan (hfin.toFinset ∪ hfin'.toFinset)
  intro v hv
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or, not_not] at hv
  apply SqLG.exists_two_primes_of_isSquare b hbd s hs hspan v hv.1
  obtain ⟨t, ht⟩ := hv.2
  refine ⟨t * algebraMap F (v.adicCompletion F) (y : F), ?_⟩
  rw [hb, map_mul, ht, map_pow]
  ring

/-! ### Proposition 101:12 for the spinor kernel -/

variable (Q : QuadForm F n)

/-- The determinant of a product of $r$ symmetries is $(-1)^r$, so a rotation is a product of an even number. -/
theorem even_length_of_symmProd_mem_soSub {xs : List (Fin n → F)} (hxs : ∀ x ∈ xs, Q.evalIn F x ≠ 0)
    (hσ : symmProd Q F xs ∈ Tamagawa.soSub Q F) : Even xs.length := by
  have h := detHom_symmProd Q F xs hxs
  rw [detHom_val, show ((symmProd Q F xs : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 from hσ] at h
  have hne : (-1 : F) ≠ 1 := by
    intro h'
    have : (2 : F) = 0 := by linear_combination -h'
    exact two_ne_zero this
  exact (neg_one_pow_eq_one_iff_even hne).mp h.symm

/-- **Proposition 101:12 for $O'$, almost-everywhere form** (O'Meara 1973, §101B, p. 294, first step of the proof):
for a regular $V$ and a rotation $\sigma \in O^+(V)$, $\sigma \in O'(V)$ if and only if $\sigma_\mathfrak p \in
O'(V_\mathfrak p)$ for almost all finite $\mathfrak p$. Variant of 101:12: the book's statement is about $\Omega_n$
(see the module docstring). -/
@[kb "omeara1963" "§101B, 101:12, p. 294 (variant: the spinor kernel O' instead of Ω_n; first step of the proof)"]
theorem mem_spinorKernel_iff_eventually (hQ : Q.Nondegenerate) {σ : orthGroup Q F}
    (hσ : σ ∈ Tamagawa.soSub Q F) :
    σ ∈ spinorKernel Q F ↔ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      orthMap Q (v.adicCompletion F) σ ∈ spinorKernel Q (v.adicCompletion F) := by
  constructor
  · intro h
    exact Filter.Eventually.of_forall fun v => orthMap_mem_spinorKernel Q v h
  · intro h
    obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q F hQ σ
    refine ⟨xs, ⟨hxs, even_length_of_symmProd_mem_soSub Q hxs hσ, ?_⟩, rfl⟩
    refine isSquare_of_eventually_isSquare _ ?_
    filter_upwards [h] with v hv
    obtain ⟨ys, ⟨hya, -, hys⟩, hyeq⟩ := hv
    have hxs' : ∀ x ∈ xs.map (locVec v), Q.evalIn (v.adicCompletion F) x ≠ 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      rw [evalIn_locVec]
      exact (map_ne_zero _).mpr (hxs x hx)
    rw [orthMap_symmProd] at hyeq
    have hcl := sqClassOf_valProd_eq Q (v.adicCompletion F) hQ hya hxs' hyeq
    rw [(sqClassOf_eq_one_iff (valProd_ne_zero Q _ hya)).mpr hys] at hcl
    rw [← valProd_map_locVec]
    exact (sqClassOf_eq_one_iff (valProd_ne_zero Q _ hxs')).mp hcl.symm

/-- **Proposition 101:12 for $O'$** (O'Meara 1973, §101B, p. 294, first step of the proof): for a regular $V$ and a
rotation $\sigma \in O^+(V)$, $\sigma \in O'(V)$ if and only if $\sigma_\mathfrak p \in O'(V_\mathfrak p)$ at every
finite spot $\mathfrak p$. Variant of 101:12 (the book's statement is about $\Omega_n$; see the module docstring). -/
@[kb "omeara1963" "§101B, 101:12, p. 294 (variant: the spinor kernel O' instead of Ω_n)"]
theorem mem_spinorKernel_iff_forall (hQ : Q.Nondegenerate) {σ : orthGroup Q F}
    (hσ : σ ∈ Tamagawa.soSub Q F) :
    σ ∈ spinorKernel Q F ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      orthMap Q (v.adicCompletion F) σ ∈ spinorKernel Q (v.adicCompletion F) :=
  ⟨fun h v => orthMap_mem_spinorKernel Q v h,
    fun h => (mem_spinorKernel_iff_eventually Q hQ hσ).mpr (Filter.Eventually.of_forall h)⟩

/-! ### The group $D = \theta(O^+(V))$ -/

/-- The quotient map $F^\times \to F^\times/F^{\times 2}$. -/
def sqClassHom (K : Type*) [Field K] : Kˣ →* SqClass K := QuotientGroup.mk' _

theorem sqClassHom_apply {K : Type*} [Field K] (a : Kˣ) : sqClassHom K a = SqClass.mk a := rfl

/-- **The group $D = \theta(O^+(V))$** (O'Meara 1973, §101D, p. 296): the subgroup of $F^\times$ of the $\alpha$ whose
square class $\alpha F^{\times 2}$ is the spinor norm of a rotation of the regular space $V$. -/
@[kb "omeara1963" "§101D, p. 296 (D = θ(O⁺(V)))"]
def spinorNormGroup (hQ : Q.Nondegenerate) : Subgroup Fˣ :=
  ((Tamagawa.soSub Q F).map (spinorNormHom Q F hQ)).comap (sqClassHom F)

theorem mem_spinorNormGroup (hQ : Q.Nondegenerate) {a : Fˣ} :
    a ∈ spinorNormGroup Q hQ ↔ ∃ σ ∈ Tamagawa.soSub Q F, spinorNorm Q F σ = SqClass.mk a := by
  simp [spinorNormGroup, sqClassHom_apply, spinorNormHom_apply]

/-- $F^{\times 2} \subseteq D$. -/
theorem sq_mem_spinorNormGroup (hQ : Q.Nondegenerate) (a : Fˣ) : a ^ 2 ∈ spinorNormGroup Q hQ := by
  rw [mem_spinorNormGroup]
  refine ⟨1, (Tamagawa.soSub Q F).one_mem, ?_⟩
  rw [← spinorNormHom_apply Q F hQ, map_one, eq_comm, SqClass.mk_eq_one_iff]
  exact ⟨a, rfl⟩

end QuadFormsKB.Lattices
