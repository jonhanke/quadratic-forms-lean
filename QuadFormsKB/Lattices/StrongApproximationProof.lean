/-
# Strong approximation for rotations: what is proved

**Layer:** lattices in $(V, Q) = (F^n, Q)$ over a number field $F$, the spinor kernels $O'(V)$, $O'(V_{\mathbb A_f})$
(`Lattices/SpinorKernel.lean`) and the named input `StrongApproximationSpin F` (`Lattices/StrongApproximation.lean`,
frozen interface).

**Defines** `SpinApprox Q` (the conclusion of the field `approx` of `StrongApproximationSpin` for one form $Q$:
$O'(V_{\mathbb A_f}) \subseteq O'(V)\,O(\hat L)$ for every lattice $L$) and the two named inputs for the remaining case,
`VecStrongApproximation F` (O'Meara 104:3 for $F$-anisotropic forms) and `QuaternarySpinorInput F` (O'Meara 95:1,
101:9).

**Proves** (all axiom-clean), following O'Meara 1973, §104 (printed pp. 311–319 = PDF pp. 319–327):
* `spinApprox_of_isotropic`: **strong approximation for rotations of an isotropic space**, unconditional: $Q$
  nondegenerate and isotropic over $F$, $n \ge 3$ (104:3 isotropic case `Lattices/SAVectorsIsotropic.lean`; 104:4 step 1
  `Lattices/SARotations.lean`, step 2 `Lattices/SATernary.lean`; the 104:5 bridge `approx_of_rotApprox`);
* `spinApprox_of_five_le`: unconditional for $n \ge 5$ and $Q$ isotropic at every infinite place (then $Q$ is
  isotropic over $F$, `isotropicIn_of_five_le`);
* unconditional versions of Eichler's theorem and of class number one in these cases:
  `eichler_spinorGenus_eq_class'`, `latSpinorGenus_eq_class'`, `classesEquivSpinorGenera'`, `isIsometric_of_sameGenus'`;
* `strongApproximationSpin_of_inputs`: **`StrongApproximationSpin F` from the two named inputs** (both needed only for
  $F$-anisotropic $Q$), and `eichler_spinorGenus_eq_class_of_inputs`.
-/
import QuadFormsKB.Lattices.SATernary
import QuadFormsKB.Lattices.Eichler
import QuadFormsKB.Lattices.SpinorGlobal

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **The strong approximation property for one form** $Q$ (the conclusion of the field `approx` of the input
`StrongApproximationSpin`): for every lattice $L$ in $V = F^n$ and every $h \in O'(V_{\mathbb A_f})$ there is
$\gamma \in O'(V)$ with $\gamma^{-1}h \in O(\hat L)$, i.e. $O'(V_{\mathbb A_f}) \subseteq O'(V)\,O(\hat L)$. -/
def SpinApprox : Prop :=
  ∀ (L : Lat F n) (h : OAf Q), h ∈ spinorKernelAf Q →
    ∃ γ : orthGroup Q F, γ ∈ spinorKernel Q F ∧ (diagF Q γ)⁻¹ * h ∈ locStab Q L

theorem spinApprox_of_rotApprox (hR : RotApprox Q) : SpinApprox Q := approx_of_rotApprox Q hR

/-- **The input from the per-form property:** `SpinApprox` for every nondegenerate indefinite form in $n \ge 3$
variables is exactly `StrongApproximationSpin F`. -/
theorem strongApproximationSpin_of_spinApprox
    (h : ∀ {n : ℕ} (Q : QuadForm F n), 3 ≤ n → Q.Nondegenerate → IsIndefinite Q → SpinApprox Q) :
    StrongApproximationSpin F :=
  ⟨fun Q hn hQ hind L k hk => h Q hn hQ hind L k hk⟩

/-- An isotropic vector over $F$ stays isotropic over every completion. -/
theorem isotropicIn_completion {Q : QuadForm F n} (hiso : Q.IsotropicIn F) (v : HeightOneSpectrum (𝓞 F)) :
    Q.IsotropicIn (v.adicCompletion F) := by
  obtain ⟨x, hx0, hx⟩ := hiso
  refine ⟨locVec v x, fun h => hx0 (funext fun i => ?_), ?_⟩
  · have := congrFun h i
    rw [locVec_apply, Pi.zero_apply] at this
    exact (map_eq_zero_iff _ (algebraMap F (v.adicCompletion F)).injective).mp this
  · rw [evalIn_locVec]; simpa using hx

/-- **Strong approximation for rotations of an isotropic space** (O'Meara 1973, 104:4 for $n \ge 4$, with 104:3 in
the isotropic case): if $Q$ is nondegenerate and isotropic over $F$ and $n \ge 4$, then $O'(V)$ is dense in
$O'(V_{\mathbb A_f})$ in the sense of `RotApprox`. -/
theorem rotApprox_of_isotropic (hn : 4 ≤ n) (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn F) : RotApprox Q :=
  rotApprox_of_vecApprox Q hQ (by omega) (vecApprox_of_isotropic Q hn hQ hiso) (isotropicIn_completion hiso)

/-- **Strong approximation for rotations, isotropic case:** for $Q$ nondegenerate and isotropic over $F$ in $n \ge 3$
variables, $O'(V_{\mathbb A_f}) \subseteq O'(V)\,O(\hat L)$ for every lattice $L$ (O'Meara 1973, 104:3–104:5: step 1 of
104:4 for $n \ge 4$, step 2 via quaternions for $n = 3$; unconditional). -/
@[kb "omeara1963" "§104, 104:3, 104:4, pp. 311–319 (isotropic case)"]
theorem spinApprox_of_isotropic (hn : 3 ≤ n) (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn F) : SpinApprox Q := by
  rcases Nat.lt_or_ge n 4 with h3 | h4
  · obtain rfl : n = 3 := by omega
    exact spinApprox_of_rotApprox Q (rotApprox_ternary_isotropic hQ hiso)
  · exact spinApprox_of_rotApprox Q (rotApprox_of_isotropic Q h4 hQ hiso)

/-- **Isotropy from Hasse–Minkowski in $\ge 5$ variables:** a nondegenerate form in $n \ge 5$ variables that is
isotropic at every infinite place of $F$ is isotropic over $F$ (O'Meara 1973, 66:1, p. 187, with 63:19, p. 170; O'Meara's 66:2, p. 188, is the analogue over a function field). -/
theorem isotropicIn_of_five_le (hn : 5 ≤ n) (hQ : Q.Nondegenerate)
    (hinf : ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion) : Q.IsotropicIn F := by
  obtain ⟨b, hb, hP⟩ := FieldGen.exists_isometric_diag Q hQ
  rw [FieldGen.isotropicIn_iff_of_isometricIn F hP, hasseMinkowski_nf _ (QuadForm.nondegenerate_diag hb)]
  intro w
  cases w with
  | infinite w => exact (FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hP)).mp (hinf w)
  | finite v => exact isotropicIn_diag_finite hn b hb v

/-- **Strong approximation for rotations in $n \ge 5$ variables:** if $Q$ is nondegenerate in $n \ge 5$ variables and
isotropic at every infinite place (e.g. $F = \mathbb Q$ and $Q$ indefinite), then $O'(V_{\mathbb A_f}) \subseteq
O'(V)\,O(\hat L)$ (unconditional). -/
@[kb "omeara1963" "§104, 104:4, p. 315 (n ≥ 5, isotropic at infinity)"]
theorem spinApprox_of_five_le (hn : 5 ≤ n) (hQ : Q.Nondegenerate)
    (hinf : ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion) : SpinApprox Q :=
  spinApprox_of_isotropic Q (by omega) hQ (isotropicIn_of_five_le Q hn hQ hinf)

/-! ### Eichler's theorem, unconditionally in these cases -/

/-- **Eichler's theorem from `SpinApprox`:** two lattices in the same spinor genus are isometric. -/
theorem eichler_of_spinApprox (hA : SpinApprox Q) {L M : Lat F n} (h : SameSpinorGenus Q L M) :
    IsIsometric Q L.1 M.1 := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨σ, k, hk, rfl⟩ := (mem_latSpinorGenus Q).mp h
  obtain ⟨γ, -, hγ⟩ := hA L k hk
  have hkL : latSMul Q k L = latSMul Q (diagF Q γ) L := by
    have hs : ((diagF Q γ)⁻¹ * k) • L = L :=
      MulAction.mem_stabilizer_iff.mp ((stabilizer_eq_locStab Q L).symm ▸ hγ)
    calc latSMul Q k L = (diagF Q γ * ((diagF Q γ)⁻¹ * k)) • L := by rw [mul_inv_cancel_left]; rfl
      _ = latSMul Q (diagF Q γ) L := by rw [mul_smul, hs]; rfl
  refine ⟨((σ * γ : orthGroup Q F) : GL (Fin n) F), (σ * γ).2, ?_⟩
  rw [hkL, diagF_smul, diagF_smul, Lat.image, Lat.image, Subgroup.coe_mul, glImage_mul]

/-- **Eichler's theorem, unconditional for isotropic forms** (O'Meara 1973, 104:5): if $Q$ is nondegenerate and
isotropic over $F$ in $n \ge 3$ variables, or isotropic at every infinite place in $n \ge 5$ variables, then two
lattices in the same spinor genus are isometric. -/
@[kb "omeara1963" "§104, 104:5, p. 319 (isotropic case)"]
theorem eichler_spinorGenus_eq_class' (hQ : Q.Nondegenerate)
    (hcase : (3 ≤ n ∧ Q.IsotropicIn F) ∨ (5 ≤ n ∧ ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion))
    {L M : Lat F n} (h : SameSpinorGenus Q L M) : IsIsometric Q L.1 M.1 := by
  refine eichler_of_spinApprox Q ?_ h
  rcases hcase with ⟨hn, hiso⟩ | ⟨hn, hinf⟩
  · exact spinApprox_of_isotropic Q hn hQ hiso
  · exact spinApprox_of_five_le Q hn hQ hinf

/-- **$\mathrm{spn}(L) = \mathrm{cls}(L)$, unconditional** under the hypotheses of `eichler_spinorGenus_eq_class'`. -/
@[kb "omeara1963" "§104, 104:5, p. 319 (isotropic case); cassels1978 Ch. 11, Thm. 1.4, p. 202"]
theorem latSpinorGenus_eq_class' (hQ : Q.Nondegenerate)
    (hcase : (3 ≤ n ∧ Q.IsotropicIn F) ∨ (5 ≤ n ∧ ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion))
    (L : Lat F n) : latSpinorGenus Q L = {M : Lat F n | IsIsometric Q L.1 M.1} :=
  Set.Subset.antisymm (fun _ h => eichler_spinorGenus_eq_class' Q hQ hcase h) (class_subset_latSpinorGenus Q L)

/-- **Classes in the genus = spinor genera in the genus, unconditional** under the hypotheses of
`eichler_spinorGenus_eq_class'`. -/
@[kb "omeara1963" "§104, 104:5, p. 319 (isotropic case)"]
def classesEquivSpinorGenera' (hQ : Q.Nondegenerate)
    (hcase : (3 ≤ n ∧ Q.IsotropicIn F) ∨ (5 ≤ n ∧ ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion))
    (L : Lat F n) :
    @AWS.ClassesInGenus (OAf Q) (Lat F n) _ (latAction Q) (ratPoints Q) L ≃
      @AWS.ClassesInGenus (OAf Q) (Lat F n) _ (latAction Q) (spnGroup Q) L :=
  Quotient.congr (Equiv.refl _) fun M M' => by
    rw [classRel_iff, spinorRel_iff]
    exact ⟨fun h => IsIsometric.sameSpinorGenus Q h, fun h => eichler_spinorGenus_eq_class' Q hQ hcase h⟩

/-- **Class number one of the genus, unconditional for $n \ge 5$** (O'Meara 1973, 102:9 and 104:5): for $\mathcal O_F$ a
PID, $Q$ nondegenerate in $n \ge 5$ variables and isotropic at every infinite place, and `LocalSpinorUnits` at every
prime, every lattice in the genus of $L$ is isometric to $L$. -/
@[kb "omeara1963" "§102B, 102:9, p. 304; §104, 104:5, p. 319 (n ≥ 5); §104, 104:8, p. 320"]
theorem isIsometric_of_sameGenus' [IsPrincipalIdealRing (𝓞 F)] (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    (hinf : ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion) (L : Lat F n)
    (hloc : ∀ v, LocalSpinorUnits Q v L) {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    IsIsometric Q L.1 M.1 :=
  eichler_of_spinApprox Q (spinApprox_of_five_le Q hn hQ hinf)
    (sameSpinorGenus_of_sameGenus Q hQ (by omega) hinf L hloc hM)

/-! ### The general case from named inputs (O'Meara 104:3, 95:1, 101:9) -/

/-- **Input (O'Meara 1973, 104:3): strong approximation for vectors of a given norm** in the remaining case: for every
nondegenerate form $Q$ over $F$ in $n \ge 4$ variables that is indefinite (isotropic at some infinite place) and
**anisotropic over $F$**, `VecApprox Q` holds. (For $Q$ isotropic over $F$ this is proved, `vecApprox_of_isotropic`.)
O'Meara's proof (printed pp. 311–315 = PDF pp. 319–323) needs Lemma 104:1, i.e. the finiteness of the number of
classes in a genus over $F$ (103:4), which is formalized here only for totally definite genera (`Lattices/Finite.lean`).
Not equivalent to `StrongApproximationSpin`: it is a statement about vectors of one norm, and it is one of the two
ingredients of 104:4 (with the local and global spinor theory below). -/
@[kb "omeara1963" "§104, 104:3, pp. 311–315 (anisotropic case)"]
structure VecStrongApproximation (F : Type) [Field F] [NumberField F] : Prop where
  /-- `VecApprox Q` for nondegenerate, indefinite, $F$-anisotropic $Q$ in $n \ge 4$ variables. -/
  approx : ∀ {n : ℕ} (Q : QuadForm F n), 4 ≤ n → Q.Nondegenerate → IsIndefinite Q → ¬ Q.IsotropicIn F →
    VecApprox Q

/-- **Input (O'Meara 1973, 95:1 and 101:9): the spinor kernel versus $\Omega$ for quaternary spaces.**
* `index` (95:1, local): for a regular quaternary space over a local field, $(O'(V_\mathfrak p) : \Omega(V_\mathfrak p)) \le 2$
  ($\Omega$ = commutator subgroup; the index is $2$ exactly for anisotropic $V_\mathfrak p$ at non-dyadic $\mathfrak p$, and $1$
  otherwise);
* `global` (101:9): for a regular quaternary space $V$ over $F$ and a finite set $T$ of primes with
  $\Omega(V_\mathfrak p) \subsetneq O'(V_\mathfrak p)$ for $\mathfrak p \in T$, there is $\sigma \in O'(V)$ with $\sigma \notin \Omega(V_\mathfrak p)$ for
  $\mathfrak p \in T$ and $\sigma \in \Omega(V_\mathfrak p)$ at every other prime.
These are what O'Meara's step 1c of 104:4 (p. 316) uses for $n = 4$; neither is equivalent to strong approximation
(no integrality conditions). -/
@[kb "omeara1963" "§95, 95:1, p. 280; §101B, 101:9, p. 292"]
structure QuaternarySpinorInput (F : Type) [Field F] [NumberField F] : Prop where
  /-- 95:1: two elements of $O'(V_\mathfrak p) \setminus \Omega(V_\mathfrak p)$ have product in $\Omega(V_\mathfrak p)$. -/
  index : ∀ (Q : QuadForm F 4), Q.Nondegenerate → ∀ (v : HeightOneSpectrum (𝓞 F))
    (φ ψ : orthGroup Q (v.adicCompletion F)), φ ∈ spinorKernel Q (v.adicCompletion F) →
    ψ ∈ spinorKernel Q (v.adicCompletion F) → φ ∉ commutator (↥(orthGroup Q (v.adicCompletion F))) →
    ψ ∉ commutator (↥(orthGroup Q (v.adicCompletion F))) → φ * ψ ∈ commutator (↥(orthGroup Q (v.adicCompletion F)))
  /-- 101:9: global elements of $O'(V)$ with prescribed local classes modulo $\Omega$ at the exceptional primes. -/
  global : ∀ (Q : QuadForm F 4), Q.Nondegenerate → ∀ (T : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ v ∈ T, ∃ φ ∈ spinorKernel Q (v.adicCompletion F), φ ∉ commutator (↥(orthGroup Q (v.adicCompletion F)))) →
    ∃ σ ∈ spinorKernel Q F, (∀ v ∈ T, orthMap Q (v.adicCompletion F) σ ∉
        commutator (↥(orthGroup Q (v.adicCompletion F)))) ∧
      ∀ v ∉ T, orthMap Q (v.adicCompletion F) σ ∈ commutator (↥(orthGroup Q (v.adicCompletion F)))

/-- **Isotropy at the finite places in $\ge 5$ variables.** -/
@[kb "omeara1963" "§63C, 63:19, p. 170"]
theorem isotropicIn_completion_of_five_le (hn : 5 ≤ n) (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    Q.IsotropicIn (v.adicCompletion F) := by
  obtain ⟨b, hb, hP⟩ := FieldGen.exists_isometric_diag Q hQ
  rw [FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hP)]
  exact isotropicIn_diag_finite hn b hb v

theorem vecApprox_of_input (hV : VecStrongApproximation F) {Q : QuadForm F n} (hn : 4 ≤ n) (hQ : Q.Nondegenerate)
    (hind : IsIndefinite Q) : VecApprox Q := by
  by_cases hiso : Q.IsotropicIn F
  · exact vecApprox_of_isotropic Q hn hQ hiso
  · exact hV.approx Q hn hQ hind hiso

/-- An indefinite ternary form has an indefinite quaternary norm form. -/
theorem isIndefinite_nrdForm {Q : QuadForm F 3} {a b : F}
    (hI : ∀ (K : Type) [Field K] [Algebra F K] [CharZero K], Q.IsotropicIn K → (Quat.nrdForm a b).IsotropicIn K)
    (hind : IsIndefinite Q) : IsIndefinite (Quat.nrdForm a b) := by
  obtain ⟨w, hw⟩ := hind
  have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
  exact ⟨w, hI _ hw⟩

/-- **Strong approximation for rotations from the named inputs** (O'Meara 1973, 104:4 and 104:5): given
`VecStrongApproximation F` (104:3 for anisotropic forms) and `QuaternarySpinorInput F` (95:1, 101:9), the input
`StrongApproximationSpin F` holds. The isotropic case needs neither (`spinApprox_of_isotropic`). -/
@[kb "omeara1963" "§104, 104:4, 104:5, pp. 315–319"]
theorem strongApproximationSpin_of_inputs (hV : VecStrongApproximation F) (hQ4 : QuaternarySpinorInput F) :
    StrongApproximationSpin F := by
  refine strongApproximationSpin_of_spinApprox fun {n} Q hn hQ hind => spinApprox_of_rotApprox Q ?_
  rcases Nat.lt_or_ge n 4 with h3 | h4
  · -- `n = 3`: step 2 (quaternions)
    obtain rfl : n = 3 := by omega
    exact rotApprox_ternary_of hQ fun a b ha hb hI =>
      vecApprox_of_input hV le_rfl (Quat.nrdForm_nondegenerate two_ne_zero ha hb) (isIndefinite_nrdForm hI hind)
  rcases Nat.lt_or_ge n 5 with h4' | h5
  · -- `n = 4`: step 1c with the correction from 95:1 and 101:9
    obtain rfl : n = 4 := by omega
    refine rotApprox_of_vecApprox_of_correction Q hQ (by omega) (vecApprox_of_input hV h4 hQ hind) ?_
    classical
    intro T φ hφ
    set T₁ := T.filter fun v => φ v ∉ commutator (↥(orthGroup Q (v.adicCompletion F)))
    obtain ⟨σ, hσ, hσT₁, hσout⟩ := hQ4.global Q hQ T₁ fun v hv =>
      ⟨φ v, hφ v (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
    refine ⟨σ, hσ, fun v hv => ?_, fun v hv => hσout v fun h => hv (Finset.mem_filter.mp h).1⟩
    by_cases h1 : v ∈ T₁
    · exact hQ4.index Q hQ v _ _ (orthMap_mem_spinorKernel Q v hσ) (hφ v hv) (hσT₁ v h1)
        (Finset.mem_filter.mp h1).2
    · have hφΩ : φ v ∈ commutator (↥(orthGroup Q (v.adicCompletion F))) := by
        by_contra hc; exact h1 (Finset.mem_filter.mpr ⟨hv, hc⟩)
      exact Subgroup.mul_mem _ (hσout v h1) hφΩ
  · -- `n ≥ 5`: every `V_p` is isotropic, step 1
    exact rotApprox_of_vecApprox Q hQ (by omega) (vecApprox_of_input hV h4 hQ hind)
      (isotropicIn_completion_of_five_le Q h5 hQ)

/-- **Eichler's theorem from the named inputs** (O'Meara 104:5): for nondegenerate indefinite $Q$ in $n \ge 3$
variables, spinor genus = class, given `VecStrongApproximation F` and `QuaternarySpinorInput F`. -/
@[kb "omeara1963" "§104, 104:5, p. 319"]
theorem eichler_spinorGenus_eq_class_of_inputs (hV : VecStrongApproximation F) (hQ4 : QuaternarySpinorInput F)
    (hn : 3 ≤ n) (hQ : Q.Nondegenerate) (hind : IsIndefinite Q) {L M : Lat F n} (h : SameSpinorGenus Q L M) :
    IsIsometric Q L.1 M.1 :=
  eichler_spinorGenus_eq_class Q (strongApproximationSpin_of_inputs hV hQ4) hn hQ hind h

end QuadFormsKB.Lattices
