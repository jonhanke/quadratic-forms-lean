/-
# O'Meara §101C: Lemma 101:11 in every dimension

**Layer:** $F$ a number field, $V = F^n$ with a nondegenerate `Q : QuadForm F n`; completions $F_\mathfrak p$
(`v.adicCompletion F`, finite spots) and $F_w$ (`w.Completion`, infinite spots); `RegTernaryRepresents Q K X`
(`Sec101Named.lean`): some regular ternary subspace of $K^n$ represents every element of the finite set $X \subseteq F$.

**Proves**
* `regTernaryRepresents_complement_four` (the local step for $n = 4$): at a non-dyadic spot $\mathfrak p$, if
  $\langle u_0, u_1, u_2, u_3\rangle \cong \langle\gamma\rangle \perp \langle\alpha_0,\alpha_1,\alpha_2\rangle$ over $F$
  with all $u_i$ units at $\mathfrak p$, then $\langle\alpha\rangle$ represents every $\mathfrak p$-unit over
  $F_\mathfrak p$. Proof: by the local classification (63:20, `LocalClassNF.isometric_finite_iff`: same discriminant
  and Hasse invariant) $\langle u_0,u_1,u_2,u_3\rangle \cong \langle\gamma,-\gamma,-u_0u_1u_2,u_3\rangle$ over
  $F_\mathfrak p$; Witt cancellation (`QuadForm.isometricIn_of_diag_cons`) gives $\langle\alpha\rangle \cong
  \langle-\gamma,-u_0u_1u_2,u_3\rangle$, which represents every unit: if $\operatorname{ord}_\mathfrak p\gamma$ is odd
  because its determinant has odd order, otherwise because it is isotropic.
* `omeara101_11_four` (**Lemma 101:11 for $n = 4$**), `omeara101_11_succ` ($n \ge 4$, by induction on $n$), and
  `omeara101_11 : OMeara101_11 F` (**Lemma 101:11**, every $n$; unconditional).
* `omeara101_12 : OMeara101_12 F` (**Proposition 101:12**), `omeara101_r39 : OMeara101_r39 F`,
  `omeara101_r40 : OMeara101_r40 F`: unconditional, from the conditional theorems `omeara101_12_of_101_11`,
  `omeara101_r39_of_101_12`, `omeara101_r40_of_101_12`.

**The route.** O'Meara's proof (pp. 293–294) splits off a global $\langle\gamma\rangle$ with $\gamma$ approximating
local values $\gamma_\mathfrak p$ orthogonal to the given local ternary subspaces at a finite set $T$ of spots
(`exists_split_global`, `Sec101Eleven.lean`), and handles the spots outside $T$ by 63:21/63:24. Here $T$ consists of
the dyadic spots and the spots where an element of $X$ (and, for $n = 4$, a diagonal coefficient of $V$) is not a unit.
*Deviation from the book for $n \ge 5$:* instead of O'Meara's binary subspace $U$ and Theorem 66:3 for subspaces, the
proof inducts on $n$: the complement $\langle\alpha\rangle$ of $\langle\gamma\rangle$ (dimension $n - 1 \ge 4$) has the
local property at $\mathfrak p \in T$ and at the infinite spots by Witt's theorem, and outside $T$ by
`regTernaryRepresents_units_nondyadic` (`Sec101ElevenLocal.lean`); the induction ends at $n = 4$, which reduces in the
same way to $n = 3$ (`omeara101_11_of_le_three`, 66:3 for numbers).
-/
import QuadFormsKB.Literature.OMeara.Sec101Eleven
import QuadFormsKB.Literature.OMeara.Sec101Omega
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationNF
import QuadFormsKB.Tamagawa.SquareClassDuality

open NumberField IsDedekindDomain WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- The integer $k$ with $v(x) = e^{k}$ ($-\operatorname{ord}_v x$), as in `Sec101ElevenLocal.lean`. -/
local notation "ordv " v:max x:max => WithZero.log (IsDedekindDomain.HeightOneSpectrum.valuation _ v x)

variable {F : Type} [Field F] [NumberField F]

/-! ### The local step for $n = 4$ -/

section Four

variable (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)

local notation "Kv" => v.adicCompletion F

include h2 in
/-- **A unit quaternary space splits as $\langle\gamma,-\gamma,-u_0u_1u_2,u_3\rangle$** at a non-dyadic spot, for every
$\gamma \in F^\times$: both have the same discriminant and Hasse invariant $1$ (Hilbert symbols of units are $1$,
`SqDual.hilbert_units_nondyadic`, and $(\gamma,-\gamma) = 1$), so they are isometric over $F_v$ (63:20). -/
theorem isometricIn_units_four (u : Fin 4 → F) (hu : ∀ i, v.valuation F (u i) = 1) {γ : F} (hγ : γ ≠ 0) :
    (QuadForm.diag u).IsometricIn Kv (QuadForm.diag ![γ, -γ, -(u 0 * u 1 * u 2), u 3]) := by
  have hu0 : ∀ i, u i ≠ 0 := fun i h => by simpa [h] using hu i
  set c := -(u 0 * u 1 * u 2) with hc
  have hcv : v.valuation F c = 1 := by simp [hc, hu]
  have hc0 : c ≠ 0 := fun h => by simp [h] at hcv
  have hm1 : v.valuation F (-1 : F) = 1 := by rw [Valuation.map_neg, map_one]
  have hb0 : ∀ i, (![γ, -γ, c, u 3] : Fin 4 → F) i ≠ 0 := by
    intro i; fin_cases i <;> simp [hγ, hc0, hu0]
  have H := fun a b (ha : v.valuation F a = 1) (hb : v.valuation F b = 1) =>
    SqDual.hilbert_units_nondyadic v h2 a b ha hb
  rw [LocalClassNF.isometric_finite_iff v _ _ hu0 hb0]
  refine ⟨⟨algebraMap F Kv γ⁻¹, ?_⟩, ?_⟩
  · have e : (∏ i, u i) / ∏ i, (![γ, -γ, c, u 3] : Fin 4 → F) i = γ⁻¹ * γ⁻¹ := by
      have h0 := hu0 0; have h1 := hu0 1; have h2' := hu0 2; have h3 := hu0 3
      simp only [Fin.prod_univ_four, hc]
      simp
      field_simp
    rw [← map_mul, e]
  · simp only [NFPlace.hasseSerre, Fin.prod_univ_four]
    simp only [Fin.isValue, ↓reduceIte, lt_self_iff_false, mul_one, one_mul, Fin.lt_def]
    norm_num
    rw [H _ _ (hu 0) (hu 1), H _ _ (hu 0) (hu 2), H _ _ (hu 0) (hu 3), H _ _ (hu 1) (hu 2),
      H _ _ (hu 1) (hu 3), H _ _ (hu 2) (hu 3), H _ _ hcv (hu 3), NFPlace.hilbert_self_neg,
      show -γ = -1 * γ by ring, NFPlace.hilbert_mul_left _ (by norm_num) hγ hc0,
      NFPlace.hilbert_mul_left _ (by norm_num) hγ (hu0 3), H _ _ hm1 hcv, H _ _ hm1 (hu 3)]
    rcases NFPlace.hilbert_eq_one_or (NFPlace.finite v) γ c with h | h <;>
      rcases NFPlace.hilbert_eq_one_or (NFPlace.finite v) γ (u 3) with h' | h' <;>
      simp [h, h']

include h2 in
/-- **The local step of 101:11 for $n = 4$**: at a non-dyadic spot $v$, if $\langle u_0,u_1,u_2,u_3\rangle \cong
\langle\gamma\rangle \perp \langle\alpha\rangle$ over $F$ with all $u_i$ units at $v$, then $\langle\alpha\rangle$ (a
ternary space) represents over $F_v$ every element of $X$ whose non-zero elements are $v$-units. -/
@[kb "omeara1963" "§101C, proof of 101:11 (case n = 4), p. 293 (the spots outside T)"]
theorem regTernaryRepresents_complement_four (u : Fin 4 → F) (hu : ∀ i, v.valuation F (u i) = 1) {γ : F}
    (hγ : γ ≠ 0) {α : Fin 3 → F} (hα : ∀ i, α i ≠ 0)
    (hiso : (QuadForm.diag u).IsometricIn F (QuadForm.diag (Fin.cons γ α))) (X : Finset F)
    (hX : ∀ a ∈ X, a ≠ 0 → v.valuation F a = 1) :
    RegTernaryRepresents (QuadForm.diag α) Kv X := by
  have hu0 : ∀ i, u i ≠ 0 := fun i h => by simpa [h] using hu i
  set c := -(u 0 * u 1 * u 2) with hc
  have hcv : v.valuation F c = 1 := by simp [hc, hu]
  have hc0 : c ≠ 0 := fun h => by simp [h] at hcv
  set β : Fin 3 → F := ![-γ, c, u 3] with hβ
  have hβ0 : ∀ i, β i ≠ 0 := by
    intro i; fin_cases i <;> simp [β, hγ, hc0, hu0]
  have h1 : (QuadForm.diag (Fin.cons γ α : Fin 4 → F)).IsometricIn Kv
      (QuadForm.diag (Fin.cons γ β : Fin 4 → F)) :=
    QuadForm.isometricIn_trans _ (QuadForm.isometricIn_symm _ (FieldGen.isometricIn_of_base _ hiso))
      (isometricIn_units_four v h2 u hu hγ)
  have h3 := QuadForm.isometricIn_of_diag_cons Kv hγ hα h1
  rw [regTernaryRepresents_iff_of_isometricIn Kv h3]
  refine regTernaryRepresents_of_coordinates β hβ0 X id Function.injective_id fun a ha => ?_
  rw [Function.comp_id]
  by_cases ha0 : a = 0
  · subst ha0
    exact ⟨0, by simp [QuadForm.evalIn_diag]⟩
  have hord0 : ordv v c = 0 := by rw [hcv]; rfl
  have hord3 : ordv v (u 3) = 0 := by rw [hu 3]; rfl
  have hordγ : ordv v (-γ) = ordv v γ := by rw [Valuation.map_neg]
  by_cases hev : Even (ordv v γ)
  · refine represents_of_even v h2 β hβ0 (fun i => ?_) a
    fin_cases i
    · simpa [β, hordγ] using hev
    · simp [β, hord0]
    · simp [β, hord3]
  · refine represents_unit_of_odd v β hβ0 ?_ (hX a ha ha0)
    simpa [β, hordγ, hord0, hord3] using hev

end Four

/-! ### Lemma 101:11 -/

/-- The spots outside the finite set `(finite_bad Y).toFinset` are non-dyadic and make every non-zero element of $Y$
a unit. -/
theorem good_of_notMem_bad {Y : Finset F} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ (finite_bad Y).toFinset) :
    (2 : 𝓞 F) ∉ v.asIdeal ∧ ∀ y ∈ Y, y ≠ 0 → v.valuation F y = 1 := by
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  exact ⟨two_notMem_of_valuation hv.1, hv.2⟩

/-- **Lemma 101:11 for $n = 4$** (O'Meara 1973, §101C, p. 293): for a regular quaternary $V$ over the number field
$F$ and a finite $X \subseteq F$, if at every spot some regular ternary subspace of the localization represents all of
$X$, so does one of $V$. Proof (O'Meara's): diagonalize $V \cong \langle u_0,\dots,u_3\rangle$; let $T$ be the dyadic
spots and the spots where some $u_i$ or some non-zero element of $X$ is not a unit; split $V \cong \langle\gamma\rangle
\perp W$ with $W$ having the local property at $T$ and at the infinite spots (`exists_split_global`, weak approximation
and Witt's theorem) and outside $T$ (`regTernaryRepresents_complement_four`); then $W$ (ternary) represents $X$
(`omeara101_11_of_le_three`, 66:3). Unconditional. -/
@[kb "omeara1963" "§101C, 101:11, p. 293 (the case n = 4)"]
theorem omeara101_11_four (Q : QuadForm F 4) (hQ : Q.Nondegenerate) (X : Finset F)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), RegTernaryRepresents Q (v.adicCompletion F) X)
    (hw : ∀ w : InfinitePlace F, RegTernaryRepresents Q w.Completion X) :
    RegTernaryRepresents Q F X := by
  classical
  obtain ⟨u, hu0, hQu⟩ := FieldGen.exists_isometric_diag Q hQ
  rw [regTernaryRepresents_iff_of_isometricIn F hQu]
  have hvu : ∀ v : HeightOneSpectrum (𝓞 F), RegTernaryRepresents (QuadForm.diag u) (v.adicCompletion F) X :=
    fun v => (regTernaryRepresents_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hQu) X).mp (hv v)
  have hwu : ∀ w : InfinitePlace F, RegTernaryRepresents (QuadForm.diag u) w.Completion X :=
    fun w => (regTernaryRepresents_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hQu) X).mp (hw w)
  set Y : Finset F := X ∪ Finset.univ.image u with hY
  obtain ⟨γ, hγ, α, hα, hiso, hT, hW⟩ := exists_split_global (m := 3) (QuadForm.diag u)
    (QuadForm.nondegenerate_diag hu0) le_rfl X (finite_bad Y).toFinset (fun v _ => hvu v) hwu
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), RegTernaryRepresents (QuadForm.diag α) (v.adicCompletion F) X := by
    intro v
    by_cases hvT : v ∈ (finite_bad Y).toFinset
    · exact hT v hvT
    · obtain ⟨h2, hgood⟩ := good_of_notMem_bad hvT
      exact regTernaryRepresents_complement_four v h2 u
        (fun i => hgood _ (by simp [hY]) (hu0 i)) hγ hα hiso X
        (fun a ha ha0 => hgood a (by simp [hY, ha]) ha0)
  have h3 := omeara101_11_of_le_three (QuadForm.diag α) (QuadForm.nondegenerate_diag hα) le_rfl X hall hW
  exact (regTernaryRepresents_iff_of_isometricIn F hiso X).mpr (regTernaryRepresents_cons F γ α X h3)

/-- **Lemma 101:11 for $n \ge 4$** ($n = m + 1$, $m \ge 3$), by induction on $n$ from `omeara101_11_four`: split
$V \cong \langle\gamma\rangle \perp W$ (`exists_split_global`, with $T$ the dyadic spots and the spots where a non-zero
element of $X$ is not a unit); $W$ has the local property at $T$ and the infinite spots by Witt's theorem and outside
$T$ by `regTernaryRepresents_units_nondyadic` ($\dim W \ge 4$); by induction $W$, hence $V$, has a regular ternary
subspace representing $X$. *Deviation from the book* (which uses a binary subspace and 66:3 for subspaces when
$n \ge 5$): recorded in the module docstring. Unconditional. -/
@[kb "omeara1963" "§101C, 101:11, pp. 293–294 (the case n ≥ 4)"]
theorem omeara101_11_succ (m : ℕ) (hm : 3 ≤ m) (Q : QuadForm F (m + 1)) (hQ : Q.Nondegenerate) (X : Finset F)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), RegTernaryRepresents Q (v.adicCompletion F) X)
    (hw : ∀ w : InfinitePlace F, RegTernaryRepresents Q w.Completion X) :
    RegTernaryRepresents Q F X := by
  classical
  induction m, hm using Nat.le_induction generalizing X with
  | base => exact omeara101_11_four Q hQ X hv hw
  | succ m hm ih =>
    obtain ⟨γ, hγ, α, hα, hiso, hT, hW⟩ := exists_split_global (m := m + 1) Q hQ (by omega) X
      (finite_bad X).toFinset (fun v _ => hv v) hw
    have hall : ∀ v : HeightOneSpectrum (𝓞 F),
        RegTernaryRepresents (QuadForm.diag α) (v.adicCompletion F) X := by
      intro v
      by_cases hvT : v ∈ (finite_bad X).toFinset
      · exact hT v hvT
      · obtain ⟨h2, hgood⟩ := good_of_notMem_bad hvT
        exact regTernaryRepresents_units_nondyadic v h2 (by omega) α hα X hgood
    exact (regTernaryRepresents_iff_of_isometricIn F hiso X).mpr
      (regTernaryRepresents_cons F γ α X (ih _ (QuadForm.nondegenerate_diag hα) X hall hW))

/-- **Lemma 101:11** (O'Meara 1973, §101C, pp. 293–294), PROVED: the named statement `OMeara101_11` holds for every
number field $F$. Let $V$ be a regular space over $F$ and $X \subseteq F$ finite; if at every spot some regular ternary
subspace of the localization represents all of $X$, so does some regular ternary subspace of $V$. Cases: $n \le 3$
(`omeara101_11_of_le_three`), $n = 4$ (`omeara101_11_four`), $n \ge 5$ (`omeara101_11_succ`). Unconditional. -/
@[kb "omeara1963" "§101C, 101:11, pp. 293–294"]
theorem omeara101_11 : OMeara101_11 F := by
  refine ⟨fun n Q hQ X hv hw => ?_⟩
  rcases le_or_gt n 3 with h | h
  · exact omeara101_11_of_le_three Q hQ h X hv hw
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact omeara101_11_succ m (by omega) Q hQ X hv hw

/-- **Proposition 101:12** (O'Meara 1973, §101C, p. 294), PROVED: $\sigma \in \Omega_n(V)$ iff $\sigma_\mathfrak p \in
\Omega_n(V_\mathfrak p)$ at every spot, for a regular space $V$ over the number field $F$ and $\sigma \in O^+(V)$
(`omeara101_12_of_101_11` with `omeara101_11`). Unconditional. -/
@[kb "omeara1963" "§101C, 101:12, p. 294"]
theorem omeara101_12 : OMeara101_12 F := omeara101_12_of_101_11 omeara101_11

/-- **101.r39** (O'Meara 1973, §101C, p. 295; $O'_n/\Omega_n \cong \prod_\mathfrak p O'_n(V_\mathfrak p)/\Omega_n(V_\mathfrak p)$), PROVED (`omeara101_r39_of_101_12` with `omeara101_12`).
Unconditional. -/
@[kb "omeara1963" "§101C, p. 295 (O'_n/Ω_n ≅ ∏_𝔭 O'_n(V_𝔭)/Ω_n(V_𝔭))"]
theorem omeara101_r39 : OMeara101_r39 F := omeara101_r39_of_101_12 omeara101_12

/-- **101.r40** (O'Meara 1973, §101C, p. 295; $O'_n = \Omega_n$ for $n \ne 4$, $O'_4/\Omega_4$ a finite product of groups of order $2$), PROVED (`omeara101_r40_of_101_12` with `omeara101_12`).
Unconditional. -/
@[kb "omeara1963" "§101C, p. 295 (O'_n = Ω_n for n ≠ 4; O'_4/Ω_4 a finite product of groups of order 2)"]
theorem omeara101_r40 : OMeara101_r40 F := omeara101_r40_of_101_12 omeara101_12

/-- **101.r38** (O'Meara 1973, §101C, p. 295), unconditional: for a regular $V$ over the number field $F$,
$-1_V \in \Omega_n(V)$ if and only if $-1_V \in \Omega_n(V_\mathfrak p)$ at every spot (`neg_one_mem_commutator_iff`
with `omeara101_12`); so $\Omega_n \cap Z_n = \{\pm 1_V\}$ or $\{1_V\}$ accordingly. -/
@[kb "omeara1963" "§101C, p. 295 (Ω_n ∩ Z_n = {±1_V} or {1_V})"]
theorem neg_one_mem_commutator_iff_holds {n : ℕ} (Q : QuadForm F n) (hQ : Q.Nondegenerate) :
    negOne Q F ∈ commutator (orthGroup Q F) ↔
      (∀ v : HeightOneSpectrum (𝓞 F),
        negOne Q (v.adicCompletion F) ∈ commutator (orthGroup Q (v.adicCompletion F))) ∧
      ∀ w : InfinitePlace F, negOne Q w.Completion ∈ commutator (orthGroup Q w.Completion) :=
  neg_one_mem_commutator_iff omeara101_12 Q hQ

end QuadFormsKB.Lattices
