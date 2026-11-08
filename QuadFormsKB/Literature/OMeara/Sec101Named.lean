/-
# O'Meara §101B–§101C: named statements 101:10, 101:11, 101:12 (for $\Omega_n$) and the groups of §101C

**Layer:** $F$ a number field, $V = F^n$ with a nondegenerate `Q : QuadForm F n`; $O(V)$ = `orthGroup Q F`,
$O^+(V)$ = `Tamagawa.soSub Q F`, $O'(V)$ = `spinorKernel Q F`, $\Omega_n(V)$ = the commutator subgroup
`commutator (orthGroup Q F)` (O'Meara §43); the same notation over the completions $F_\mathfrak p$ at the finite spots
(`v.adicCompletion F`) and $F_w$ at the infinite spots (`w.Completion`); localization `orthMap`. O'Meara's spots are
all spots of $F$, finite and infinite; both kinds appear explicitly below.

**Defines** (named statements: Prop-valued structures stating the book's results; they are not assumed anywhere
as axioms; all of them are now proved, see below)
* `OMeara101_10` (Example 101:10, pp. 292–293): for even $n \ge 2$ some lattice $K$ has $\operatorname{cls}^+K \ne
  \operatorname{cls}K$. Proved in `Sec101Ten.lean` (`omeara101_10`) by O'Meara's construction from 65:20, 81:14 and
  the local lattices of Example 92:8.
* `OMeara101_11` (Lemma 101:11, pp. 293–294): regular ternary subspaces representing a finite set, local–global.
  PROVED in `Sec101ElevenMain.lean` (`omeara101_11`).
* `OMeara101_12` (Proposition 101:12, p. 294, the book's statement for $\Omega_n$; the library proves the version for
  $O'_n$, `mem_spinorKernel_iff_forall`, which is the first step of O'Meara's proof). PROVED in `Sec101ElevenMain.lean`
  (`omeara101_12`, from 101:11 by `omeara101_12_of_101_11`).
* `OMeara101_r39` (p. 295): $O'_n/\Omega_n \cong \prod_\mathfrak p O'_n(V_\mathfrak p)/\Omega_n(V_\mathfrak p)$, stated as
  "kernel and image" of the localization map; O'Meara deduces it from 101:9 and 101:12.
* `OMeara101_r40` (p. 295): $O'_n = \Omega_n$ for $n \ne 4$, and $O'_4/\Omega_4$ is a finite product of groups of
  order $2$.
Both follow from `OMeara101_12` (`omeara101_r39_of_101_12`, `omeara101_r40_of_101_12`, `Sec101Omega.lean`); the
field `image` of `OMeara101_r39` is proved unconditionally (`omeara101_r39_image`). Both are PROVED in
`Sec101ElevenMain.lean` (`omeara101_r39`, `omeara101_r40`).

**Proves**
* `negOne` ($-1_V \in O(V)$) and 101.r38 (p. 295, from 101:12): $\Omega_n \cap Z_n = \{\pm 1_V\}$ if $-1_V \in
  \Omega_n(V_\mathfrak p)$ at every spot, and $\{1_V\}$ otherwise (`neg_one_mem_commutator_iff`, conditional on the
  named statement `OMeara101_12`; $Z_n = \{\pm 1_V\}$ is the centre of $O_n(V)$).
-/
import QuadFormsKB.Literature.OMeara.Sec101B
import QuadFormsKB.Literature.OMeara.Sec102

open NumberField IsDedekindDomain
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- The completion at an infinite place has characteristic $0$ (needed for the spinor kernel $O'(V_w)$). -/
instance charZero_completion (w : InfinitePlace F) : CharZero w.Completion :=
  charZero_of_injective_algebraMap (algebraMap F w.Completion).injective

/-! ### Regular ternary subspaces -/

/-- **Some regular ternary subspace of $V_K = K^n$ represents every element of $X$** (the condition of Lemma 101:11):
there is a $K$-subspace $W$ of dimension $3$ on which the bilinear form of $Q$ is nondegenerate (`x ⬝ᵥ H y`, $H$ the
Hessian; nondegeneracy does not depend on the factor $2$ between it and O'Meara's $B$), such that every $a \in X$ is
$Q(x)$ for some $x \in W$. -/
def RegTernaryRepresents (Q : QuadForm F n) (K : Type*) [Field K] [Algebra F K] (X : Finset F) : Prop :=
  ∃ W : Submodule K (Fin n → K), Module.finrank K W = 3 ∧
    (∀ x ∈ W, (∀ y ∈ W, x ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ y) = 0) → x = 0) ∧
    ∀ a ∈ X, ∃ x ∈ W, Q.evalIn K x = algebraMap F K a

/-! ### Named statements -/

/-- **Example 101:10 — named statement** (O'Meara 1973, §101B, pp. 292–293). Let $V$ be a regular $n$-ary space over
the number field $F$ with $n$ even ($n \ge 2$; O'Meara's $V$ is non-zero). Then there is a lattice $K$ on $V$ with
$\operatorname{cls}^+K \ne \operatorname{cls}K$: some lattice isometric to $K$ is not properly isometric to it.
(For odd $n$, and over local fields, $\operatorname{cls}^+ = \operatorname{cls}$: Example 82:4, Corollary 91:4a.)
O'Meara's proof chooses two spots $\mathfrak q, \mathfrak q'$ by Proposition 65:20 and local lattices with prescribed
spinor norms there (Example 92:8), glued by 81:14. PROVED in `Sec101Ten.lean` (`omeara101_10 : OMeara101_10 F`),
following the book. -/
@[kb "omeara1963" "§101B, 101:10, pp. 292–293"]
structure OMeara101_10 (F : Type) [Field F] [NumberField F] : Prop where
  /-- For even $n \ge 2$ some lattice has $\operatorname{cls}^+K \ne \operatorname{cls}K$. -/
  holds : ∀ (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate → 2 ≤ n → Even n →
    ∃ K M : Lat F n, IsIsometric Q K.1 M.1 ∧ ¬ IsProperIsometric Q K.1 M.1

/-- **Lemma 101:11 — named statement** (O'Meara 1973, §101C, pp. 293–294). Let $V$ be a regular space over the number
field $F$ and $X \subseteq F$ finite. If at every spot (finite and infinite) some regular ternary subspace of the
localization of $V$ represents all of $X$, then some regular ternary subspace of $V$ represents all of $X$.
O'Meara's proof (cases $n = 3$, $n = 4$, $n \ge 5$) uses Theorem 66:3 for representations of spaces by spaces, 63:18,
63:21, 63:24 and Witt's theorem. PROVED in `Sec101ElevenMain.lean` (`omeara101_11 : OMeara101_11 F`, unconditional),
following O'Meara's splitting $V \cong \langle\gamma\rangle \perp W$; for $n \ge 5$ by induction on $n$ instead of 66:3
for spaces. -/
@[kb "omeara1963" "§101C, 101:11, pp. 293–294"]
structure OMeara101_11 (F : Type) [Field F] [NumberField F] : Prop where
  /-- Local–global principle for regular ternary subspaces representing a finite set. -/
  holds : ∀ (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate → ∀ X : Finset F,
    (∀ v : HeightOneSpectrum (𝓞 F), RegTernaryRepresents Q (v.adicCompletion F) X) →
    (∀ w : InfinitePlace F, RegTernaryRepresents Q w.Completion X) →
    RegTernaryRepresents Q F X

/-- **Proposition 101:12 — named statement** (O'Meara 1973, §101C, p. 294), the book's statement for $\Omega_n$: for a
regular $V$ over the number field $F$ and $\sigma \in O^+(V)$, $\sigma \in \Omega_n(V)$ if and only if $\sigma_\mathfrak p
\in \Omega_n(V_\mathfrak p)$ at every spot $\mathfrak p$ (finite and infinite). The library proves the analogue for the
spinor kernel $O'_n$ (`mem_spinorKernel_iff_forall`, `Sec101B.lean`), which is the book's statement when $n \le 3$;
the case $n \ge 4$ uses Proposition 95:2, Lemma 101:11 and Proposition 55:3. The book's statement for $n \le 3$ is
proved in `Sec101Twelve.lean` (`omeara101_12_of_le_three`); in general it is PROVED in `Sec101ElevenMain.lean`
(`omeara101_12 : OMeara101_12 F`, unconditional). -/
@[kb "omeara1963" "§101C, 101:12, p. 294"]
structure OMeara101_12 (F : Type) [Field F] [NumberField F] : Prop where
  /-- $\sigma \in \Omega_n(V)$ iff $\sigma_\mathfrak p \in \Omega_n(V_\mathfrak p)$ at every spot. -/
  holds : ∀ (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate → ∀ σ ∈ Tamagawa.soSub Q F,
    σ ∈ commutator (orthGroup Q F) ↔
      (∀ v : HeightOneSpectrum (𝓞 F),
        orthMap Q (v.adicCompletion F) σ ∈ commutator (orthGroup Q (v.adicCompletion F))) ∧
      ∀ w : InfinitePlace F, orthMap Q w.Completion σ ∈ commutator (orthGroup Q w.Completion)

/-- **The isomorphism $O'_n/\Omega_n \cong \prod_\mathfrak p O'_n(V_\mathfrak p)/\Omega_n(V_\mathfrak p)$ — named
statement** (O'Meara 1973, §101C, p. 295, "this follows easily from Propositions 101:9 and 101:12"). It is stated as the
two facts that make the localization map $\sigma \mapsto (\sigma_\mathfrak p\,\Omega_n(V_\mathfrak p))_\mathfrak p$ an
isomorphism of $O'_n(V)/\Omega_n(V)$ onto the product (only finitely many factors are non-trivial):
* (kernel) for $\sigma \in O'(V)$: $\sigma \in \Omega_n(V)$ iff $\sigma_\mathfrak p \in \Omega_n(V_\mathfrak p)$ at every spot;
* (image) for every family $\varphi_\mathfrak p \in O'(V_\mathfrak p)$, with $\varphi_\mathfrak p \in \Omega_n(V_\mathfrak p)$
  at almost all finite spots, there is $\sigma \in O'(V)$ with $\sigma_\mathfrak p \in \varphi_\mathfrak p\,
  \Omega_n(V_\mathfrak p)$ at every spot.

PROVED in `Sec101ElevenMain.lean` (`omeara101_r39 : OMeara101_r39 F`, unconditional). -/
@[kb "omeara1963" "§101C, p. 295 (O'_n/Ω_n ≅ ∏_𝔭 O'_n(V_𝔭)/Ω_n(V_𝔭))"]
structure OMeara101_r39 (F : Type) [Field F] [NumberField F] : Prop where
  /-- The kernel of the localization map on $O'(V)$ is $\Omega_n(V)$. -/
  ker : ∀ (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate → ∀ σ ∈ spinorKernel Q F,
    σ ∈ commutator (orthGroup Q F) ↔
      (∀ v : HeightOneSpectrum (𝓞 F),
        orthMap Q (v.adicCompletion F) σ ∈ commutator (orthGroup Q (v.adicCompletion F))) ∧
      ∀ w : InfinitePlace F, orthMap Q w.Completion σ ∈ commutator (orthGroup Q w.Completion)
  /-- The localization map is onto the restricted product of the local quotients. -/
  image : ∀ (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate →
    ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F))
      (ψ : ∀ w : InfinitePlace F, orthGroup Q w.Completion),
    (∀ v, φ v ∈ spinorKernel Q (v.adicCompletion F)) → (∀ w, ψ w ∈ spinorKernel Q w.Completion) →
    (∀ᶠ v in Filter.cofinite, φ v ∈ commutator (orthGroup Q (v.adicCompletion F))) →
    ∃ σ ∈ spinorKernel Q F,
      (∀ v, (φ v)⁻¹ * orthMap Q (v.adicCompletion F) σ ∈ commutator (orthGroup Q (v.adicCompletion F))) ∧
      ∀ w, (ψ w)⁻¹ * orthMap Q w.Completion σ ∈ commutator (orthGroup Q w.Completion)

/-- **$O'_n = \Omega_n$ for $n \ne 4$; $O'_4/\Omega_4$ is a finite product of groups of order $2$ — named statement**
(O'Meara 1973, §101C, p. 295, from 101:9, 101:12 and the local results of §95). The second part is stated as: every
$\sigma \in O'_4(V)$ has $\sigma^2 \in \Omega_4(V)$ (so the quotient is an elementary abelian $2$-group, i.e. a direct
product of groups of order $2$), and finitely many cosets of $\Omega_4(V)$ cover $O'_4(V)$. PROVED in
`Sec101ElevenMain.lean` (`omeara101_r40 : OMeara101_r40 F`, unconditional). -/
@[kb "omeara1963" "§101C, p. 295 (O'_n = Ω_n for n ≠ 4; O'_4/Ω_4 a finite product of groups of order 2)"]
structure OMeara101_r40 (F : Type) [Field F] [NumberField F] : Prop where
  /-- $O'_n(V) \subseteq \Omega_n(V)$ for $n \ne 4$ (the reverse inclusion always holds). -/
  ne_four : ∀ (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate → n ≠ 4 →
    spinorKernel Q F ≤ commutator (orthGroup Q F)
  /-- $O'_4/\Omega_4$ has exponent $2$ and is finite. -/
  four : ∀ (Q : QuadForm F 4), Q.Nondegenerate →
    (∀ σ ∈ spinorKernel Q F, σ ^ 2 ∈ commutator (orthGroup Q F)) ∧
    ∃ S : Finset (orthGroup Q F), ∀ σ ∈ spinorKernel Q F, ∃ s ∈ S, s⁻¹ * σ ∈ commutator (orthGroup Q F)

/-! ### 101.r38 from 101:12 -/

/-- $-1_V \in O(V)$ over any $F$-algebra $R$. -/
def negOne (Q : QuadForm F n) (R : Type*) [CommRing R] [Algebra F R] : orthGroup Q R :=
  ⟨-1, by rw [mem_orthGroup]; simp⟩

theorem orthMap_negOne (Q : QuadForm F n) (R : Type*) [CommRing R] [Algebra F R] :
    orthMap Q R (negOne Q F) = negOne Q R := by
  ext i j
  simp only [negOne, orthMap_val]
  by_cases h : i = j <;> simp [h]

/-- Commutators have determinant $1$: $\Omega_n \le O^+_n$. -/
theorem commutator_le_soSub (Q : QuadForm F n) (R : Type*) [CommRing R] [Algebra F R] :
    commutator (orthGroup Q R) ≤ Tamagawa.soSub Q R := by
  let d : orthGroup Q R →* Rˣ :=
    (Matrix.GeneralLinearGroup.det).comp (orthGroup Q R).subtype
  have hk : Tamagawa.soSub Q R = d.ker := by
    ext g
    simp only [Tamagawa.mem_soSub, MonoidHom.mem_ker, d, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [Units.ext_iff]
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  rw [hk]
  exact Abelianization.commutator_subset_ker d

theorem negOne_mem_soSub_iff (Q : QuadForm F n) (K : Type*) [Field K] [Algebra F K] :
    negOne Q K ∈ Tamagawa.soSub Q K ↔ Even n := by
  have two_ne_zero : (2 : K) ≠ 0 := by
    have := (map_ne_zero (algebraMap F K)).mpr (two_ne_zero (α := F))
    rwa [map_ofNat] at this
  rw [Tamagawa.mem_soSub]
  change (-1 : Matrix (Fin n) (Fin n) K).det = 1 ↔ _
  rw [Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => h.neg_one_pow⟩
  by_contra ho
  rw [Nat.not_even_iff_odd] at ho
  rw [ho.neg_one_pow] at h
  have : (2 : K) = 0 := by linear_combination -h
  exact two_ne_zero this

/-- **101.r38** (O'Meara 1973, §101C, p. 295), from Proposition 101:12 (the named statement `OMeara101_12`): for a
regular $V$ over the number field $F$, $-1_V \in \Omega_n(V)$ if and only if $-1_V \in \Omega_n(V_\mathfrak p)$ at every
spot $\mathfrak p$. Since the centre of $O_n(V)$ is $Z_n = \{\pm 1_V\}$, this is O'Meara's
$\Omega_n \cap Z_n = \{\pm 1_V\}$ if $-1_V \in \Omega_n(V_\mathfrak p)$ at every spot, and $\{1_V\}$ otherwise.
(For odd $n$ both sides are false: $\det(-1_V) = -1$.) -/
@[kb "omeara1963" "§101C, p. 295 (Ω_n ∩ Z_n = {±1_V} or {1_V})"]
theorem neg_one_mem_commutator_iff (h12 : OMeara101_12 F) (Q : QuadForm F n) (hQ : Q.Nondegenerate) :
    negOne Q F ∈ commutator (orthGroup Q F) ↔
      (∀ v : HeightOneSpectrum (𝓞 F),
        negOne Q (v.adicCompletion F) ∈ commutator (orthGroup Q (v.adicCompletion F))) ∧
      ∀ w : InfinitePlace F, negOne Q w.Completion ∈ commutator (orthGroup Q w.Completion) := by
  by_cases hn : Even n
  · have hs : negOne Q F ∈ Tamagawa.soSub Q F := (negOne_mem_soSub_iff Q F).mpr hn
    rw [h12.holds n Q hQ _ hs]
    simp only [orthMap_negOne]
  · constructor
    · intro h
      exact absurd ((negOne_mem_soSub_iff Q F).mp (commutator_le_soSub Q F h)) hn
    · rintro ⟨-, hw⟩
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
      exact absurd ((negOne_mem_soSub_iff Q w.Completion).mp (commutator_le_soSub Q _ (hw w))) hn

end QuadFormsKB.Lattices
