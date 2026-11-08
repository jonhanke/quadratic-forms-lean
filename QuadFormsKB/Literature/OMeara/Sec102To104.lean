/-
# O'Meara §102–§104: finiteness of the counting numbers, counting numbers, definite spots

**Layer:** $V = F^n$ over a number field $F$ with the form `Q : QuadForm F n`, lattices `Lat F n`, $S$ = all finite
spots (so "$S$ is indefinite for $V$" is `IsIndefinite Q`, "$S$ is definite" is `IsDefiniteSpots Q`).

**Defines** `countingNumber` ($N\alpha$, 103.r3) and `IsDefiniteSpots` (104.r1).

**Proves** (O'Meara 1973)
* 103.r2: the sets of classes / proper classes / spinor genera / proper spinor genera in a genus are finite;
* 103.r3–r4: $N\alpha = N(\alpha\mathfrak o)$, multiplicativity and the product formula $N\alpha = \prod_\mathfrak
  p\lvert\alpha\rvert_\mathfrak p^{-1}$;
* 104.r1: $S$ is definite iff $S$ is not indefinite.

*Deviation.* Only the finite spots are used (see `Sec102.lean`).
-/
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Literature.OMeara.Sec102Spn
import QuadFormsKB.Literature.OMeara.Sec104Indef
import QuadFormsKB.Lattices.ClassFinite
import QuadFormsKB.Literature.OMeara.Sec33A
import QuadFormsKB.Lattices.SpinorKernel
import QuadFormsKB.Literature.OMeara.Sec64
import QuadFormsKB.Literature.OMeara.Sec82
import QuadFormsKB.Literature.OMeara.Sec101B

open NumberField IsDedekindDomain Matrix
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### 104.r1: definite sets of spots -/

/-- **$S$ is a definite set of spots for $V$** (O'Meara 1973, §104, p. 311), for $S$ the set of all finite spots of
the number field $F$: $V_w$ is anisotropic at every infinite spot $w$ of $F$. -/
@[kb "omeara1963" "§104, p. 311 (definite set of spots)"]
def IsDefiniteSpots : Prop := ∀ w : InfinitePlace F, ¬ Q.IsotropicIn w.Completion

/-- **Definite versus indefinite** (O'Meara 1973, §104, p. 311): the set $S$ of all finite spots is definite for
$V$ if and only if it is not indefinite for $V$ (`IsIndefinite`: some infinite $V_w$ is isotropic). -/
@[kb "omeara1963" "§104, p. 311 (S definite iff not indefinite)"]
theorem isDefiniteSpots_iff_not_isIndefinite : IsDefiniteSpots Q ↔ ¬ IsIndefinite Q := by
  unfold IsDefiniteSpots IsIndefinite
  push Not
  exact Iff.rfl

/-! ### 103.r2: finiteness of the counting numbers -/

section Finiteness

/-- **The proper classes in a genus are finitely many** (O'Meara 1973, §103, p. 305, remark following 103:4): for
nondegenerate $Q$ on $F^n$ and every lattice $L$, $h^+(L)$ counts a finite set, so `properClassNumber` is the true
number (not the junk value $0$ of `Set.ncard`). By 103:4 (`ClassFin.genusClasses_finite_nf`) and 102:2: each class
contains at most two proper classes. -/
@[kb "omeara1963" "§103, p. 305 (h⁺(L) is finite)"]
theorem properGenusClasses_finite (hQ : Q.Nondegenerate) (L : Lat F n) :
    (properGenusClasses Q L).Finite := by
  have hG := ClassFin.genusClasses_finite_nf Q hQ L
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact (hG.image _).subset (properGenusClasses_subset_zero Q hn L)
  · obtain ⟨τ, hτ⟩ := Tamagawa.exists_orthGroup_det_neg_one Q hQ hn
    exact ((hG.image _).union (hG.image _)).subset (properGenusClasses_subset Q hQ L τ hτ)

/-- **The spinor genera in a genus are finitely many** (O'Meara 1973, §103, p. 305): $g(L)$ counts a finite set,
being the image of the finite set of classes in $\operatorname{gen}L$ (103:4). -/
@[kb "omeara1963" "§103, p. 305 (g(L) is finite)"]
theorem genusSpinorGenera_finite_of_nondegenerate (hQ : Q.Nondegenerate) (L : Lat F n) :
    (genusSpinorGenera Q L).Finite := by
  have hG := ClassFin.genusClasses_finite_nf Q hQ L
  let φ : LatClass Q → Quotient (spnSetoid Q) :=
    Quotient.map id fun _ _ h => IsIsometric.sameSpinorGenus Q h
  refine (hG.image φ).subset ?_
  rintro _ ⟨M, rfl, hM⟩
  exact ⟨Quotient.mk _ M, ⟨M, rfl, hM⟩, rfl⟩

/-- **The proper spinor genera in a genus are finitely many** (O'Meara 1973, §103, p. 305): $g^+(L)$ counts a finite
set; each spinor genus contains at most two proper spinor genera (102:2). -/
@[kb "omeara1963" "§103, p. 305 (g⁺(L) is finite)"]
theorem genusProperSpinorGenera_finite (hQ : Q.Nondegenerate) (L : Lat F n) :
    (genusProperSpinorGenera Q L).Finite := by
  have hG := genusSpinorGenera_finite_of_nondegenerate Q hQ L
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine (hG.image spnLift₁).subset ?_
    rintro _ ⟨M, rfl, hM⟩
    set c : Quotient (spnSetoid Q) := Quotient.mk _ M
    obtain ⟨γ, k, hk, he⟩ := (mem_latSpinorGenus Q).mp (Quotient.exact (Quotient.out_eq c))
    exact ⟨c, ⟨M, rfl, hM⟩, Quotient.sound ((sameProperSpinorGenus_iff Q).mpr
      ⟨γ, by simp [Tamagawa.mem_soSub], k, hk, he⟩)⟩
  · obtain ⟨τ, hτ⟩ := Tamagawa.exists_orthGroup_det_neg_one Q hQ hn
    exact ((hG.image _).union (hG.image _)).subset (genusProperSpinorGenera_subset τ hQ hτ L)

end Finiteness

/-! ### Named statements (cited results, not proved here) -/

section Statements

/-- **$L$ is a modular lattice** (O'Meara 1973, §82G, p. 231, as used in §102–§104): $L$ is $\mathfrak a$-modular
(`OMeara.IsModular`: $\mathfrak sL = \mathfrak a$ and $\mathfrak vL = \mathfrak a^{r}$) for some fractional ideal
$\mathfrak a$ of the number field $F$, for the form `Q.toQuadraticForm` (O'Meara's $B$, with $B(x, x) = Q(x)$). -/
def IsModularLat (L : Lat F n) : Prop :=
  ∃ a : FractionalIdeal (𝓞 F)⁰ F, a ≠ 0 ∧
    OMeara.IsModular Q.toQuadraticForm (a : Submodule (𝓞 F) F) L.1

/-- **$L$ is a maximal lattice** (O'Meara 1973, §82H, p. 234, as used in §102–§104): $L$ is $\mathfrak a$-maximal
(`OMeara.IsMaximal`: $\mathfrak nL \subseteq \mathfrak a$ and maximal with this property) for some non-zero
fractional ideal $\mathfrak a$ of the number field $F$, for the form `Q.toQuadraticForm`. -/
def IsMaximalLat (L : Lat F n) : Prop :=
  ∃ a : FractionalIdeal (𝓞 F)⁰ F, a ≠ 0 ∧
    OMeara.IsMaximal Q.toQuadraticForm (a : Submodule (𝓞 F) F) L.1

/-- **102.r18: the volume of a genus** (O'Meara 1973, §102A, p. 299): the common volume
$\mathfrak vK$ ($K \in \operatorname{gen}L$) of the lattices of the genus of $L$, here computed on the representative
$L$ (`OMeara.volume` of §82E for the form `Q.toQuadraticForm` over $R = \mathfrak o_F$); that it does not depend on
the representative is `OMeara102_r18`. -/
@[kb "omeara1963" "§102A, p. 299 (the volume of a genus)"]
def genusVolume (L : Lat F n) : Submodule (𝓞 F) F := OMeara.volume Q.toQuadraticForm L.1

/-- **Statement 102.r18: all lattices in a genus have the same volume** (O'Meara 1973, §102A, p. 299, "All lattices
in the same genus have the same volume"): for every $K \in \operatorname{gen}L$, $\mathfrak vK = \mathfrak vL$, so
`genusVolume` is well defined on genera. *Proved* (unconditionally) as `omeara102_r18_holds` in `Sec102Volume.lean`,
by O'Meara's local–global argument $(\mathfrak vK)_\mathfrak p = \mathfrak vK_\mathfrak p = \mathfrak vL_\mathfrak p =
(\mathfrak vL)_\mathfrak p$ at the completions (`volume_loc`, `Sec104LocalMod.lean`). -/
@[kb "omeara1963" "§102A, p. 299 (all lattices in a genus have the same volume) [statement]"]
structure OMeara102_r18 (Q : QuadForm F n) : Prop where
  holds : ∀ L K : Lat F n, SameGenus Q L.1 K.1 → genusVolume Q L = genusVolume Q K

/-- **Statement 102:3: the genus of an $\mathfrak a$-maximal lattice** (O'Meara 1973, §102A, Example 102:3, p. 299):
for a regular space ($Q$ nondegenerate on $F^n$, $F$ a number field) and a non-zero fractional ideal $\mathfrak a$, if
$L$ is an $\mathfrak a$-maximal lattice on $V$ then a lattice $K$ on $V$ is in $\operatorname{gen}L$ if and only if $K$ is
$\mathfrak a$-maximal; in particular any two $\mathfrak a$-maximal lattices on $V$ have the same scale, norm and
volume. *Proved* (unconditionally) as `omeara102_3_holds` in `Sec102Three.lean` (maximality is local at the
completions, `Sec102Max.lean`, and 91:2 at each completion). -/
@[kb "omeara1963" "§102A, 102:3, p. 299 (genus of an a-maximal lattice) [statement]"]
structure OMeara102_3 (Q : QuadForm F n) (hQ : Q.Nondegenerate) (a : FractionalIdeal (𝓞 F)⁰ F) : Prop where
  genus_iff : a ≠ 0 → ∀ L K : Lat F n, OMeara.IsMaximal Q.toQuadraticForm (a : Submodule (𝓞 F) F) L.1 →
    (SameGenus Q L.1 K.1 ↔ OMeara.IsMaximal Q.toQuadraticForm (a : Submodule (𝓞 F) F) K.1)
  same_invariants : a ≠ 0 → ∀ L K : Lat F n,
    OMeara.IsMaximal Q.toQuadraticForm (a : Submodule (𝓞 F) F) L.1 →
    OMeara.IsMaximal Q.toQuadraticForm (a : Submodule (𝓞 F) F) K.1 →
    OMeara.scale Q.toQuadraticForm L.1 = OMeara.scale Q.toQuadraticForm K.1 ∧
    OMeara.normIdeal Q.toQuadraticForm L.1 = OMeara.normIdeal Q.toQuadraticForm K.1 ∧
    OMeara.volume Q.toQuadraticForm L.1 = OMeara.volume Q.toQuadraticForm K.1

/-- **Statement 103:5** (O'Meara 1973, §103, Remark 103:5, pp. 310–311): for the number field $F$ (with $S$ = all
finite spots), a fixed dimension $n$ and a fixed integral ideal $\mathfrak c$ of $\mathfrak o_F$, only finitely many
regular quadratic spaces of dimension $n$ over $F$, up to isometry, carry a lattice $L$ with integral scale
($\mathfrak sL \subseteq \mathfrak o_F$) and volume $\mathfrak vL = \mathfrak c$. Stated for the spaces $(F^n, Q)$,
$Q$ nondegenerate (every $n$-ary space is of this form): there is a finite set $s$ of forms such that each such $Q$ is
isometric over $F$ (`IsometricIn F`) to a member of $s$. *Proved* (unconditionally) as `omeara103_5_holds` in
`Sec103Five.lean`, by O'Meara's route (finitely many discriminant classes, 63:20 and Hasse–Minkowski). -/
@[kb "omeara1963" "§103, 103:5, pp. 310–311 (finitely many spaces carrying a lattice of given volume) [statement]"]
structure OMeara103_5 (F : Type) [Field F] [NumberField F] (n : ℕ) (c : Ideal (𝓞 F)) : Prop where
  holds : ∃ s : Finset (QuadForm F n), ∀ Q : QuadForm F n, Q.Nondegenerate →
    (∃ L : Lat F n, OMeara.scale Q.toQuadraticForm L.1 ≤ 1 ∧
      OMeara.volume Q.toQuadraticForm L.1 = ((c : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)) →
    ∃ Q' ∈ s, Q.IsometricIn F Q'

/-- **Statement 104:9** (O'Meara 1973, §104, Theorem 104:9, p. 320), for $S$ = the set of all finite spots of the
number field $F$ and a regular space $V = (F^n, Q)$: if $\dim V = n \ge 3$, $S$ is indefinite for $V$
(`IsIndefinite Q`: $V_w$ isotropic at some infinite spot $w$), the idèle condition $J_F = P_DJ_F^S$ holds, with
$D = \theta(O^+(V))$ (`spinorNormGroup Q hQ`), and $L$ is a modular or a maximal lattice on $V$ (`IsModularLat`,
`IsMaximalLat`), then $\operatorname{cls}^+L = \operatorname{gen}L$: every $K$ in $\operatorname{gen}L$
(`SameGenus Q L K`) is properly isometric to $L$ (`IsProperIsometric Q L K`).

*The idèle condition.* $J_F$ is Mathlib's `IdeleGroup (𝓞 F) F` (all idèles, finite and infinite components), $J_F^S$
is `OMeara.sIdeles Set.univ` (the idèles of absolute value $1$ at every finite spot, arbitrary at the infinite spots),
and $P_D$ is the group of principal idèles $(\alpha)$, $\alpha \in D$ (the image of $D$ under
`IdeleGroup.unitEmbedding`). Since $J_F$ is abelian, $J_F = P_DJ_F^S$ says exactly that every idèle $i$ is
$i = (\alpha)\,j$ with $\alpha \in D$ and $j \in J_F^S$ (a unit at every finite spot); this is how it is stated in
`holds`. (Equivalently `P_D ⊔ sIdeles univ = ⊤`.)

*Deviation/Note.* O'Meara's $S$ is a Dedekind set of spots containing almost all spots; only the case of all finite
spots is stated. The OCR of the book reads `dim V = 3`; the hypothesis is $\dim V \ge 3$ (as in 104:5).
*Proved* (unconditionally) as `omeara104_9` in `Sec104NineMain.lean`: 104:5 ($\operatorname{cls}^+L =
\operatorname{spn}^+L$ in the indefinite case, strong approximation) with 102:9 (`omeara102_9`, `Sec104Nine.lean`) and
Example 102:10 (ii) ($\theta(O^+(L_\mathfrak p)) \supseteq \mathfrak u_\mathfrak p$ for modular and maximal lattices, by
92:5, 93:20 and 91:8). -/
@[kb "omeara1963" "§104, 104:9, p. 320 [statement]"]
structure OMeara104_9 (Q : QuadForm F n) (hQ : Q.Nondegenerate) : Prop where
  holds : 3 ≤ n → IsIndefinite Q →
    (∀ i : IdeleGroup (𝓞 F) F, ∃ α ∈ spinorNormGroup Q hQ,
      ∃ j ∈ OMeara.sIdeles (Set.univ : Set (HeightOneSpectrum (𝓞 F))),
        i = IdeleGroup.unitEmbedding (𝓞 F) F α * j) →
    ∀ L K : Lat F n, (IsModularLat Q L ∨ IsMaximalLat Q L) → SameGenus Q L.1 K.1 →
      IsProperIsometric Q L.1 K.1

/-- **Statement 104:10** (O'Meara 1973, §104, Theorem 104:10, pp. 320–321): over $F = \mathbb Q$ ($S$ = all finite
spots), for a regular space $V = (\mathbb Q^n, Q)$ with $n \ge 3$ and $V_\infty$ isotropic (`IsIndefinite Q`), two
lattices $L, K$ on $V$ with the same norm and the same scale, which are either both modular or both maximal, are in
the same proper class: $\operatorname{cls}^+L = \operatorname{cls}^+K$ (`IsProperIsometric Q L K`). Norm and scale are
`OMeara.normIdeal` and `OMeara.scale` over $R = \mathbb Z = \mathfrak o_{\mathbb Q}$. (The idèle condition of 104:9 holds
over $\mathbb Q$, Example 102:10, which is why it is not a hypothesis here.) *Note:* the OCR of the book reads
$\dim V = 3$; the hypothesis is $n \ge 3$. *Proved* (unconditionally) as `omeara104_10` in `Sec104Ten.lean`: 104:9 with genus equality for modular lattices
(92:2, 93:29; `Sec104TenModular.lean`) and maximal lattices (91:2; `Sec104TenMax.lean`) and 102:10 (i) for $\mathbb Q$. -/
@[kb "omeara1963" "§104, 104:10, pp. 320–321 [statement]"]
structure OMeara104_10 {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) : Prop where
  holds : 3 ≤ n → IsIndefinite Q → ∀ L K : Lat ℚ n,
    OMeara.normIdeal Q.toQuadraticForm L.1 = OMeara.normIdeal Q.toQuadraticForm K.1 →
    OMeara.scale Q.toQuadraticForm L.1 = OMeara.scale Q.toQuadraticForm K.1 →
    ((IsModularLat Q L ∧ IsModularLat Q K) ∨ (IsMaximalLat Q L ∧ IsMaximalLat Q K)) →
    IsProperIsometric Q L.1 K.1

/-- **Statement 104:12, lattice part** (O'Meara 1973, §104, Example 104:12, p. 321): a unimodular $\mathbb Z$-lattice
$L = \mathbb Z^n$ with norm $\mathbb Z$ on a space $V$ with $V_\infty$ isotropic is isometric to
$\langle 1\rangle^p \perp \langle -1\rangle^q$ ($p + q = n$). Here the lattice is $\mathbb Z^n$ with the integral
form `Q : QuadForm ℤ n` (O'Meara's $B(x, x) = Q(x)$): *unimodular* ($\mathfrak sL = \mathbb Z$, $\mathfrak vL =
\mathbb Z$) means that O'Meara's matrix $G = \tfrac12H_Q$ is an integral matrix (`IsClassicallyIntegral Q`) of
determinant $\pm1$, i.e. $\det H_Q = \pm 2^n$; *norm $\mathbb Z$* means the values $Q(x)$ generate
the ideal $\mathbb Z$; *$V_\infty$ isotropic* means $Q$ is isotropic over $\mathbb R$ (`IsotropicIn ℝ` for
`Q.map (Int.castRingHom ℚ)`); the conclusion is the existence of $p$ and of a $\mathbb Z$-isometry
$U \in GL_n(\mathbb Z)$ with $Q \circ U = \langle 1\rangle^p \perp \langle -1\rangle^{n-p}$ (`signDiag ℤ p`,
`IsometricIn ℤ`). The space part (first part of 104:12) is proved as `omeara104_12_space`.

*Correction.* An earlier version of this statement omitted the hypothesis
`IsClassicallyIntegral Q` (the integrality of $\tfrac12H_Q$, part of "unimodular"); without it the statement is false:
$Q = x_0x_1 + 4x_2^2$ has $\det H_Q = -2^3$, norm $\mathbb Z$ and $V_\infty$ isotropic, but its bilinear form takes the
value $\tfrac12$ on $\mathbb Z^3$, so $Q$ is not $\mathbb Z$-equivalent to any $\langle\pm1,\pm1,\pm1\rangle$.
*Proved* (unconditionally) as `omeara104_12_lattice` / `omeara104_12Lattice_holds` in `Sec104Twelve.lean`. -/
@[kb "omeara1963" "§104, 104:12, p. 321 (lattice part: L ≅ ⟨1⟩ᵖ ⊥ ⟨−1⟩^q) [statement]"]
structure OMeara104_12Lattice {n : ℕ} (Q : QuadForm ℤ n) : Prop where
  holds : IsClassicallyIntegral Q → (Q.hessian.det = 2 ^ n ∨ Q.hessian.det = -2 ^ n) →
    Ideal.span (Set.range Q.eval) = ⊤ →
    (Q.map (Int.castRingHom ℚ)).IsotropicIn ℝ →
    ∃ p : ℕ, Q.IsometricIn ℤ (signDiag ℤ p)

end Statements

end QuadFormsKB.Lattices

/-! ### 103.r3–r4: the counting number of a scalar -/

namespace QuadFormsKB.OMeara

variable (F : Type) [Field F] [NumberField F]

/-- **The counting number of a nonzero scalar** (O'Meara 1973, §103, p. 305): $N\alpha = N(\alpha\mathfrak o)$, the norm
(`idealNorm`, equal to Mathlib's `FractionalIdeal.absNorm`) of the principal fractional ideal $\alpha\mathfrak o$. -/
@[kb "omeara1963" "§103, p. 305 (counting number Nα = N(α𝔬))"]
abbrev countingNumber (α : F) : ℚ := idealNorm F (FractionalIdeal.spanSingleton (𝓞 F)⁰ α)

/-- **Comparison:** $N\alpha$ is Mathlib's absolute norm of the principal fractional ideal $\alpha\mathfrak o$
(for $\alpha \ne 0$). -/
@[kb "omeara1963" "§103, p. 305 (Nα = N(α𝔬), Mathlib absNorm)"]
theorem countingNumber_eq_absNorm {α : F} (hα : α ≠ 0) :
    countingNumber F α = FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 F)⁰ α) :=
  (idealNorm_eq_prod_inv_normalizedAbs F _ (by simpa using hα)).2

/-- **Multiplicativity of the counting number** (O'Meara 1973, §103, p. 305): $N(\alpha\beta) = N\alpha\,N\beta$ for
nonzero $\alpha, \beta \in F$. -/
@[kb "omeara1963" "§103, p. 305 (N(αβ) = Nα Nβ)"]
theorem countingNumber_mul {α β : F} (hα : α ≠ 0) (hβ : β ≠ 0) :
    countingNumber F (α * β) = countingNumber F α * countingNumber F β := by
  rw [countingNumber_eq_absNorm F (mul_ne_zero hα hβ), countingNumber_eq_absNorm F hα,
    countingNumber_eq_absNorm F hβ, map_mul, map_mul]

/-- **Product formula for the counting number** (O'Meara 1973, §103, p. 305, from 33:3): for nonzero $\alpha$,
$N\alpha = \prod_\mathfrak p \lvert\alpha\mathfrak o\rvert_\mathfrak p^{-1}$ over the finite spots $\mathfrak p$,
where $\lvert\alpha\mathfrak o\rvert_\mathfrak p = (N\mathfrak p)^{-\operatorname{ord}_\mathfrak p\alpha}$ is the normalized
absolute value (`normalizedAbs`) of the principal ideal. -/
@[kb "omeara1963" "§103, p. 305 (Nα = ∏ |α|_𝔭⁻¹)"]
theorem countingNumber_eq_prod_inv {α : F} (hα : α ≠ 0) :
    countingNumber F α = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      (normalizedAbs F v (FractionalIdeal.spanSingleton (𝓞 F)⁰ α))⁻¹ :=
  (idealNorm_eq_prod_inv_normalizedAbs F _ (by simpa using hα)).1

end QuadFormsKB.OMeara
