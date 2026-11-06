/-
# O'Meara §82J: scaling a lattice

**Setting.** $R$ is a Dedekind domain with fraction field $F$, $2 \in F^\times$, and $(V, Q)$ a finite-dimensional
quadratic space over $F$ with O'Meara's bilinear form $B$ = `bil Q`. For a non-zero $\alpha \in F$, O'Meara's
space $V^\alpha$ is $V$ with the form $\alpha B$, i.e. the quadratic form `α • Q` (`bil_smul`: the bilinear form of
$\alpha Q$ is $\alpha B$), and $L^\alpha$ is the lattice $L$ regarded in $V^\alpha$: here simply the same
`L : Submodule R V`, with `α • Q` in place of `Q`. The fractional ideal $\alpha\mathfrak a$ is `span R {α} * a`, and
$\alpha^r$ as an ideal is `span R {α ^ r}`.

**Proves** (O'Meara 1963, §82J, p. 238):
* `scale_smul_form`, `normIdeal_smul_form` (proved in `Sec93Gap.lean`, tagged here), `volume_smul_form`:
  $\mathfrak sL^\alpha = \alpha(\mathfrak sL)$,
  $\mathfrak nL^\alpha = \alpha(\mathfrak nL)$, $\mathfrak vL^\alpha = \alpha^r(\mathfrak vL)$, $r$ the rank of $L$;
* `IsModular.smul_form`, `IsMaximal.smul_form`: if $L$ is $\mathfrak a$-modular in $V$ then $L^\alpha$ is
  $\alpha\mathfrak a$-modular in $V^\alpha$; if $L$ is $\mathfrak a$-maximal on $V$ then $L^\alpha$ is
  $\alpha\mathfrak a$-maximal on $V^\alpha$;
* `LatticeIsRepresentedBy.smul_form`: a representation $L \to K$ is a representation $L^\alpha \to K^\alpha$;
* `orthLat_smul_form`, `orthLatPlus_smul_form`, `cls_smul_form`, `clsPlus_smul_form`: $O(L) = O(L^\alpha)$,
  $O^+(L) = O^+(L^\alpha)$, $\operatorname{cls} L = \operatorname{cls} L^\alpha$,
  $\operatorname{cls}^+ L = \operatorname{cls}^+ L^\alpha$ (O'Meara states these for $L$ on a regular non-zero
  space; *Update:* they hold for every lattice);
* `HasDisc.smul_form`: a free lattice with matrix $M$ has the matrix $\alpha M$ in $V^\alpha$ (`gram_smul`), hence
  $d(L^\alpha) = \alpha^r(dL)$;
* `subA_smul_form`: $(L^{\mathfrak a})^\alpha = (L^\alpha)^{\alpha\mathfrak a}$ for the sublattice
  $L^{\mathfrak a} = \{x \in L : B(x, L) \subseteq \mathfrak a\}$ of §82I.

*Transcription.* The machine-read text of p. 238 garbles the formulas $\mathfrak vL^\alpha = \alpha^r(\mathfrak vL)$,
$d(L^\alpha) = \alpha^r(dL)$ and $(L^{\mathfrak a})^\alpha = (L^\alpha)^{\alpha\mathfrak a}$; they are reconstructed
here from the argument (the matrix of $L^\alpha$ is $\alpha M$, of size $r$, and
$\alpha B(x, L) \subseteq \alpha\mathfrak a \iff B(x, L) \subseteq \mathfrak a$); the page image was not read.
-/
import QuadFormsKB.Literature.OMeara.Sec92Class
import QuadFormsKB.Literature.OMeara.Sec82Free
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Literature.OMeara.Sec93Gap

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- $(\alpha\mathfrak o)^n = \alpha^n\mathfrak o$ (any commutative ring `R`; `span_singleton_pow_eq` of
`Sec92SpinorVolume.lean` is the same statement under the hypotheses of §92). -/
theorem span_singleton_pow_eq_span_pow (α : F) (n : ℕ) :
    (span R {α} : Submodule R F) ^ n = span R {α ^ n} := by
  induction n with
  | zero => simp [Submodule.one_eq_span]
  | succ n ih => rw [pow_succ, ih, span_mul_span, Set.singleton_mul_singleton, pow_succ]

attribute [kb "omeara1963" "§82J, p. 238 (sL^α = α sL)"] scale_smul_form
attribute [kb "omeara1963" "§82J, p. 238 (nL^α = α nL)"] normIdeal_smul_form

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- **$\mathfrak vL^\alpha = \alpha^r(\mathfrak vL)$** (O'Meara 1963, §82J, p. 238), $r = \operatorname{rank} L$.
(Formula reconstructed; see the module docstring.) -/
@[kb "omeara1963" "§82J, p. 238 (vL^α = α^r vL)"]
theorem volume_smul_form (α : F) (L : Submodule R V) :
    volume (α • Q) L = span R {α ^ finrank R L} * volume Q L := by
  unfold volume
  rw [span_mul_span, Set.singleton_mul]
  congr 1
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_image, gram_smul, Matrix.det_smul, Fintype.card_fin]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- **$L^\alpha$ is $\alpha\mathfrak a$-modular** (O'Meara 1963, §82J, p. 238): if $L$ is $\mathfrak a$-modular in
$V$ and $\alpha \ne 0$, then $L^\alpha$ is $\alpha\mathfrak a$-modular in $V^\alpha$. -/
@[kb "omeara1963" "§82J, p. 238 (L a-modular ⇒ L^α αa-modular)"]
theorem IsModular.smul_form {a : Submodule R F} {L : Submodule R V} (hL : IsModular Q a L) {α : F}
    (hα : α ≠ 0) : IsModular (α • Q) (span R {α} * a) L := by
  obtain ⟨ha0, hs, hv⟩ := hL
  refine ⟨?_, by rw [scale_smul_form, hs], by rw [volume_smul_form, hv, mul_pow, span_singleton_pow_eq_span_pow]⟩
  intro h
  apply ha0
  have : span R {α⁻¹} * (span R {α} * a) = a := by
    rw [← mul_assoc, span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hα, ← one_eq_span, one_mul]
  rw [← this, h, mul_bot]

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- Cancelling a non-zero principal factor: $\alpha\mathfrak b \subseteq \alpha\mathfrak a \iff \mathfrak b \subseteq
\mathfrak a$. -/
theorem span_singleton_mul_le_iff {α : F} (hα : α ≠ 0) {a b : Submodule R F} :
    span R {α} * b ≤ span R {α} * a ↔ b ≤ a := by
  refine ⟨fun h => ?_, fun h => mul_le_mul' le_rfl h⟩
  have hc : ∀ c : Submodule R F, span R {α⁻¹} * (span R {α} * c) = c := fun c => by
    rw [← mul_assoc, span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hα, ← one_eq_span, one_mul]
  rw [← hc b, ← hc a]
  exact mul_le_mul' le_rfl h

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- **$L^\alpha$ is $\alpha\mathfrak a$-maximal** (O'Meara 1963, §82J, p. 238): if $L$ is $\mathfrak a$-maximal on
$V$ and $\alpha \ne 0$, then $L^\alpha$ is $\alpha\mathfrak a$-maximal on $V^\alpha$. -/
@[kb "omeara1963" "§82J, p. 238 (L a-maximal ⇒ L^α αa-maximal)"]
theorem IsMaximal.smul_form {a : Submodule R F} {L : Submodule R V} (hL : IsMaximal Q a L) {α : F}
    (hα : α ≠ 0) : IsMaximal (α • Q) (span R {α} * a) L := by
  obtain ⟨hlat, hn, hmax⟩ := hL
  refine ⟨hlat, by rw [normIdeal_smul_form]; exact mul_le_mul' le_rfl hn, fun K hK hLK hnK => ?_⟩
  rw [normIdeal_smul_form, span_singleton_mul_le_iff hα] at hnK
  exact hmax K hK hLK hnK

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- **A representation $L \to K$ is a representation $L^\alpha \to K^\alpha$** (O'Meara 1963, §82J, p. 238). -/
@[kb "omeara1963" "§82J, p. 238 (σ : L → K gives σ : L^α → K^α)"]
theorem LatticeIsRepresentedBy.smul_form {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V']
    [IsScalarTower R F V'] {Q' : QuadraticForm F V'} {L : Submodule R V'} {K : Submodule R V}
    (h : LatticeIsRepresentedBy Q' Q L K) (α : F) : LatticeIsRepresentedBy (α • Q') (α • Q) L K := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun x => by simp only [smul_apply, hf x]⟩

omit [IsDedekindDomain R] [IsFractionRing R F] in
/-- **$O(L) = O(L^\alpha)$** (O'Meara 1963, §82J, p. 238) for $\alpha \ne 0$ (O'Meara: $L$ on a regular non-zero
space; the equality holds for every lattice). -/
@[kb "omeara1963" "§82J, p. 238 (O(L) = O(L^α))"]
theorem orthLat_smul_form {α : F} (hα : α ≠ 0) (L : Submodule R V) : orthLat (α • Q) L = orthLat Q L := by
  ext σ
  simp only [orthLat, Subgroup.mem_mk, Set.mem_ofPred_eq, Submonoid.mem_mk, Subsemigroup.mem_mk,
    orth_smul Q hα]

omit [IsDedekindDomain R] [IsFractionRing R F] in
/-- **$O^+(L) = O^+(L^\alpha)$** (O'Meara 1963, §82J, p. 238) for $\alpha \ne 0$. -/
@[kb "omeara1963" "§82J, p. 238 (O⁺(L) = O⁺(L^α))"]
theorem orthLatPlus_smul_form {α : F} (hα : α ≠ 0) (L : Submodule R V) :
    orthLatPlus (α • Q) L = orthLatPlus Q L := by
  unfold orthLatPlus
  rw [orthLat_smul_form Q hα, orthPlus_smul Q hα]

omit [IsDedekindDomain R] [IsFractionRing R F] in
/-- **$\operatorname{cls} L = \operatorname{cls} L^\alpha$** (O'Meara 1963, §82J, p. 238) for $\alpha \ne 0$. -/
@[kb "omeara1963" "§82J, p. 238 (cls L = cls L^α)"]
theorem cls_smul_form {α : F} (hα : α ≠ 0) (L : Submodule R V) : cls (α • Q) L = cls Q L := by
  unfold cls
  rw [orth_smul Q hα]

omit [IsDedekindDomain R] [IsFractionRing R F] in
/-- **$\operatorname{cls}^+ L = \operatorname{cls}^+ L^\alpha$** (O'Meara 1963, §82J, p. 238) for $\alpha \ne 0$. -/
@[kb "omeara1963" "§82J, p. 238 (cls⁺ L = cls⁺ L^α)"]
theorem clsPlus_smul_form {α : F} (hα : α ≠ 0) (L : Submodule R V) : clsPlus (α • Q) L = clsPlus Q L := by
  unfold clsPlus
  rw [orthPlus_smul Q hα]

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- **$d(L^\alpha) = \alpha^r(dL)$** (O'Meara 1963, §82J, p. 238): if the free lattice $L$ has a base with
discriminant $\beta$, the same base has discriminant $\alpha^r\beta$ in $V^\alpha$ (its matrix is $\alpha M$,
`gram_smul`). (Formula reconstructed; see the module docstring.) -/
@[kb "omeara1963" "§82J, p. 238 (d(L^α) = α^r dL)"]
theorem HasDisc.smul_form {L : Submodule R V} {β : F} (h : HasDisc Q L β) (α : F) :
    HasDisc (α • Q) L (α ^ finrank R L * β) := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by rw [gram_smul, Matrix.det_smul, Fintype.card_fin, hb]⟩

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- **$(L^{\mathfrak a})^\alpha = (L^\alpha)^{\alpha\mathfrak a}$** (O'Meara 1963, §82J, p. 238) for $\alpha \ne 0$:
the sublattice $\{x \in L : \alpha B(x, L) \subseteq \alpha\mathfrak a\}$ of $L^\alpha$ is
$L^{\mathfrak a} = \{x \in L : B(x, L) \subseteq \mathfrak a\}$. (Formula reconstructed; see the module
docstring.) -/
@[kb "omeara1963" "§82J, p. 238 ((L^a)^α = (L^α)^(αa))"]
theorem subA_smul_form {α : F} (hα : α ≠ 0) (a : Submodule R F) (L : Submodule R V) :
    subA (α • Q) (span R {α} * a) L = subA Q a L := by
  ext x
  simp only [subA, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, bil_smul,
    mem_span_singleton_mul]
  refine and_congr_right fun _ => forall₂_congr fun y _ => ?_
  constructor
  · rintro ⟨z, hz, hzx⟩
    rwa [mul_left_cancel₀ hα hzx] at hz
  · intro h
    exact ⟨_, h, rfl⟩

end QuadFormsKB.OMeara
