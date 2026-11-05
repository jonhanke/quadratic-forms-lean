/-
# O'Meara §93E: 93:23 (scaling the form), 93:25 (monotonicity), 93:26 (even case), 93:27

**Setting** (as in `Sec93E.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$,
$\pi$ an irreducible element, `dord hπ` the order function; $(V, Q)$ a quadratic space over $F$, lattices are
`Submodule R V`, and a Jordan splitting $L = L_1 \perp \cdots \perp L_t$ is `hL : IsJordanSplitting Q L Ls`.
**Indices are $0$-based**: O'Meara's $\mathfrak f_i$ is `fIdeal Q L Ls (i-1) i`.

**Proves** (O'Meara 1963, §93E, pp. 266–267)
* `isJordanSplitting_smul_form`, `isJordanSplitting_smul_form_iff`, `scale_smul_form_eq`,
  `fundSub_smul_form`, `fundNormGroup_smul_form`, `fundWeight_smul_form`, `isFundNormGenerators_smul_form`,
  `fIdeal_smul_form`, `isSaturated_smul_form_iff` (**93:23**): scaling the form by $\alpha \ne 0$ ($L^\alpha$ is the
  lattice $L$ in the space with form `α • Q`): Jordan splittings and saturation are preserved, $\mathfrak s_i$,
  $\mathfrak g_i$, $\mathfrak w_i$, $a_i$ scale by $\alpha$, and $\mathfrak f_i$ is unchanged. All unconditional
  (no dyadic hypothesis), for $\alpha \ne 0$.
* `exists_scale_eq_span_mul`, `exists_scale_eq_pow_mul`, `fundNormGroup_sq_smul_le`, `fundWeight_sq_smul_le`,
  `fundNormIdeal_sq_mul_le` (**93:25**): $\pi^{-2s_t}\mathfrak g_t \supseteq \cdots \supseteq \pi^{-2s_1}\mathfrak g_1$,
  the same for $\mathfrak w$, and $\mathfrak s_j^{-2}a_j\mathfrak o \supseteq \mathfrak s_i^{-2}a_i\mathfrak o$. The
  proof is direct (not through 93:24): $x \in L^{\mathfrak s_i} \Rightarrow \pi^kx \in L^{\mathfrak s_j}$. No dyadic
  hypothesis is needed.
* `mul_fIdeal_of_even` (**93:26**, even case): $\mathfrak s_i^2\mathfrak f_i = \mathfrak d(a_ia_{i+1}) +
  a_i\mathfrak w_{i+1} + a_{i+1}\mathfrak w_i + 2\mathfrak p^{\frac12(u_i+u_{i+1})+s_i}$ (dyadic, Henselian, finite
  residue field, $L$ regular; the odd case is `mul_fIdeal_of_odd` of `Sec93FIdeal.lean`).
* `dord_fundNormGenerator_le`, `mul_fIdeal_of_dord_eq`, `mul_fIdeal_of_dord_succ`, `mul_fIdeal_of_dord_add_two`
  (**93:27**): $u_{i+1} \ge u_i$ and $\mathfrak s_i^2\mathfrak f_i = a_{i+1}\mathfrak w_i$, $a_ia_{i+1}\mathfrak o$,
  $a_i\mathfrak w_{i+1}$ in the three cases.

*Note on 93:25.* O'Meara's "$\mathfrak s_t^{-2}a_t \supseteq \cdots \supseteq \mathfrak s_1^{-2}a_1$" is formalized
without inverses as $\mathfrak s_j^2\,\mathfrak nL^{\mathfrak s_i} \subseteq \mathfrak s_i^2\,\mathfrak nL^{\mathfrak s_j}$
for $i \le j$ (`fundNormIdeal_sq_mul_le`), and in orders as $u_j - 2s_j \le u_i - 2s_i$ (`ord_scale_ineq`). The
"fact" used in 93:26 ("$a_i\mathfrak s_i^{-2} \subseteq a_{i+1}\mathfrak s_{i+1}^{-2}$") is the same statement.
-/
import QuadFormsKB.Literature.OMeara.Sec93FIdeal

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace FundAux
end FundAux
open FundAux
open FIdealAux

section Mono

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)] {π : R}
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

namespace FundAux

lemma c_smul_mem_fundSub {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V} {i j : Fin t} {c : R}
    (hc : scale Q (Ls j) = (R ∙ algebraMap R F c) * scale Q (Ls i)) {x : V} (hx : x ∈ fundSub Q L Ls i) :
    c • x ∈ fundSub Q L Ls j := by
  refine ⟨L.smul_mem c hx.1, fun y hy => ?_⟩
  rw [bil_rsmul_left, hc]
  exact Submodule.mul_mem_mul (mem_span_singleton_self _) (hx.2 y hy)

lemma sq_mul_mem_scale {t : ℕ} {Ls : Fin t → Submodule R V} {i j : Fin t} {c : R}
    (hc : scale Q (Ls j) = (R ∙ algebraMap R F c) * scale Q (Ls i)) {d : F} (hd : d ∈ scale Q (Ls i)) :
    algebraMap R F c ^ 2 * d ∈ scale Q (Ls j) := by
  have h1 : algebraMap R F c * d ∈ scale Q (Ls j) := hc ▸ Submodule.mul_mem_mul (mem_span_singleton_self _) hd
  have h2 := (scale Q (Ls j)).smul_mem c h1
  have : algebraMap R F c ^ 2 * d = c • (algebraMap R F c * d) := by rw [Algebra.smul_def]; ring
  rw [this]; exact h2

lemma sq_mul_mem_fundNormGroup {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) {i j : Fin t} {c : R}
    (hc : scale Q (Ls j) = (R ∙ algebraMap R F c) * scale Q (Ls i)) {g : F} (hg : g ∈ fundNormGroup Q L Ls i) :
    algebraMap R F c ^ 2 * g ∈ fundNormGroup Q L Ls j := by
  obtain ⟨x, hx, d, hd, rfl⟩ := hg
  have hd' : d ∈ scale Q (Ls i) := by rwa [scale_fundSub Q hfg hJ] at hd
  refine ⟨c • x, c_smul_mem_fundSub Q hc hx, algebraMap R F c ^ 2 * d, ?_, ?_⟩
  · show _ ∈ scale Q (fundSub Q L Ls j)
    rw [scale_fundSub Q hfg hJ]; exact sq_mul_mem_scale Q hc hd'
  · rw [Q_rsmul]; ring

lemma smul_mono_aux (a : F) {A B : Submodule R F} (h : A ≤ B) : a • A ≤ a • B := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
  exact Submodule.smul_mem_pointwise_smul _ _ _ (h hx)

end FundAux

/-- **Scales of the fundamental lattices** (O'Meara 1963, §93E, p. 267): if $\mathfrak s_i \supseteq \mathfrak s_j$
($i \le j$), then $\mathfrak s_j = c\,\mathfrak s_i$ for some $c \in \mathfrak o$ (the scales are principal). -/
theorem exists_scale_eq_span_mul {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) {i j : Fin t} (hij : i ≤ j) :
    ∃ c : R, scale Q (Ls j) = (R ∙ algebraMap R F c) * scale Q (Ls i) := by
  have hLs : ∀ k, Ls k ≤ L := fun k => hJ.split.iSup_eq ▸ le_iSup Ls k
  obtain ⟨σ, hσ, hs⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (FG.of_le hfg (hLs i))) (hJ.modular i).1
  obtain ⟨τ, hτ, ht⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (FG.of_le hfg (hLs j))) (hJ.modular j).1
  have hle : scale Q (Ls j) ≤ scale Q (Ls i) := hJ.scale_strictAnti.antitone hij
  rw [hs, ht] at hle
  obtain ⟨c, hc⟩ := mem_span_singleton.1 (hle (mem_span_singleton_self τ))
  refine ⟨c, ?_⟩
  rw [hs, ht, span_mul_span', ← hc, Algebra.smul_def]

/-- **93:25, the exponent** (O'Meara 1963, §93E, p. 267): for $i \le j$, if $\mathfrak s_i = \sigma\mathfrak o$ and
$\mathfrak s_j = \tau\mathfrak o$, then $\mathfrak s_j = \pi^k\mathfrak s_i$ with $k = s_j - s_i =
\operatorname{ord}\tau - \operatorname{ord}\sigma \ge 0$. -/
theorem exists_scale_eq_pow_mul (hπ : Irreducible π) {L : Submodule R V} {t : ℕ}
    {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls) {i j : Fin t} (hij : i ≤ j) {σ τ : F}
    (hσ : scale Q (Ls i) = R ∙ σ) (hτ : scale Q (Ls j) = R ∙ τ) :
    ∃ k : ℕ, scale Q (Ls j) = (R ∙ algebraMap R F π ^ (k : ℤ)) * scale Q (Ls i) ∧
      (k : ℤ) = dord hπ τ - dord hπ σ := by
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    exact (hJ.modular i).1 ((hJ.modular i).2.1.symm.trans (by rw [hσ]; simp))
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact (hJ.modular j).1 ((hJ.modular j).2.1.symm.trans (by rw [hτ]; simp))
  have hle : scale Q (Ls j) ≤ scale Q (Ls i) := hJ.scale_strictAnti.antitone hij
  rw [hσ, hτ] at hle
  have hord : dord hπ σ ≤ dord hπ τ := (mem_span_iff hπ hτ0 hσ0).1 (hle (mem_span_singleton_self τ))
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  refine ⟨(dord hπ τ - dord hπ σ).toNat, ?_, by omega⟩
  have hk : (((dord hπ τ - dord hπ σ).toNat : ℕ) : ℤ) = dord hπ τ - dord hπ σ := by omega
  rw [hσ, hτ, hk, span_mul_span']
  refine span_eq_of_dord_eq hπ hτ0 (mul_ne_zero (zpow_ne_zero _ hpi) hσ0) ?_
  rw [dord_mul hπ (zpow_ne_zero _ hpi) hσ0, dord_zpow]; omega

/-- **93:25, norm groups** (O'Meara 1963, §93E, p. 267): $\pi^{-2s_t}\mathfrak g_t \supseteq \cdots \supseteq
\pi^{-2s_1}\mathfrak g_1$. For $i \le j$ and $c \in \mathfrak o$ with $\mathfrak s_j = c\,\mathfrak s_i$ (e.g.
$c = \pi^{s_j - s_i}$, `exists_scale_eq_pow_mul`), we have $c^2\mathfrak g_i \subseteq \mathfrak g_j$, i.e.
$\mathfrak s_j^{-2}\mathfrak g_j \supseteq \mathfrak s_i^{-2}\mathfrak g_i$. *Proof is direct, not through 93:24:* for
$x \in L^{\mathfrak s_i}$ the vector $cx$ lies in $L^{\mathfrak s_j}$ and $Q(cx) = c^2Q(x)$, and
$c^2\mathfrak s_i \subseteq \mathfrak s_j$ for the term $2\mathfrak s$ of the norm group. (The statement is for any
$c \in \mathfrak o$ with $\mathfrak s_j = c\mathfrak s_i$; `hij` is not needed once $c$ is given.) -/
@[kb "omeara1963" "§93E, 93:25, p. 267"]
theorem fundNormGroup_sq_smul_le {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) {i j : Fin t} {c : R}
    (hc : scale Q (Ls j) = (R ∙ algebraMap R F c) * scale Q (Ls i)) :
    (fundNormGroup Q L Ls i).map (AddMonoidHom.mulLeft (algebraMap R F c ^ 2)) ≤ fundNormGroup Q L Ls j := by
  rintro _ ⟨g, hg, rfl⟩
  exact sq_mul_mem_fundNormGroup Q hfg hJ hc hg

/-- **93:25, weights** (O'Meara 1963, §93E, p. 267): $\pi^{-2s_t}\mathfrak w_t \supseteq \cdots \supseteq
\pi^{-2s_1}\mathfrak w_1$; for $c \in \mathfrak o$ with $\mathfrak s_j = c\,\mathfrak s_i$, $c^2\mathfrak w_i \subseteq
\mathfrak w_j$. -/
@[kb "omeara1963" "§93E, 93:25, p. 267"]
theorem fundWeight_sq_smul_le {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) {i j : Fin t} {c : R}
    (hc : scale Q (Ls j) = (R ∙ algebraMap R F c) * scale Q (Ls i)) :
    algebraMap R F c ^ 2 • fundWeight Q L Ls i ≤ fundWeight Q L Ls j := by
  set a : F := algebraMap R F c ^ 2 with ha
  have hm : a • normGroupIdeal Q (fundSub Q L Ls i) ≤ normGroupIdeal Q (fundSub Q L Ls j) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    intro r
    have h1 : a * (r • y) ∈ fundNormGroup Q L Ls j := sq_mul_mem_fundNormGroup Q hfg hJ hc (hy r)
    have : r • a • y = a * (r • y) := by
      rw [smul_eq_mul, Algebra.smul_def, Algebra.smul_def]; ring
    rw [this]; exact h1
  have hs : a • scale Q (fundSub Q L Ls i) ≤ scale Q (fundSub Q L Ls j) := by
    intro z hz
    obtain ⟨d, hd, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    rw [scale_fundSub Q hfg hJ] at hd ⊢
    exact sq_mul_mem_scale Q hc hd
  show a • (_ + _) ≤ _ + _
  rw [Submodule.add_eq_sup, smul_sup', Submodule.add_eq_sup]
  refine sup_le_sup ?_ ?_
  · rw [← mul_smul_comm]; exact mul_le_mul' le_rfl hm
  · rw [smul_comm]; exact smul_mono_aux _ hs

/-- **93:25, the ideals $\mathfrak s^{-2}a\mathfrak o$** (O'Meara 1963, §93E, p. 267): $\mathfrak s_j^{-2}a_j
\supseteq \mathfrak s_i^{-2}a_i$ for $i \le j$, stated without inverses as $\mathfrak s_j^2\,\mathfrak nL^{\mathfrak s_i}
\subseteq \mathfrak s_i^2\,\mathfrak nL^{\mathfrak s_j}$ (multiply both sides by $\mathfrak s_i^2\mathfrak s_j^2$);
$\mathfrak nL^{\mathfrak s_i} = a_i\mathfrak o$ (`fundNormIdeal`). (Hypothesis `hc` as in `fundNormGroup_sq_smul_le`.)
*Note:* the inclusion reads this way round, not $\mathfrak s_i^2 a_j \subseteq \mathfrak s_j^2 a_i$. -/
@[kb "omeara1963" "§93E, 93:25, p. 267"]
theorem fundNormIdeal_sq_mul_le {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) {i j : Fin t} {c : R}
    (hc : scale Q (Ls j) = (R ∙ algebraMap R F c) * scale Q (Ls i)) :
    scale Q (Ls j) * scale Q (Ls j) * fundNormIdeal Q L Ls i ≤
      scale Q (Ls i) * scale Q (Ls i) * fundNormIdeal Q L Ls j := by
  have hn : (R ∙ algebraMap R F c) * (R ∙ algebraMap R F c) * fundNormIdeal Q L Ls i ≤
      fundNormIdeal Q L Ls j := by
    rw [span_mul_span', fIdeal_fundNormIdeal_eq_span, Submodule.span_mul_span, span_le]
    rintro _ ⟨u, hu, g, hg, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    rw [← pow_two]
    exact normGroup_subset_normIdeal Q _ (sq_mul_mem_fundNormGroup Q hfg hJ hc hg)
  calc scale Q (Ls j) * scale Q (Ls j) * fundNormIdeal Q L Ls i
      = scale Q (Ls i) * scale Q (Ls i) *
        ((R ∙ algebraMap R F c) * (R ∙ algebraMap R F c) * fundNormIdeal Q L Ls i) := by rw [hc]; ring
    _ ≤ _ := mul_le_mul' le_rfl hn

end Mono

section ScaleForm

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

namespace FundAux

lemma smul_eq_span_mul (c : F) (N : Submodule R F) : c • N = (R ∙ c) * N := by
  ext z
  rw [Submodule.mem_smul_pointwise_iff_exists, mem_span_singleton_mul_iff']
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

lemma mul_mem_span_mul_iff {α : F} (hα : α ≠ 0) {a : Submodule R F} {z : F} :
    α * z ∈ (R ∙ α) * a ↔ z ∈ a := by
  rw [mem_span_singleton_mul_iff']
  constructor
  · rintro ⟨c, hc, h⟩; rwa [mul_left_cancel₀ hα h]
  · intro h; exact ⟨z, h, rfl⟩

lemma span_mul_le_span_mul_iff {α : F} (hα : α ≠ 0) {a b : Submodule R F} :
    (R ∙ α) * a ≤ (R ∙ α) * b ↔ a ≤ b := by
  constructor
  · intro h z hz
    exact (mul_mem_span_mul_iff hα).1 (h (Submodule.mul_mem_mul (mem_span_singleton_self α) hz))
  · intro h; exact mul_le_mul' le_rfl h

lemma span_mul_cancel {α : F} (hα : α ≠ 0) {a b : Submodule R F} :
    (R ∙ α) * a = (R ∙ α) * b ↔ a = b := by
  constructor
  · intro h
    exact le_antisymm ((span_mul_le_span_mul_iff hα).1 h.le) ((span_mul_le_span_mul_iff hα).1 h.ge)
  · rintro rfl; rfl

lemma span_mul_ne_bot {α : F} (hα : α ≠ 0) {a : Submodule R F} (ha : a ≠ ⊥) : (R ∙ α) * a ≠ ⊥ := by
  intro h
  apply ha
  rw [eq_bot_iff]
  intro z hz
  have : α * z ∈ (R ∙ α) * a := Submodule.mul_mem_mul (mem_span_singleton_self α) hz
  rw [h, Submodule.mem_bot] at this
  rw [Submodule.mem_bot]
  exact (mul_eq_zero.1 this).resolve_left hα

lemma volume_smul_form (α : F) (L : Submodule R V) :
    volume (α • Q) L = (R ∙ α ^ finrank R L) * volume Q L := by
  rw [volume, volume, Submodule.span_mul_span]
  congr 1
  ext d
  have hdet : ∀ x : Fin (finrank R L) → V, (gram (α • Q) x).det = α ^ finrank R L * (gram Q x).det := by
    intro x
    have : gram (α • Q) x = α • gram Q x := by ext i j; simp [gram, bil_smul_form]
    rw [this, Matrix.det_smul, Fintype.card_fin]
  simp only [Set.mem_ofPred_eq, Set.singleton_mul, Set.mem_image, hdet]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

lemma isModular_smul_form {α : F} (hα : α ≠ 0) {a : Submodule R F} {L : Submodule R V}
    (h : IsModular Q a L) : IsModular (α • Q) ((R ∙ α) * a) L := by
  obtain ⟨ha, hs, hv⟩ := h
  refine ⟨span_mul_ne_bot hα ha, by rw [scale_smul_form, hs], ?_⟩
  rw [volume_smul_form, hv, mul_pow, span_pow, Set.singleton_pow]

lemma subA_smul_form {α : F} (hα : α ≠ 0) (a : Submodule R F) (L : Submodule R V) :
    subA (α • Q) ((R ∙ α) * a) L = subA Q a L := by
  ext x
  show (x ∈ L ∧ ∀ y ∈ L, bil (α • Q) x y ∈ (R ∙ α) * a) ↔ (x ∈ L ∧ ∀ y ∈ L, bil Q x y ∈ a)
  simp only [bil_smul_form, mul_mem_span_mul_iff hα]

end FundAux

/-- **93:23 (a), Jordan splittings** (O'Meara 1963, §93E, 93:23, p. 266): if $L = L_1 \perp \cdots \perp L_t$ is a
Jordan splitting on $V$, it is a Jordan splitting on $V^\alpha$ (the form $\alpha Q$, `α • Q`), $\alpha \ne 0$.
Here $\mathfrak sL_i^\alpha = \alpha\,\mathfrak sL_i$, $\mathfrak v(L_i^\alpha) = \alpha^{\operatorname{rk}}\mathfrak v(L_i)$ and
multiplication by $\alpha\mathfrak o$ preserves strict inclusion. -/
@[kb "omeara1963" "§93E, 93:23, p. 266"]
theorem isJordanSplitting_smul_form {α : F} (hα : α ≠ 0) {L : Submodule R V} {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) : IsJordanSplitting (α • Q) L Ls := by
  refine ⟨⟨fun i j hij x hx y hy => ?_, hL.split.indep, hL.split.iSup_eq⟩, fun i => ?_, fun i j hij => ?_⟩
  · rw [bil_smul_form, hL.split.orth i j hij x hx y hy, mul_zero]
  · have := isModular_smul_form Q hα (hL.modular i)
    rwa [← scale_smul_form] at this
  · have h := hL.scale_strictAnti hij
    simp only [scale_smul_form]
    refine lt_of_le_not_ge (mul_le_mul' le_rfl h.le) fun h' => ?_
    exact h.not_ge ((span_mul_le_span_mul_iff hα).1 h')

/-- **93:23 (a), iff form** (O'Meara 1963, §93E, 93:23, p. 266): $L = L_1 \perp \cdots \perp L_t$ is a Jordan
splitting on $V$ if and only if it is on $V^\alpha$ ($\alpha \ne 0$). -/
@[kb "omeara1963" "§93E, 93:23, p. 266"]
theorem isJordanSplitting_smul_form_iff {α : F} (hα : α ≠ 0) {L : Submodule R V} {t : ℕ}
    {Ls : Fin t → Submodule R V} : IsJordanSplitting (α • Q) L Ls ↔ IsJordanSplitting Q L Ls := by
  refine ⟨fun h => ?_, isJordanSplitting_smul_form Q hα⟩
  have := isJordanSplitting_smul_form (α • Q) (inv_ne_zero hα) h
  rwa [smul_smul, inv_mul_cancel₀ hα, one_smul] at this

/-- **93:23 (b), scales** (O'Meara 1963, §93E, 93:23, p. 266): $\mathfrak s_i^\alpha = \alpha\,\mathfrak s_i$, i.e.
$\mathfrak s(L_i^\alpha) = \alpha\,\mathfrak sL_i$ (`α •` is the pointwise product with the fractional ideal
$\alpha\mathfrak o$); valid for any lattice. -/
@[kb "omeara1963" "§93E, 93:23, p. 266"]
theorem scale_smul_form_eq (α : F) (M : Submodule R V) : scale (α • Q) M = α • scale Q M := by
  rw [scale_smul_form, smul_eq_span_mul]

/-- **$L^{\mathfrak s_i}$ is unchanged by scaling the form** (O'Meara 1963, §93E, 93:23, p. 266): since
$\mathfrak s(L_i^\alpha) = \alpha\mathfrak s_i$, $(L^\alpha)^{\alpha\mathfrak s_i} = L^{\mathfrak s_i}$ as sets of vectors
($\{x \in L : \alpha B(x, L) \subseteq \alpha\mathfrak s_i\}$). -/
@[kb "omeara1963" "§93E, 93:23, p. 266"]
theorem fundSub_smul_form {α : F} (hα : α ≠ 0) (L : Submodule R V) {t : ℕ} (Ls : Fin t → Submodule R V)
    (i : Fin t) : fundSub (α • Q) L Ls i = fundSub Q L Ls i := by
  unfold fundSub
  rw [scale_smul_form, subA_smul_form Q hα]

/-- **93:23 (b), norm groups** (O'Meara 1963, §93E, 93:23, p. 266): $\mathfrak g_i^\alpha = \alpha\,\mathfrak g_i$. -/
@[kb "omeara1963" "§93E, 93:23, p. 266"]
theorem fundNormGroup_smul_form {α : F} (hα : α ≠ 0) (L : Submodule R V) {t : ℕ} (Ls : Fin t → Submodule R V)
    (i : Fin t) :
    fundNormGroup (α • Q) L Ls i = (fundNormGroup Q L Ls i).map (AddMonoidHom.mulLeft α) := by
  unfold fundNormGroup
  rw [fundSub_smul_form Q hα, normGroup_smul_form]

/-- **93:23 (b), weights** (O'Meara 1963, §93E, 93:23, p. 266): $\mathfrak w_i^\alpha = \alpha\,\mathfrak w_i$. -/
@[kb "omeara1963" "§93E, 93:23, p. 266"]
theorem fundWeight_smul_form {α : F} (hα : α ≠ 0) (L : Submodule R V) {t : ℕ} (Ls : Fin t → Submodule R V)
    (i : Fin t) : fundWeight (α • Q) L Ls i = α • fundWeight Q L Ls i := by
  unfold fundWeight
  rw [fundSub_smul_form Q hα, weight_smul_form Q hα, smul_eq_span_mul]

/-- **The fundamental norm ideal under scaling** (O'Meara 1963, §93E, 93:23, p. 266):
$\mathfrak n(L^{\mathfrak s_i})^\alpha = \alpha\,\mathfrak n(L^{\mathfrak s_i})$. -/
theorem fundNormIdeal_smul_form {α : F} (hα : α ≠ 0) (L : Submodule R V) {t : ℕ} (Ls : Fin t → Submodule R V)
    (i : Fin t) : fundNormIdeal (α • Q) L Ls i = α • fundNormIdeal Q L Ls i := by
  unfold fundNormIdeal
  rw [fundSub_smul_form Q hα, normIdeal_smul_form, smul_eq_span_mul]

/-- **93:23 (b), fundamental norm generators** (O'Meara 1963, §93E, 93:23, p. 266): if $a_i$ are fundamental norm
generators of $L$, then $\alpha a_i$ are fundamental norm generators of $L^\alpha$. -/
@[kb "omeara1963" "§93E, 93:23, p. 266"]
theorem isFundNormGenerators_smul_form {α : F} (hα : α ≠ 0) {L : Submodule R V} {t : ℕ}
    {Ls : Fin t → Submodule R V} {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) :
    IsFundNormGenerators (α • Q) L Ls (fun i => α * a i) := by
  intro i
  rw [fundSub_smul_form Q hα]
  exact IsNormGenerator.smul_form Q (ha i) α

end ScaleForm

section ScaleFormF

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

namespace FundAux

lemma defect_iSup_smul (α : F) (g g' : AddSubgroup F) :
    (⨆ (x : F) (_ : x ∈ g.map (AddMonoidHom.mulLeft α)) (y : F) (_ : y ∈ g'.map (AddMonoidHom.mulLeft α)),
        quadDefect R (x * y)) =
      (R ∙ α ^ 2) * ⨆ (x : F) (_ : x ∈ g) (y : F) (_ : y ∈ g'), quadDefect R (x * y) := by
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
    obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.1 hy
    have e : (AddMonoidHom.mulLeft α) a * (AddMonoidHom.mulLeft α) b = α ^ 2 * (a * b) := by
      simp only [AddMonoidHom.coe_mulLeft]; ring
    rw [e, quadDefect_sq_mul]
    refine mul_le_mul' le_rfl ?_
    exact le_iSup_of_le a <| le_iSup_of_le ha <| le_iSup_of_le b <| le_iSup_of_le hb le_rfl
  · simp only [Submodule.mul_iSup]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun b => iSup_le fun hb => ?_
    rw [← quadDefect_sq_mul]
    have e : α ^ 2 * (a * b) = (AddMonoidHom.mulLeft α) a * (AddMonoidHom.mulLeft α) b := by
      simp only [AddMonoidHom.coe_mulLeft]; ring
    rw [e]
    exact le_iSup_of_le _ <| le_iSup_of_le (AddSubgroup.mem_map.2 ⟨a, ha, rfl⟩) <| le_iSup_of_le _ <|
      le_iSup_of_le (AddSubgroup.mem_map.2 ⟨b, hb, rfl⟩) le_rfl

lemma sqRoots_iff {α : F} (hα : α ≠ 0) (n n' : Submodule R F) (z : F) :
    (R ∙ (α * z)) * (R ∙ (α * z)) = ((R ∙ α) * n) * ((R ∙ α) * n') ↔ (R ∙ z) * (R ∙ z) = n * n' := by
  have e1 : (R ∙ (α * z)) * (R ∙ (α * z)) = (R ∙ (α * α)) * ((R ∙ z) * (R ∙ z)) := by
    simp only [span_mul_span']
    rw [show α * z * (α * z) = α * α * (z * z) by ring]
  have e2 : ((R ∙ α) * n) * ((R ∙ α) * n') = (R ∙ (α * α)) * (n * n') := by
    rw [← span_mul_span']; ring
  rw [e1, e2]
  exact span_mul_cancel (mul_ne_zero hα hα)

lemma sqRoots_span_smul {α : F} (hα : α ≠ 0) (n n' : Submodule R F) :
    span R {z : F | (R ∙ z) * (R ∙ z) = ((R ∙ α) * n) * ((R ∙ α) * n')} =
      (R ∙ α) * span R {z : F | (R ∙ z) * (R ∙ z) = n * n'} := by
  rw [Submodule.span_mul_span, Set.singleton_mul]
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h
    refine ⟨w / α, ?_, by field_simp⟩
    rw [← sqRoots_iff hα, mul_div_cancel₀ _ hα]
    exact h
  · rintro ⟨z, hz, rfl⟩
    exact (sqRoots_iff hα n n' z).2 hz

lemma div_span_mul_cancel {c : F} (hc : c ≠ 0) (N D : Submodule R F) :
    ((R ∙ c) * N) / ((R ∙ c) * D) = N / D := by
  ext z
  rw [Submodule.mem_div_iff_forall_mul_mem, Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h w hw
    have := h (c * w) (Submodule.mul_mem_mul (mem_span_singleton_self c) hw)
    rw [← mul_assoc, mul_comm z c, mul_assoc] at this
    exact (mul_mem_span_mul_iff hc).1 this
  · intro h w hw
    obtain ⟨d, hd, rfl⟩ := mem_span_singleton_mul_iff'.1 hw
    rw [mul_left_comm]
    exact Submodule.mul_mem_mul (mem_span_singleton_self c) (h d hd)

end FundAux

/-- **93:23 (c)** (O'Meara 1963, §93E, 93:23, p. 266): $\mathfrak f_i^\alpha = \mathfrak f_i$, scaling the form
by $\alpha \ne 0$ does not change the ideals $\mathfrak f_i$. In the defining equation every term of $\mathfrak
s_i^2\mathfrak f_i$ is multiplied by $\alpha^2$: $\mathfrak d(\alpha^2\xi) = \alpha^2\mathfrak d(\xi)$ (63A), the
square roots $z$ with $(z\mathfrak o)^2 = \mathfrak n\mathfrak n'$ scale by $\alpha$, and $\mathfrak s_i$ by $\alpha$. -/
@[kb "omeara1963" "§93E, 93:23, p. 266"]
theorem fIdeal_smul_form {α : F} (hα : α ≠ 0) (L : Submodule R V) {t : ℕ} (Ls : Fin t → Submodule R V)
    (i j : Fin t) : fIdeal (α • Q) L Ls i j = fIdeal Q L Ls i j := by
  unfold fIdeal fIdealOf
  rw [fundNormGroup_smul_form Q hα, fundNormGroup_smul_form Q hα, fundNormIdeal_smul_form Q hα,
    fundNormIdeal_smul_form Q hα, scale_smul_form, smul_eq_span_mul α (fundNormIdeal Q L Ls i),
    smul_eq_span_mul α (fundNormIdeal Q L Ls j), defect_iSup_smul, sqRoots_span_smul hα]
  have e1 : (R ∙ α ^ 2) = (R ∙ α) * (R ∙ α) := by rw [span_mul_span', _root_.sq]
  have e2 : (2 : F) • ((R ∙ α) * span R {z : F | (R ∙ z) * (R ∙ z) = fundNormIdeal Q L Ls i * fundNormIdeal Q L Ls j} *
      ((R ∙ α) * scale Q (Ls i))) =
      (R ∙ α ^ 2) * ((2 : F) • (span R {z : F | (R ∙ z) * (R ∙ z) = fundNormIdeal Q L Ls i * fundNormIdeal Q L Ls j} *
      scale Q (Ls i))) := by
    rw [e1, mul_smul_comm]
    congr 1
    ring
  rw [e2, ← Submodule.mul_sup]
  have e3 : ((R ∙ α) * scale Q (Ls i)) * ((R ∙ α) * scale Q (Ls i)) =
      (R ∙ α ^ 2) * (scale Q (Ls i) * scale Q (Ls i)) := by rw [e1]; ring
  rw [e3]
  exact div_span_mul_cancel (pow_ne_zero 2 hα) _ _

/-- **93:23 (d)** (O'Meara 1963, §93E, 93:23, p. 266): $L = L_1 \perp \cdots \perp L_t$ is saturated on $V$ if and
only if it is saturated on $V^\alpha$ ($\alpha \ne 0$): $\mathfrak g(L_i^\alpha) = \alpha\mathfrak gL_i$ and $\mathfrak
g_i^\alpha = \alpha\mathfrak g_i$. -/
@[kb "omeara1963" "§93E, 93:23, p. 266"]
theorem isSaturated_smul_form_iff {α : F} (hα : α ≠ 0) {L : Submodule R V} {t : ℕ}
    {Ls : Fin t → Submodule R V} : IsSaturated (α • Q) L Ls ↔ IsSaturated Q L Ls := by
  unfold IsSaturated
  rw [isJordanSplitting_smul_form_iff Q hα]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  rw [normGroup_smul_form, fundNormGroup_smul_form Q hα]
  exact (AddSubgroup.map_injective (f := AddMonoidHom.mulLeft α)
    (mul_right_injective₀ hα)).eq_iff

end ScaleFormF

section Even93

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)] {π : R}
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

namespace FundAux

lemma mem_span_of_add (hπ : Irreducible π) {u η x : F} (h : x ∈ R ∙ (u + η)) (hn : x ∉ R ∙ η) :
    x ∈ R ∙ u := by
  by_cases hη : η = 0
  · subst hη; simpa using h
  have hx : x ≠ 0 := by rintro rfl; exact hn (zero_mem _)
  have hs : u + η ≠ 0 := by
    intro h0
    rw [h0] at h
    simp only [Submodule.span_zero_singleton, Submodule.mem_bot] at h
    exact hx h
  have h1 := (mem_span_iff hπ hx hs).1 h
  have h2 : dord hπ x < dord hπ η := by
    by_contra hc; exact hn ((mem_span_iff hπ hx hη).2 (not_lt.1 hc))
  have hu : u ≠ 0 := by
    rintro rfl; rw [zero_add] at h1; omega
  have h3 : dord hπ u < dord hπ η := by
    by_contra hc
    have := dord_add_ge hπ hu hη hs
    rw [min_eq_right (not_lt.1 hc)] at this
    omega
  have h4 := dord_add_of_lt hπ hu hη hs h3
  exact (mem_span_iff hπ hx hu).2 (by omega)

/-- **$\mathfrak d(\xi + \eta) \subseteq \mathfrak d(\xi) + \eta\mathfrak o$** (O'Meara 1963, §63A, p. 160). -/
lemma quadDefect_add_le (hπ : Irreducible π) (ξ η : F) :
    quadDefect R (ξ + η) ≤ quadDefect R ξ ⊔ R ∙ η := by
  intro z hz
  by_cases hzη : z ∈ R ∙ η
  · exact Submodule.mem_sup_right hzη
  · refine Submodule.mem_sup_left ?_
    rw [quadDefect, Submodule.mem_iInf]
    intro θ
    rw [quadDefect, Submodule.mem_iInf] at hz
    have h := hz θ
    rw [show ξ + η - θ ^ 2 = (ξ - θ ^ 2) + η by ring] at h
    exact mem_span_of_add hπ h hzη

lemma quadDefect_eq_span_of_odd (hπ : Irreducible π) {ξ : F} (hξ : ξ ≠ 0) (h : Odd (dord hπ ξ)) :
    quadDefect R ξ = R ∙ ξ := by
  obtain ⟨u, hu, hu'⟩ := dord_spec hπ hξ
  have hq := quadDefect_of_odd (F := F) hπ hu h
  rw [← hu'] at hq
  exact hq

lemma dord_pi (hπ : Irreducible π) : dord hπ (algebraMap R F π) = 1 :=
  dord_eq hπ (u := 1) isUnit_one (k := 1) (by simp)

/-- The "odd trick": if $\mathfrak d(a\beta) \subseteq D$ for $\beta$ and $\pi\beta$, then $a\pi\beta \in D$, since
one of $a\beta$, $a\pi\beta$ has odd order, and $\mathfrak d(\xi) = \xi\mathfrak o$ for odd order. -/
lemma mul_pi_mem_of_defect (hπ : Irreducible π) {a ν : F} {D : Submodule R F} {B : F → Prop}
    (hD : ∀ β : F, B β → quadDefect R (a * β) ≤ D) (hν : B ν) (hπν : B (algebraMap R F π * ν)) :
    a * (algebraMap R F π * ν) ∈ D := by
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  by_cases h0 : a * ν = 0
  · have : a * (algebraMap R F π * ν) = algebraMap R F π * (a * ν) := by ring
    rw [this, h0, mul_zero]; exact zero_mem _
  have ha0 : a ≠ 0 := left_ne_zero_of_mul h0
  have hν0 : ν ≠ 0 := right_ne_zero_of_mul h0
  have e : a * (algebraMap R F π * ν) = algebraMap R F π * (a * ν) := by ring
  rcases Int.even_or_odd (dord hπ (a * ν)) with he | ho
  · have hne : a * (algebraMap R F π * ν) ≠ 0 := mul_ne_zero ha0 (mul_ne_zero hpi hν0)
    have hodd : Odd (dord hπ (a * (algebraMap R F π * ν))) := by
      rw [e, dord_mul hπ hpi h0, dord_pi hπ]
      rw [add_comm]; exact he.add_one
    have := hD _ hπν
    rw [quadDefect_eq_span_of_odd hπ hne hodd] at this
    exact this (mem_span_singleton_self _)
  · have := hD _ hν
    rw [quadDefect_eq_span_of_odd hπ h0 ho] at this
    have h1 : a * (algebraMap R F π * ν) ∈ R ∙ (a * ν) :=
      mem_span_singleton.2 ⟨π, by rw [e, Algebra.smul_def]⟩
    exact this h1

lemma smul_weight_le (hπ : Irreducible π) {M : Submodule R V} {a : F} {D : Submodule R F}
    (hD : ∀ β ∈ normGroup Q M, quadDefect R (a * β) ≤ D) (hE : a • ((2 : F) • scale Q M) ≤ D) :
    a • weight Q M ≤ D := by
  have hT : Submodule.map (Algebra.linearMap R F) (maximalIdeal R) * normGroupIdeal Q M ≤
      Submodule.comap (LinearMap.mulLeft R a) D := by
    rw [Submodule.mul_le]
    rintro _ ⟨r0, hr0, rfl⟩ ν hν
    rw [hπ.maximalIdeal_eq] at hr0
    obtain ⟨r1, rfl⟩ := Ideal.mem_span_singleton'.1 hr0
    have hν' : ν ∈ normGroup Q M := normGroupIdeal_subset Q M hν
    have hπν : algebraMap R F π * ν ∈ normGroup Q M := by
      have : algebraMap R F π * ν = π • ν := by rw [Algebra.smul_def]
      rw [this]; exact normGroupIdeal_subset Q M (smul_mem _ π hν)
    have key := mul_pi_mem_of_defect hπ (B := fun β => β ∈ normGroup Q M) hD hν' hπν
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, Algebra.linearMap_apply, map_mul]
    have : a * (algebraMap R F r1 * algebraMap R F π * ν) = r1 • (a * (algebraMap R F π * ν)) := by
      rw [Algebra.smul_def]; ring
    rw [this]; exact D.smul_mem r1 key
  unfold weight
  rw [Submodule.add_eq_sup, smul_sup']
  refine sup_le ?_ hE
  intro z hz
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
  have := hT hy
  simpa using this

lemma mul_mem_smul_pointwise (c z : F) (N : Submodule R F) (hz : z ∈ N) : c * z ∈ c • N := by
  simpa using Submodule.smul_mem_pointwise_smul z c N hz

/-- $u_i \le u_j$ for $i \le j$ ($\mathfrak g_j \subseteq \mathfrak g_i$, O'Meara 1963, §93E, p. 263). -/
lemma dord_gen_le (hπ : Irreducible π) {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) {i j : Fin t}
    (hij : i ≤ j) : dord hπ (a i) ≤ dord hπ (a j) := by
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha i
  have haj := fundNormGenerator_ne_zero Q hfg hJ ha j
  have h1 : a j ∈ R ∙ a i :=
    (ha i).2 ▸ normGroup_subset_normIdeal Q _ (fundNormGroup_antitone Q hJ hij (ha j).1)
  exact (mem_span_iff hπ haj hai).1 h1

/-- **93:25 in terms of orders** (O'Meara 1963, §93E, p. 267): for $i \le j$ with $\mathfrak s_i = \sigma\mathfrak o$,
$\mathfrak s_j = \tau\mathfrak o$: $u_j \le u_i + 2(\operatorname{ord}\tau - \operatorname{ord}\sigma)$, i.e.
$\mathfrak s_i^{-2}a_i\mathfrak o \subseteq \mathfrak s_j^{-2}a_j\mathfrak o$. -/
lemma ord_scale_ineq (hπ : Irreducible π) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) {i j : Fin t} (hij : i ≤ j) {σ τ : F}
    (hσ : scale Q (Ls i) = R ∙ σ) (hτ : scale Q (Ls j) = R ∙ τ) :
    dord hπ (a j) ≤ dord hπ (a i) + 2 * (dord hπ τ - dord hπ σ) := by
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha i
  have haj := fundNormGenerator_ne_zero Q hfg hJ ha j
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  obtain ⟨k, hk, hkd⟩ := exists_scale_eq_pow_mul Q hπ hJ hij hσ hτ
  have hc : scale Q (Ls j) = (R ∙ algebraMap R F (π ^ k)) * scale Q (Ls i) := by
    rw [map_pow, ← zpow_natCast]; exact hk
  have h1 : algebraMap R F (π ^ k) ^ 2 * a i ∈ R ∙ a j :=
    (ha j).2 ▸ normGroup_subset_normIdeal Q _ (sq_mul_mem_fundNormGroup Q hfg hJ hc (ha i).1)
  have hpk : algebraMap R F (π ^ k) = algebraMap R F π ^ (k : ℤ) := by rw [map_pow, zpow_natCast]
  have hpk0 : algebraMap R F (π ^ k) ≠ 0 := by rw [hpk]; exact zpow_ne_zero _ hpi
  have hne : algebraMap R F (π ^ k) ^ 2 * a i ≠ 0 := mul_ne_zero (pow_ne_zero 2 hpk0) hai
  have h2 := (mem_span_iff hπ hne haj).1 h1
  rw [dord_mul hπ (pow_ne_zero 2 hpk0) hai, dord_sq hπ hpk0, hpk, dord_zpow] at h2
  omega

end FundAux

end Even93

section Even93Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
  {π : R}
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **93:26, even case** (O'Meara 1963, §93E, 93:26, p. 267): let $F$ be dyadic, $L$ a finitely generated regular
lattice with Jordan splitting and fundamental norm generators $a_i$, $\mathfrak s_i = \sigma\mathfrak o$,
$u_i = \operatorname{ord} a_i$, $s_i = \operatorname{ord}\sigma$. If $u_i + u_{i+1}$ is even then
$$\mathfrak s_i^2\mathfrak f_i = \mathfrak d(a_ia_{i+1}) + a_i\mathfrak w_{i+1} + a_{i+1}\mathfrak w_i +
2\mathfrak p^{\frac12(u_i+u_{i+1}) + s_i}.$$
(Indices $0$-based, `j = i + 1`; $2\mathfrak p^k = (2\pi^k)\mathfrak o$.) Proof: by the defining equation
(`mul_fIdealOf_even`) and 93:4 ($\mathfrak g_i = a_i\mathfrak o^2 + \mathfrak w_i$), using
$\mathfrak d(\xi + \eta) \subseteq \mathfrak d(\xi) + \eta\mathfrak o$, $\mathfrak d(\varepsilon^2\xi) \subseteq
\mathfrak d(\xi)$, $\mathfrak w_i \subseteq a_i\mathfrak o$ for "$\subseteq$"; for "$\supseteq$": the odd-order trick
($\mathfrak d(\xi) = \xi\mathfrak o$ if $\operatorname{ord}\xi$ is odd, applied to $a_i\beta$ or $a_i\pi\beta$,
$\beta \in \mathfrak m_{i+1}$) gives $a_i\mathfrak p\mathfrak m_{i+1} \subseteq \sum\mathfrak d(\alpha\beta)$, and
$2a_i\mathfrak s_{i+1}$, $2a_{i+1}\mathfrak s_i$ lie in $2\mathfrak p^{\frac12(u_i+u_{i+1})+s_i}$ because of 93:25
($u_{i+1} - 2s_{i+1} \le u_i - 2s_i$, `ord_scale_ineq`) and $u_i \le u_{i+1}$. -/
@[kb "omeara1963" "§93E, 93:26, p. 267 (u_i + u_{i+1} even)"]
theorem mul_fIdeal_of_even (hπ : Irreducible π) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls)
    {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t) (hij : (j : ℕ) = i + 1) {σ : F}
    (hσ : scale Q (Ls i) = R ∙ σ) (heven : Even (dord hπ (a i) + dord hπ (a j))) :
    scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j =
      quadDefect R (a i * a j) ⊔ (a i) • fundWeight Q L Ls j ⊔ (a j) • fundWeight Q L Ls i ⊔
        R ∙ (2 * algebraMap R F π ^ ((dord hπ (a i) + dord hπ (a j)) / 2 + dord hπ σ)) := by
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  have hLs : ∀ k, Ls k ≤ L := fun k => hJ.split.iSup_eq ▸ le_iSup Ls k
  obtain ⟨τ, hτ0, hτ⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (FG.of_le hfg (hLs j)))
    (hJ.modular j).1
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    exact (hJ.modular i).1 ((hJ.modular i).2.1.symm.trans (by rw [hσ]; simp))
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha i
  have haj := fundNormGenerator_ne_zero Q hfg hJ ha j
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  have key : fIdeal Q L Ls i j = fIdealOf R (R ∙ σ) (fundNormGroup Q L Ls i) (fundNormGroup Q L Ls j)
      (R ∙ a i) (R ∙ a j) := by
    unfold fIdeal fundNormIdeal; rw [hσ, (ha i).2, (ha j).2]
  rw [hσ, key, mul_fIdealOf_even hπ hσ0 hai haj heven]
  have hu1 := FundAux.dord_gen_le Q hπ hfg hJ ha hij'
  have hu2 := FundAux.ord_scale_ineq Q hπ hfg hJ ha hij' hσ hτ
  obtain ⟨m, hm⟩ := heven
  -- the two terms `2 a_i 𝔰_{i+1}` and `2 a_{i+1} 𝔰_i` lie in `E`
  have hE1 : a i • ((2 : F) • scale Q (fundSub Q L Ls j)) ≤
      R ∙ (2 * algebraMap R F π ^ ((dord hπ (a i) + dord hπ (a j)) / 2 + dord hπ σ)) := by
    rw [scale_fundSub Q hfg hJ, hτ, FIdealAux.smul_span_singleton, FIdealAux.smul_span_singleton,
      Submodule.span_singleton_le_iff_mem]
    have hne : a i * (2 * τ) ≠ 0 := mul_ne_zero hai (mul_ne_zero h2F hτ0)
    have hne2 : 2 * algebraMap R F π ^ ((dord hπ (a i) + dord hπ (a j)) / 2 + dord hπ σ) ≠ 0 :=
      mul_ne_zero h2F (zpow_ne_zero _ hpi)
    rw [mem_span_iff hπ hne hne2, dord_mul hπ h2F (zpow_ne_zero _ hpi), dord_zpow,
      dord_mul hπ hai (mul_ne_zero h2F hτ0), dord_mul hπ h2F hτ0]
    omega
  have hE2 : a j • ((2 : F) • scale Q (fundSub Q L Ls i)) ≤
      R ∙ (2 * algebraMap R F π ^ ((dord hπ (a i) + dord hπ (a j)) / 2 + dord hπ σ)) := by
    rw [scale_fundSub Q hfg hJ, hσ, FIdealAux.smul_span_singleton, FIdealAux.smul_span_singleton,
      Submodule.span_singleton_le_iff_mem]
    have hne : a j * (2 * σ) ≠ 0 := mul_ne_zero haj (mul_ne_zero h2F hσ0)
    have hne2 : 2 * algebraMap R F π ^ ((dord hπ (a i) + dord hπ (a j)) / 2 + dord hπ σ) ≠ 0 :=
      mul_ne_zero h2F (zpow_ne_zero _ hpi)
    rw [mem_span_iff hπ hne hne2, dord_mul hπ h2F (zpow_ne_zero _ hpi), dord_zpow,
      dord_mul hπ haj (mul_ne_zero h2F hσ0), dord_mul hπ h2F hσ0]
    omega
  -- representation of the fundamental norm groups (93:4)
  have rep : ∀ k : Fin t, ∀ z ∈ fundNormGroup Q L Ls k,
      ∃ ε : R, ∃ w ∈ fundWeight Q L Ls k, z = a k * algebraMap R F ε ^ 2 + w := by
    intro k z hz
    have h := fundNormGroup_eq_sq_add Q h2p hfg hreg hJ k (ha k)
    have hz' : z ∈ (fundNormGroup Q L Ls k : Set F) := hz
    rw [h] at hz'
    exact hz'
  have hwle : ∀ k : Fin t, ∀ w ∈ fundWeight Q L Ls k, w ∈ R ∙ a k := fun k w hw => by
    rw [(ha k).2]; exact (weight_bounds Q (fundSub Q L Ls k)).2.2.2 hw
  set E := R ∙ (2 * algebraMap R F π ^ ((dord hπ (a i) + dord hπ (a j)) / 2 + dord hπ σ)) with hEdef
  set D := ⨆ (α : F) (_ : α ∈ fundNormGroup Q L Ls i) (β : F) (_ : β ∈ fundNormGroup Q L Ls j),
    quadDefect R (α * β) with hDdef
  have hdef : quadDefect R (a i * a j) ≤ D :=
    le_iSup_of_le (a i) <| le_iSup_of_le (ha i).1 <| le_iSup_of_le (a j) <| le_iSup_of_le (ha j).1 le_rfl
  have hw1 : a i • fundWeight Q L Ls j ≤ D ⊔ E :=
    FundAux.smul_weight_le Q hπ (M := fundSub Q L Ls j) (a := a i) (D := D ⊔ E)
      (fun β hβ => le_sup_of_le_left
        (le_iSup_of_le (a i) <| le_iSup_of_le (ha i).1 <| le_iSup_of_le β <| le_iSup_of_le hβ le_rfl))
      (hE1.trans le_sup_right)
  have hw2 : a j • fundWeight Q L Ls i ≤ D ⊔ E :=
    FundAux.smul_weight_le Q hπ (M := fundSub Q L Ls i) (a := a j) (D := D ⊔ E)
      (fun β hβ => le_sup_of_le_left (by
        rw [mul_comm]
        exact le_iSup_of_le β <| le_iSup_of_le hβ <| le_iSup_of_le (a j) <| le_iSup_of_le (ha j).1 le_rfl))
      (hE2.trans le_sup_right)
  have hDle : D ≤ quadDefect R (a i * a j) ⊔ a i • fundWeight Q L Ls j ⊔ a j • fundWeight Q L Ls i := by
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
    obtain ⟨ε, w, hw, rfl⟩ := rep i x hx
    obtain ⟨η, w', hw', rfl⟩ := rep j y hy
    have e : (a i * algebraMap R F ε ^ 2 + w) * (a j * algebraMap R F η ^ 2 + w') =
        algebraMap R F (ε * η) ^ 2 * (a i * a j) +
          (a i * (algebraMap R F ε ^ 2 * w') + (a j * (algebraMap R F η ^ 2 * w) + w * w')) := by
      rw [map_mul]; ring
    have hw1' : algebraMap R F ε ^ 2 * w' ∈ fundWeight Q L Ls j := by
      have := (fundWeight Q L Ls j).smul_mem (ε ^ 2) hw'
      rwa [Algebra.smul_def, map_pow] at this
    have hw2' : algebraMap R F η ^ 2 * w ∈ fundWeight Q L Ls i := by
      have := (fundWeight Q L Ls i).smul_mem (η ^ 2) hw
      rwa [Algebra.smul_def, map_pow] at this
    have hw3 : w * w' ∈ a i • fundWeight Q L Ls j := by
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hwle i w hw)
      have : w * w' = a i * (r • w') := by
        rw [← hr, Algebra.smul_def, Algebra.smul_def]; ring
      rw [this]
      exact FundAux.mul_mem_smul_pointwise _ _ _ ((fundWeight Q L Ls j).smul_mem r hw')
    have hB : (a i * (algebraMap R F ε ^ 2 * w') + (a j * (algebraMap R F η ^ 2 * w) + w * w')) ∈
        a i • fundWeight Q L Ls j ⊔ a j • fundWeight Q L Ls i := by
      refine add_mem (Submodule.mem_sup_left (FundAux.mul_mem_smul_pointwise _ _ _ hw1')) ?_
      exact add_mem (Submodule.mem_sup_right (FundAux.mul_mem_smul_pointwise _ _ _ hw2'))
        (Submodule.mem_sup_left hw3)
    rw [e]
    refine (FundAux.quadDefect_add_le hπ _ _).trans (sup_le ?_ ?_)
    · rw [quadDefect_sq_mul]
      refine le_sup_of_le_left (le_sup_of_le_left ?_)
      have h1 : R ∙ (algebraMap R F (ε * η) ^ 2) ≤ (1 : Submodule R F) :=
        (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_one.2 ⟨(ε * η) ^ 2, by simp⟩)
      calc _ ≤ (1 : Submodule R F) * quadDefect R (a i * a j) := mul_le_mul' h1 le_rfl
        _ = _ := one_mul _
    · rw [Submodule.span_singleton_le_iff_mem]
      have hs : (a i • fundWeight Q L Ls j ⊔ a j • fundWeight Q L Ls i) ≤
          quadDefect R (a i * a j) ⊔ a i • fundWeight Q L Ls j ⊔ a j • fundWeight Q L Ls i :=
        sup_le (le_sup_of_le_left le_sup_right) le_sup_right
      exact hs hB
  apply le_antisymm
  · exact sup_le (hDle.trans le_sup_left) le_sup_right
  · exact sup_le (sup_le (sup_le (hdef.trans le_sup_left) hw1) hw2) le_sup_right

namespace FundAux

lemma quadDefect_sq_eq_bot (θ : F) : quadDefect R (θ ^ 2) = ⊥ :=
  eq_bot_iff.2 ((iInf_le _ θ).trans (by simp))

lemma fund_rep (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (k : Fin t) {z : F} (hz : z ∈ fundNormGroup Q L Ls k) :
    ∃ ε : R, ∃ w ∈ fundWeight Q L Ls k, z = a k * algebraMap R F ε ^ 2 + w := by
  have h := fundNormGroup_eq_sq_add Q h2p hfg hreg hJ k (ha k)
  have hz' : z ∈ (fundNormGroup Q L Ls k : Set F) := hz
  rw [h] at hz'
  exact hz'

/-- If $b \ne 0$, $\mathfrak s_k = \sigma\mathfrak o$ and $\operatorname{ord} b + \operatorname{ord}\sigma \le n$, then
$2\pi^n\mathfrak o \subseteq b\mathfrak w_k$ (since $2\mathfrak s_k \subseteq \mathfrak w_k$). -/
lemma span_two_le_smul_weight (hπ : Irreducible π) {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V}
    (hfg : L.FG) (hJ : IsJordanSplitting Q L Ls) (k : Fin t) {σ : F} (hσ : scale Q (Ls k) = R ∙ σ)
    (hσ0 : σ ≠ 0) {b : F} (hb : b ≠ 0) (n : ℤ) (hn : dord hπ b + dord hπ σ ≤ n) :
    R ∙ (2 * algebraMap R F π ^ n) ≤ b • fundWeight Q L Ls k := by
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  have h1 : R ∙ (2 * algebraMap R F π ^ n) ≤ R ∙ (b * (2 * σ)) := by
    rw [Submodule.span_singleton_le_iff_mem]
    have hne : 2 * algebraMap R F π ^ n ≠ 0 := mul_ne_zero h2F (zpow_ne_zero _ hpi)
    have hne2 : b * (2 * σ) ≠ 0 := mul_ne_zero hb (mul_ne_zero h2F hσ0)
    rw [mem_span_iff hπ hne hne2, dord_mul hπ hb (mul_ne_zero h2F hσ0), dord_mul hπ h2F hσ0,
      dord_mul hπ h2F (zpow_ne_zero _ hpi), dord_zpow]
    omega
  have h2 : b • ((2 : F) • scale Q (fundSub Q L Ls k)) ≤ b • weight Q (fundSub Q L Ls k) :=
    smul_mono_aux b (weight_bounds Q (fundSub Q L Ls k)).2.2.1
  rw [scale_fundSub Q hfg hJ, hσ, smul_span_singleton, smul_span_singleton] at h2
  exact h1.trans h2

end FundAux

/-- **93:27, $u_{i+1} \ge u_i$** (O'Meara 1963, §93E, 93:27, p. 267, "since $\mathfrak g_{i+1} \subseteq
\mathfrak g_i$"): for $i \le j$ the orders of fundamental norm generators satisfy $u_i \le u_j$. -/
@[kb "omeara1963" "§93E, 93:27, p. 267"]
theorem dord_fundNormGenerator_le (hπ : Irreducible π) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) {i j : Fin t} (hij : i ≤ j) : dord hπ (a i) ≤ dord hπ (a j) :=
  FundAux.dord_gen_le Q hπ hfg hJ ha hij

/-- **93:27, case $u_{i+1} = u_i$** (O'Meara 1963, §93E, 93:27, p. 267): $\mathfrak s_i^2\mathfrak f_i =
a_{i+1}\mathfrak w_i$. (Indices $0$-based, `j = i + 1`; same hypotheses as `mul_fIdeal_of_even`; proved from it:
$a_{i+1} \in \mathfrak g_i = a_i\mathfrak o^2 + \mathfrak w_i$ makes $\mathfrak d(a_ia_{i+1})$ lie in
$a_i\mathfrak w_i$, and $\mathfrak w_{i+1} \subseteq \mathfrak w_i$, $2\mathfrak s_i \subseteq \mathfrak w_i$.) -/
@[kb "omeara1963" "§93E, 93:27, p. 267"]
theorem mul_fIdeal_of_dord_eq (hπ : Irreducible π) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V}
    (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t)
    (hij : (j : ℕ) = i + 1) {σ : F} (hσ : scale Q (Ls i) = R ∙ σ)
    (hu : dord hπ (a j) = dord hπ (a i)) :
    scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j = a j • fundWeight Q L Ls i := by
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    exact (hJ.modular i).1 ((hJ.modular i).2.1.symm.trans (by rw [hσ]; simp))
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha i
  have haj := fundNormGenerator_ne_zero Q hfg hJ ha j
  rw [mul_fIdeal_of_even Q hπ h2p hfg hreg hJ ha i j hij hσ ⟨dord hπ (a i), by omega⟩]
  have hspan : R ∙ a i = R ∙ a j := span_eq_of_dord_eq hπ hai haj hu.symm
  have hsm : a i • fundWeight Q L Ls i = a j • fundWeight Q L Ls i := by
    rw [FundAux.smul_eq_span_mul, FundAux.smul_eq_span_mul, hspan]
  have hE := FundAux.span_two_le_smul_weight Q hπ hfg hJ i hσ hσ0 haj
    ((dord hπ (a i) + dord hπ (a j)) / 2 + dord hπ σ) (by omega)
  have hX : a i • fundWeight Q L Ls j ≤ a j • fundWeight Q L Ls i :=
    (FundAux.smul_mono_aux _ (fundWeight_antitone Q hJ hij')).trans hsm.le
  have hD : quadDefect R (a i * a j) ≤ a j • fundWeight Q L Ls i := by
    obtain ⟨ε, w, hw, hεw⟩ := FundAux.fund_rep Q h2p hfg hreg hJ ha i
      (fundNormGroup_antitone Q hJ hij' (ha j).1)
    have e : a i * a j = (a i * algebraMap R F ε) ^ 2 + a i * w := by
      conv_lhs => rw [hεw]
      ring
    rw [e]
    refine (FundAux.quadDefect_add_le hπ _ _).trans (sup_le ?_ ?_)
    · rw [FundAux.quadDefect_sq_eq_bot]; exact bot_le
    · rw [Submodule.span_singleton_le_iff_mem, ← hsm]
      exact FundAux.mul_mem_smul_pointwise _ _ _ hw
  apply le_antisymm
  · exact sup_le (sup_le (sup_le hD hX) le_rfl) hE
  · exact le_sup_of_le_left le_sup_right

/-- **93:27, case $u_{i+1} = u_i + 1$** (O'Meara 1963, §93E, 93:27, p. 267): $\mathfrak s_i^2\mathfrak f_i =
a_ia_{i+1}\mathfrak o$. This is the odd case of 93:26 (`mul_fIdeal_of_odd`; no dyadic hypothesis is needed). -/
@[kb "omeara1963" "§93E, 93:27, p. 267"]
theorem mul_fIdeal_of_dord_succ (hπ : Irreducible π) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t) (hu : dord hπ (a j) = dord hπ (a i) + 1) :
    scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j = R ∙ (a i * a j) :=
  mul_fIdeal_of_odd Q hπ hfg hJ ha i j ⟨dord hπ (a i), by omega⟩

/-- **93:27, case $u_{i+1} = u_i + 2$, $s_{i+1} = s_i + 1$** (O'Meara 1963, §93E, 93:27, p. 267): $\mathfrak
s_i^2\mathfrak f_i = a_i\mathfrak w_{i+1}$. Here $\mathfrak s_i = \sigma\mathfrak o$, $\mathfrak s_{i+1} = \tau\mathfrak
o$, $s_i = \operatorname{ord}\sigma$, $s_{i+1} = \operatorname{ord}\tau$. Proof as in O'Meara: by 93:25,
$\pi^2\mathfrak g_i \subseteq \mathfrak g_{i+1}$ and $\pi^2\mathfrak w_i \subseteq \mathfrak w_{i+1}$ (here
$\pi^{2(s_{i+1} - s_i)} = \pi^2$), so $\pi^2a_i$ is, up to a unit square plus weight, $a_{i+1}$; substituting in
93:26 (even case). -/
@[kb "omeara1963" "§93E, 93:27, p. 267"]
theorem mul_fIdeal_of_dord_add_two (hπ : Irreducible π) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V}
    (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t)
    (hij : (j : ℕ) = i + 1) {σ τ : F} (hσ : scale Q (Ls i) = R ∙ σ) (hτ : scale Q (Ls j) = R ∙ τ)
    (hu : dord hπ (a j) = dord hπ (a i) + 2) (hs : dord hπ τ = dord hπ σ + 1) :
    scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j = a i • fundWeight Q L Ls j := by
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    exact (hJ.modular i).1 ((hJ.modular i).2.1.symm.trans (by rw [hσ]; simp))
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact (hJ.modular j).1 ((hJ.modular j).2.1.symm.trans (by rw [hτ]; simp))
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha i
  have haj := fundNormGenerator_ne_zero Q hfg hJ ha j
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  rw [mul_fIdeal_of_even Q hπ h2p hfg hreg hJ ha i j hij hσ ⟨dord hπ (a i) + 1, by omega⟩]
  -- `s_j = π s_i`
  obtain ⟨k, hk, hkd⟩ := exists_scale_eq_pow_mul Q hπ hJ hij' hσ hτ
  have hk1 : k = 1 := by omega
  have hc : scale Q (Ls j) = (R ∙ algebraMap R F π) * scale Q (Ls i) := by
    rw [hk1] at hk; simpa using hk
  have hweight := fundWeight_sq_smul_le Q hfg hJ hc
  have hsq : ∀ {g : F}, g ∈ fundNormGroup Q L Ls i →
      algebraMap R F π ^ 2 * g ∈ fundNormGroup Q L Ls j :=
    fun hg => FundAux.sq_mul_mem_fundNormGroup Q hfg hJ hc hg
  -- `a j = r • (π² a i)`
  have hne : algebraMap R F π ^ 2 * a i ≠ 0 := mul_ne_zero (pow_ne_zero 2 hpi) hai
  obtain ⟨r, hr⟩ : ∃ r : R, r • (algebraMap R F π ^ 2 * a i) = a j := by
    refine mem_span_singleton.1 ((mem_span_iff hπ haj hne).2 ?_)
    rw [dord_mul hπ (pow_ne_zero 2 hpi) hai, dord_sq hπ hpi, FundAux.dord_pi hπ]
    omega
  have hmulw : ∀ y ∈ fundWeight Q L Ls i, ∀ r' : R, r' • (algebraMap R F π ^ 2 * y) ∈ fundWeight Q L Ls j :=
    fun y hy r' => (fundWeight Q L Ls j).smul_mem r' (by
      simpa using hweight (Submodule.smul_mem_pointwise_smul y (algebraMap R F π ^ 2) _ hy))
  have hE := FundAux.span_two_le_smul_weight Q hπ hfg hJ j hτ hτ0 hai
    ((dord hπ (a i) + dord hπ (a j)) / 2 + dord hπ σ) (by omega)
  have hX : a j • fundWeight Q L Ls i ≤ a i • fundWeight Q L Ls j := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    have : a j • y = a i * (r • (algebraMap R F π ^ 2 * y)) := by
      rw [← hr, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]; ring
    rw [this]
    exact FundAux.mul_mem_smul_pointwise _ _ _ (hmulw y hy r)
  have hD : quadDefect R (a i * a j) ≤ a i • fundWeight Q L Ls j := by
    obtain ⟨ε, w, hw, hεw⟩ := FundAux.fund_rep Q h2p hfg hreg hJ ha j (hsq (ha i).1)
    have e : a i * a j = (a j * algebraMap R F ε / algebraMap R F π) ^ 2 + a i * (r • w) := by
      have h2 : a j = algebraMap R F r * (algebraMap R F π ^ 2 * a i) := by
        rw [← hr, Algebra.smul_def]
      have hw' : w = algebraMap R F π ^ 2 * a i - a j * algebraMap R F ε ^ 2 := by
        linear_combination -hεw
      rw [Algebra.smul_def, hw', h2]
      field_simp
      ring
    rw [e]
    refine (FundAux.quadDefect_add_le hπ _ _).trans (sup_le ?_ ?_)
    · rw [FundAux.quadDefect_sq_eq_bot]; exact bot_le
    · rw [Submodule.span_singleton_le_iff_mem]
      exact FundAux.mul_mem_smul_pointwise _ _ _ ((fundWeight Q L Ls j).smul_mem r hw)
  apply le_antisymm
  · exact sup_le (sup_le (sup_le hD le_rfl) hX) hE
  · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)

end Even93Main

end QuadFormsKB.OMeara
