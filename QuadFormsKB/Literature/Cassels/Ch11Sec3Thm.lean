/-
# Cassels, Chapter 11, Theorem 3.1 and Corollary: $G = R/ST$ acts simply transitively on the spinor genera

**Layer:** $\mathbb Z$-lattices `Lat ℚ n` in $V = \mathbb Q^n$ with a regular form $Q$, $n \ge 3$; a finite set $P$ of
primes with Cassels' condition (3.7) (`hP`); Cassels' group $G$ = `CasselsG Q hQ L P` (`Ch11Sec3Group.lean`); the
spinor genus `SameProperSpinorGenus`.

**Defines** Cassels' action (3.32) (p. 211) as a relation, `CasselsAct g Γ Δ`: "$\Delta$ is in the spinor genus
$g\mathcal S_\Gamma$": there are $\Gamma'$ in the spinor genus of $\Gamma$ with $\Gamma'_p = \Lambda_p$ ($p \notin P$),
(3.28), and $\alpha \in O(V)(\mathbb A_f)$ with $\alpha_p \in O^+(V_p)$ ($p \in P$), $\alpha_p = 1$ ($p \notin P$), whose
spinor norms $\{\theta(\alpha_p)\}_{p\in P}$ represent $g$, such that $\Delta$ is in the spinor genus of $\alpha\Gamma'$
((3.29)–(3.31)).

**Proves** Cassels' Theorem 3.1 (pp. 211–212), for spinor genera in the genus of $\Lambda$: (i) $g\mathcal S_\Gamma$ is
defined (`casselsAct_exists`); (ii) $g_1\mathcal S_\Gamma = g_2\mathcal S_\Gamma$ only when $g_1 = g_2$
(`casselsAct_unique`); (iii) any two spinor genera satisfy $\mathcal S_\Delta = g\mathcal S_\Gamma$ for some $g$
(`casselsAct_transitive`); (iv) $g_1(g_2\mathcal S) = (g_1g_2)\mathcal S$ (`casselsAct_mul`); and the Corollary
(p. 212, `casselsAct_of_smul`): the definition does not depend on the choice of $\Lambda$ — for any $\Gamma$ in the genus
and $\Delta = \beta\Gamma$ with $\beta_p \in O^+(V_p)$ ($p \in P$), $\beta_p = 1$ ($p \notin P$), $\mathcal S_\Delta =
g\mathcal S_\Gamma$ with $g$ the image of $\{\theta(\beta_p)\}$. Over $\mathbb Q$ via Lemmas 3.4 and 3.5.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3GroupLemma34
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-- **Cassels' action (3.32)** (Ch. 11, p. 211), as a relation: $\Delta \in g\mathcal S_\Gamma$ (module docstring). -/
@[kb "cassels1978" "Ch. 11, (3.28)–(3.32), p. 211 (the action g𝒮_Γ, as a relation)"]
def CasselsAct (g : CasselsG Q hQ L P) (Γ Δ : Lat ℚ n) : Prop :=
  ∃ Γ' : Lat ℚ n, SameProperSpinorGenus Q Γ Γ' ∧ (∀ v, v ∉ P → loc v Γ'.1 = loc v L.1) ∧
    ∃ α : OAf Q, (∀ v ∈ P, α v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ)) ∧ (∀ v, v ∉ P → α v = 1) ∧
      ∃ x : CasselsR P, (∀ v : P, SqClass.mk (x v) = spinorNorm Q (v.1.adicCompletion ℚ) (α v)) ∧
        (QuotientGroup.mk x : CasselsG Q hQ L P) = g ∧ SameProperSpinorGenus Q Δ (latSMul Q α Γ')

/-- $\mathcal O_{\mathbb Q}$ is a principal ideal domain. -/
theorem pid_rat : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective

/-- The genus is stable under the adelic action. -/
theorem sameGenus_latSMul (α : OAf Q) (Γ : Lat ℚ n) : SameGenus Q Γ.1 (latSMul Q α Γ).1 := by
  have hmem : latSMul Q α Γ ∈ @MulAction.orbit (OAf Q) (Lat ℚ n) (latAction Q).toSMul Γ := ⟨α, rfl⟩
  rw [orbit_eq_genus Q Γ] at hmem
  exact hmem

/-- Every adelic rotation has local spinor norms represented by an element of $R$. -/
theorem exists_casselsR_rep (g : OAf Q) : ∃ z : CasselsR P,
    ∀ v : P, SqClass.mk (z v) = spinorNorm Q (v.1.adicCompletion ℚ) (g v.1) := by
  choose z hz using fun v : P => SqClass.ind
    (P := fun c : SqClass (v.1.adicCompletion ℚ) => ∃ a : (v.1.adicCompletion ℚ)ˣ, SqClass.mk a = c)
    (fun a => ⟨a, rfl⟩) (spinorNorm Q (v.1.adicCompletion ℚ) (g v.1))
  exact ⟨z, hz⟩

/-- Rotations supported on $P$ with prescribed local spinor norm classes (Lemma 3.1). -/
theorem exists_oaf_casselsLift (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (x : CasselsR P) :
    ∃ α : OAf Q, (∀ v, α v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ)) ∧ (∀ v, v ∉ P → α v = 1) ∧
      ∀ v : P, SqClass.mk (x v) = spinorNorm Q (v.1.adicCompletion ℚ) (α v.1) := by
  classical
  have hex : ∀ v : P, ∃ σ ∈ Tamagawa.soSub Q (v.1.adicCompletion ℚ),
      spinorNorm Q (v.1.adicCompletion ℚ) σ = SqClass.mk (x v) := fun v =>
    exists_soSub_spinorNorm_eq_local Q hQ hn v.1 (x v)
  choose σ hσ hσθ using hex
  obtain ⟨α, hα⟩ : ∃ α : OAf Q, ∀ v, α v = if h : v ∈ P then σ ⟨v, h⟩ else 1 :=
    ⟨⟨fun v => if h : v ∈ P then σ ⟨v, h⟩ else 1, by
      filter_upwards [P.eventually_cofinite_notMem] with v hv
      simp only [hv, ↓reduceDIte]
      exact (stdStab Q v).one_mem⟩, fun v => rfl⟩
  refine ⟨α, fun v => ?_, fun v hv => ?_, fun v => ?_⟩
  · by_cases hv : v ∈ P
    · rw [hα]; simp only [hv, ↓reduceDIte]; exact hσ _
    · rw [hα]; simp only [hv, ↓reduceDIte]; exact (Tamagawa.soSub Q _).one_mem
  · rw [hα]; simp only [hv, ↓reduceDIte]
  · have : α v.1 = σ v := by rw [hα]; simp only [v.2, ↓reduceDIte]
    rw [this, hσθ]

/-- Rotations at $P$ and trivial elsewhere are rotations everywhere. -/
theorem soSub_of_P (α : OAf Q) (hα : ∀ v ∈ P, α v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ))
    (h1 : ∀ v, v ∉ P → α v = 1) : ∀ v, α v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ) := fun v => by
  by_cases hv : v ∈ P
  · exact hα v hv
  · rw [h1 v hv]; exact (Tamagawa.soSub Q _).one_mem

/-- Core of uniqueness: two shifted lattices in one spinor genus, from lattices in one spinor genus, have equal
classes in $G$. -/
theorem casselsAct_aux_eq (hQ : Q.Nondegenerate)
    (hP : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P → ∀ u : (v.adicCompletion ℚ)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    {Γ₁ Γ₂ : Lat ℚ n} (hΓ₁ : SameGenus Q L.1 Γ₁.1) (hΓ₂ : SameGenus Q L.1 Γ₂.1)
    (h1P : ∀ v, v ∉ P → loc v Γ₁.1 = loc v L.1) (h2P : ∀ v, v ∉ P → loc v Γ₂.1 = loc v L.1)
    (hΓ : SameProperSpinorGenus Q Γ₁ Γ₂) (α₁ α₂ : OAf Q)
    (hα₁ : ∀ v, α₁ v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ))
    (hα₂ : ∀ v, α₂ v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ))
    (hα₁P : ∀ v, v ∉ P → α₁ v = 1) (hα₂P : ∀ v, v ∉ P → α₂ v = 1)
    (x₁ x₂ : CasselsR P) (hx₁ : ∀ v : P, SqClass.mk (x₁ v) = spinorNorm Q (v.1.adicCompletion ℚ) (α₁ v))
    (hx₂ : ∀ v : P, SqClass.mk (x₂ v) = spinorNorm Q (v.1.adicCompletion ℚ) (α₂ v))
    (h : SameProperSpinorGenus Q (latSMul Q α₁ Γ₁) (latSMul Q α₂ Γ₂)) :
    (QuotientGroup.mk x₁ : CasselsG Q hQ L P) = QuotientGroup.mk x₂ := by
  classical
  have : IsPrincipalIdealRing (𝓞 ℚ) := pid_rat
  let _ : MulAction (OAf Q) (Lat ℚ n) := latAction Q
  obtain ⟨β₁, hβ₁, hβ₁1, rfl⟩ := exists_oaf_soSub_one hQ L P hΓ₁ h1P
  obtain ⟨β₂, hβ₂, hβ₂1, rfl⟩ := exists_oaf_soSub_one hQ L P hΓ₂ h2P
  obtain ⟨z₁, hz₁⟩ := exists_casselsR_rep Q P β₁
  obtain ⟨z₂, hz₂⟩ := exists_casselsR_rep Q P β₂
  have hker : ∀ g : OAf Q, (∀ v, v ∉ P → g v = 1) →
      ∀ v, v ∉ P → g v ∈ spinorKernel Q (v.adicCompletion ℚ) := fun g hg v hv => by
    rw [hg v hv]; exact (spinorKernel Q _).one_mem
  have h1 := (sameProperSpinorGenus_smul_iff_casselsG Q hQ L P hP β₁ β₂ hβ₁ hβ₂ (hker β₁ hβ₁1) (hker β₂ hβ₂1)
    z₁ z₂ hz₁ hz₂).mp hΓ
  have e1 : latSMul Q α₁ (latSMul Q β₁ L) = latSMul Q (α₁ * β₁) L := (mul_smul α₁ β₁ L).symm
  have e2 : latSMul Q α₂ (latSMul Q β₂ L) = latSMul Q (α₂ * β₂) L := (mul_smul α₂ β₂ L).symm
  rw [e1, e2] at h
  have hmul1 : ∀ v, v ∉ P → (α₁ * β₁) v = 1 := fun v hv => by
    change α₁ v * β₁ v = 1
    rw [hα₁P v hv, hβ₁1 v hv, mul_one]
  have hmul2 : ∀ v, v ∉ P → (α₂ * β₂) v = 1 := fun v hv => by
    change α₂ v * β₂ v = 1
    rw [hα₂P v hv, hβ₂1 v hv, mul_one]
  have h2 := (sameProperSpinorGenus_smul_iff_casselsG Q hQ L P hP (α₁ * β₁) (α₂ * β₂)
    (fun v => (Tamagawa.soSub Q _).mul_mem (hα₁ v) (hβ₁ v))
    (fun v => (Tamagawa.soSub Q _).mul_mem (hα₂ v) (hβ₂ v)) (hker _ hmul1) (hker _ hmul2)
    (x₁ * z₁) (x₂ * z₂) ?_ ?_).mp h
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, h1] at h2
    let _ : CommGroup (CasselsG Q hQ L P) := QuotientGroup.Quotient.commGroup _
    exact mul_right_cancel h2
  · intro v
    change SqClass.mk (x₁ v * z₁ v) = spinorNorm Q (v.1.adicCompletion ℚ) (α₁ v * β₁ v)
    rw [SqClass.mk_mul, hx₁ v, hz₁ v]
    exact (map_mul (spinorNormHom Q (v.1.adicCompletion ℚ) hQ) (α₁ v) (β₁ v)).symm
  · intro v
    change SqClass.mk (x₂ v * z₂ v) = spinorNorm Q (v.1.adicCompletion ℚ) (α₂ v * β₂ v)
    rw [SqClass.mk_mul, hx₂ v, hz₂ v]
    exact (map_mul (spinorNormHom Q (v.1.adicCompletion ℚ) hQ) (α₂ v) (β₂ v)).symm

variable (hn : 3 ≤ n)
  (hP : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P → ∀ u : (v.adicCompletion ℚ)ˣ,
    u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))

include hn hP

/-- **Cassels, Theorem 3.1 (i)** (Ch. 11, p. 211): *the spinor genus $g\mathcal S_\Gamma$ is defined for all $g \in G$
and every spinor genus $\mathcal S_\Gamma$ in the genus of $\Lambda$*, and lies in the genus. -/
@[kb "cassels1978" "Ch. 11, Thm. 3.1 (i), p. 211"]
theorem casselsAct_exists (g : CasselsG Q hQ L P) {Γ : Lat ℚ n} (hΓ : SameGenus Q L.1 Γ.1) :
    ∃ Δ : Lat ℚ n, SameGenus Q L.1 Δ.1 ∧ CasselsAct Q hQ L P g Γ Δ := by
  classical
  obtain ⟨Γ', hΓΓ', β, -, -, -, -, hΓ'P⟩ := exists_sameProperSpinorGenus_casselsForm_rat Q hQ hn L P hP hΓ
  have hΓ' : SameGenus Q L.1 Γ'.1 :=
    SameGenus.trans Q hΓ (SameSpinorGenus.sameGenus Q (SameProperSpinorGenus.sameSpinorGenus Q hΓΓ'))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨α, hα, hα1, hαx⟩ := exists_oaf_casselsLift Q P hQ hn x
  exact ⟨latSMul Q α Γ', SameGenus.trans Q hΓ' (sameGenus_latSMul Q α Γ'), Γ', hΓΓ', hΓ'P, α,
    fun v _ => hα v, hα1, x, hαx, rfl, SameProperSpinorGenus.refl Q _⟩

/-- **Cassels, Theorem 3.1 (ii)** (Ch. 11, p. 211): *$g_1\mathcal S_\Gamma = g_2\mathcal S_\Gamma$ only when
$g_1 = g_2$.* -/
@[kb "cassels1978" "Ch. 11, Thm. 3.1 (ii), p. 211"]
theorem casselsAct_unique {g₁ g₂ : CasselsG Q hQ L P} {Γ Δ : Lat ℚ n} (hΓ : SameGenus Q L.1 Γ.1)
    (h₁ : CasselsAct Q hQ L P g₁ Γ Δ) (h₂ : CasselsAct Q hQ L P g₂ Γ Δ) : g₁ = g₂ := by
  obtain ⟨Γ₁, hΓ₁, hP1, α₁, hα₁, hα₁1, x₁, hx₁, rfl, hΔ₁⟩ := h₁
  obtain ⟨Γ₂, hΓ₂, hP2, α₂, hα₂, hα₂1, x₂, hx₂, rfl, hΔ₂⟩ := h₂
  have hG₁ : SameGenus Q L.1 Γ₁.1 :=
    SameGenus.trans Q hΓ (SameSpinorGenus.sameGenus Q (SameProperSpinorGenus.sameSpinorGenus Q hΓ₁))
  have hG₂ : SameGenus Q L.1 Γ₂.1 :=
    SameGenus.trans Q hΓ (SameSpinorGenus.sameGenus Q (SameProperSpinorGenus.sameSpinorGenus Q hΓ₂))
  exact casselsAct_aux_eq Q L P hQ hP hG₁ hG₂ hP1 hP2
    (SameProperSpinorGenus.trans Q (SameProperSpinorGenus.symm Q hΓ₁) hΓ₂) α₁ α₂
    (soSub_of_P Q P α₁ hα₁ hα₁1) (soSub_of_P Q P α₂ hα₂ hα₂1) hα₁1 hα₂1 x₁ x₂ hx₁ hx₂
    (SameProperSpinorGenus.trans Q (SameProperSpinorGenus.symm Q hΔ₁) hΔ₂)

/-- **Cassels, Theorem 3.1 (iii)** (Ch. 11, p. 211): *if $\mathcal S_1, \mathcal S_2$ are any two spinor genera in the
genus, there is a $g \in G$ such that $\mathcal S_2 = g\mathcal S_1$.* -/
@[kb "cassels1978" "Ch. 11, Thm. 3.1 (iii), p. 211"]
theorem casselsAct_transitive {Γ Δ : Lat ℚ n} (hΓ : SameGenus Q L.1 Γ.1) (hΔ : SameGenus Q L.1 Δ.1) :
    ∃ g : CasselsG Q hQ L P, CasselsAct Q hQ L P g Γ Δ := by
  classical
  let _ : MulAction (OAf Q) (Lat ℚ n) := latAction Q
  obtain ⟨Γ', hΓΓ', β, rfl, hβ, -, hβ1, hΓ'P⟩ := exists_sameProperSpinorGenus_casselsForm_rat Q hQ hn L P hP hΓ
  obtain ⟨Δ', hΔΔ', δ, rfl, hδ, -, hδ1, -⟩ := exists_sameProperSpinorGenus_casselsForm_rat Q hQ hn L P hP hΔ
  obtain ⟨z, hz⟩ := exists_casselsR_rep Q P (δ * β⁻¹)
  have e : latSMul Q (δ * β⁻¹) (latSMul Q β L) = latSMul Q δ L := by
    change (δ * β⁻¹) • (β • L) = δ • L
    rw [← mul_smul, inv_mul_cancel_right]
  refine ⟨QuotientGroup.mk z, latSMul Q β L, hΓΓ', hΓ'P, δ * β⁻¹, fun v _ => ?_, fun v hv => ?_, z, hz, rfl, ?_⟩
  · exact (Tamagawa.soSub Q _).mul_mem (hδ v) ((Tamagawa.soSub Q _).inv_mem (hβ v))
  · change δ v * (β v)⁻¹ = 1
    rw [hδ1 v hv, hβ1 v hv]; simp
  · rw [e]; exact hΔΔ'

/-- **Cassels, Theorem 3.1 (iv)** (Ch. 11, p. 211): *$g_1(g_2\mathcal S) = (g_1g_2)\mathcal S$ for $g_1, g_2 \in G$.* -/
@[kb "cassels1978" "Ch. 11, Thm. 3.1 (iv), p. 211"]
theorem casselsAct_mul {g₁ g₂ : CasselsG Q hQ L P} {Γ Δ E : Lat ℚ n} (hΓ : SameGenus Q L.1 Γ.1)
    (h₂ : CasselsAct Q hQ L P g₂ Γ Δ) (h₁ : CasselsAct Q hQ L P g₁ Δ E) :
    CasselsAct Q hQ L P (g₁ * g₂) Γ E := by
  classical
  let _ : MulAction (OAf Q) (Lat ℚ n) := latAction Q
  obtain ⟨Γ', hΓΓ', hΓ'P, α₂, hα₂, hα₂1, x₂, hx₂, rfl, hΔ⟩ := h₂
  obtain ⟨Δ', hΔΔ', hΔ'P, α₁, hα₁, hα₁1, x₁, hx₁, rfl, hE⟩ := h₁
  have e : latSMul Q (α₁ * α₂) Γ' = latSMul Q α₁ (latSMul Q α₂ Γ') := mul_smul α₁ α₂ Γ'
  refine ⟨Γ', hΓΓ', hΓ'P, α₁ * α₂, fun v hv => (Tamagawa.soSub Q _).mul_mem (hα₁ v hv) (hα₂ v hv),
    fun v hv => ?_, x₁ * x₂, fun v => ?_, QuotientGroup.mk_mul _ _ _, ?_⟩
  · change α₁ v * α₂ v = 1
    rw [hα₁1 v hv, hα₂1 v hv, mul_one]
  · change SqClass.mk (x₁ v * x₂ v) = spinorNorm Q (v.1.adicCompletion ℚ) (α₁ v * α₂ v)
    rw [SqClass.mk_mul, hx₁ v, hx₂ v]
    exact (map_mul (spinorNormHom Q (v.1.adicCompletion ℚ) hQ) (α₁ v) (α₂ v)).symm
  · rw [e]
    exact SameProperSpinorGenus.trans Q hE (sameProperSpinorGenus_smul_left Q hQ α₁
      (SameProperSpinorGenus.trans Q (SameProperSpinorGenus.symm Q hΔΔ') hΔ))

/-- **Cassels, Theorem 3.1, Corollary** (Ch. 11, p. 212): *the definition of (3.32) is independent of the choice of
$\Lambda$ in its genus. More precisely: let $\Gamma$ be any lattice in the genus of $\Lambda$ (not necessarily satisfying
(3.28)) and let $\Delta$ be any lattice for which $\Delta_p = \beta_p\Gamma_p$, $\beta_p \in O^+(V_p)$ ($p \in P$),
$\Delta_p = \Gamma_p$ ($p \notin P$). Then $\mathcal S_\Delta = g\mathcal S_\Gamma$, where $g$ is the image of
$\{\theta(\beta_p)\}_{p\in P}$ in $G$.* -/
@[kb "cassels1978" "Ch. 11, Thm. 3.1, Cor., p. 212"]
theorem casselsAct_of_smul {Γ : Lat ℚ n} (hΓ : SameGenus Q L.1 Γ.1) (β : OAf Q)
    (hβ : ∀ v ∈ P, β v ∈ Tamagawa.soSub Q (v.adicCompletion ℚ)) (hβ1 : ∀ v, v ∉ P → β v = 1)
    (x : CasselsR P) (hx : ∀ v : P, SqClass.mk (x v) = spinorNorm Q (v.1.adicCompletion ℚ) (β v)) :
    CasselsAct Q hQ L P (QuotientGroup.mk x) Γ (latSMul Q β Γ) := by
  obtain ⟨Γ', hΓΓ', -, -, -, -, -, hΓ'P⟩ := exists_sameProperSpinorGenus_casselsForm_rat Q hQ hn L P hP hΓ
  exact ⟨Γ', hΓΓ', hΓ'P, β, hβ, hβ1, x, hx, rfl, sameProperSpinorGenus_smul_left Q hQ β hΓΓ'⟩

end QuadFormsKB.Lattices
