/-
# Global Eichler orders, place by place (Voight, 23.4.2, 23.4.19)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): 23.4.2 (p. 382),
Proposition 23.4.3 (p. 382), 23.4.19 (p. 385).

**Setting.** $F$ a number field, $B = (a,b)_F$ = `QuatF F a b` with $a, b \in \mathbb Z_F$ nonzero, orders are
`Subalgebra (𝓞 F) (QuatF F a b)`; for a finite place $v$, $\mathfrak o_v \subset F_v$ is the completion
(`v.adicCompletionIntegers F`, a discrete valuation ring with uniformizer $\pi_v$ = `LocalDensity.NF.π v`),
$B_v$ = `QuatV v a b` and $\mathcal O_v$ = `QuatOrder.localOrder` the completion of $\mathcal O$.
Global Eichler orders are the library's `IsEichlerOrder` and `IsEichlerOrderOfLevel`; local ones are the library's
`IsEichler` (Definition 23.4.1 for any algebra).

**Contents.**
* `IsEichler.map_algEquiv`: Eichler orders transport along algebra isomorphisms. Proved.
* `exists_algEquiv_localOrder_eq_stdEichlerOrder` (Proposition 23.4.3 at a split place, proved): if $B_v \cong \mathrm M_2(F_v)$
  and $\mathcal O_v$ is an Eichler order, then some isomorphism $B_v \cong \mathrm M_2(F_v)$ carries $\mathcal O_v$ onto the standard
  Eichler order $\mathcal O_0(\pi_v^e)$.
* `EichlerIsLocal F` (23.4.2): an order is Eichler iff all its completions are. Stated, not proved (the "if" direction
  needs the local-global dictionary for lattices, Theorem 9.4.9, in its existence form; the "only if" direction needs
  that completion commutes with intersection of lattices).
* `EichlerLocalLevel F` (23.4.19): an Eichler order of level $\mathfrak M$ has $\mathcal O_v$ maximal at $v \mid \mathfrak D$ and
  $\mathcal O_v \cong \mathcal O_0(\pi_v^{e_v})$, $e_v = \operatorname{ord}_v\mathfrak M$, at $v \nmid \mathfrak D$. Stated, not proved.
-/
import QuadFormsKB.Literature.Voight.Wave4.EichlerStructure
import QuadFormsKB.Literature.Voight.Wave2.Statements

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB.Voight.Wave4

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Quat

/-- **Eichler orders transport along algebra isomorphisms**: if $\varphi : A \cong A'$ is a $K$-algebra isomorphism and
$\mathcal O = \mathcal O_1 \cap \mathcal O_2$ is an Eichler order of $A$, then $\varphi(\mathcal O) = \varphi(\mathcal O_1) \cap \varphi(\mathcal O_2)$ is an
Eichler order of $A'$. -/
theorem IsEichler.map_algEquiv {R K A A' : Type*} [CommRing R] [Field K] [Algebra R K] [Ring A] [Algebra K A]
    [Algebra R A] [IsScalarTower R K A] [Ring A'] [Algebra K A'] [Algebra R A'] [IsScalarTower R K A']
    {O : Subalgebra R A} (hO : IsEichler R K O) (φ : A ≃ₐ[K] A') :
    IsEichler R K (O.map ((φ : A →ₐ[K] A').restrictScalars R)) := by
  obtain ⟨O₁, O₂, h₁, h₂, rfl⟩ := hO
  exact ⟨_, _, h₁.map φ, h₂.map φ, Algebra.map_inf _ φ.injective _ _⟩

section Local

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **Completions of Eichler orders at split places are standard** (Voight 2021, Proposition 23.4.3 and the sentence
after Definition 23.4.11, applied to $B_v \cong \mathrm M_2(F_v)$): if $B_v$ is split and the completion $\mathcal O_v$ is an
Eichler $\mathfrak o_v$-order, then there are an $F_v$-algebra isomorphism $\varphi : B_v \cong \mathrm M_2(F_v)$ and $e \ge 0$ with
$\varphi(\mathcal O_v) = \mathcal O_0(\pi_v^e)$. -/
@[kb "voight2021" "Proposition 23.4.3, p. 382"]
theorem exists_algEquiv_localOrder_eq_stdEichlerOrder {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsEichler 𝔬 Fv (localOrder (v := v) a b O))
    (hsplit : Nonempty (QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv)) :
    ∃ (φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv) (e : ℕ),
      (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) =
        stdEichlerOrder 𝔬 Fv (LocalDensity.NF.π v) e := by
  obtain ⟨φ₀⟩ := hsplit
  obtain ⟨e, P, Q, hPQ, hQP, heq⟩ :=
    localEichlerStructure (LocalDensity.NF.irreducible_π v) _ (IsEichler.map_algEquiv hO φ₀)
  refine ⟨φ₀.trans (conjAlgEquiv Q P hQP hPQ), e, ?_⟩
  ext x
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : φ₀ y ∈ (localOrder (v := v) a b O).map ((φ₀ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) :=
      ⟨y, hy, rfl⟩
    rw [heq, mem_map_conj] at h1
    exact h1
  · intro hx
    have h1 : P * x * Q ∈ (localOrder (v := v) a b O).map ((φ₀ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) := by
      rw [heq, mem_map_conj]
      rw [show Q * (P * x * Q) * P = x by
        simp only [← mul_assoc, hQP, one_mul]; rw [mul_assoc, hQP, mul_one]]
      exact hx
    obtain ⟨y, hy, hyx⟩ := h1
    refine ⟨y, hy, ?_⟩
    change Q * φ₀ y * P = x
    change φ₀ y = P * x * Q at hyx
    rw [hyx]
    simp only [← mul_assoc, hQP, one_mul]; rw [mul_assoc, hQP, mul_one]

end Local

/-! ### Statements -/

/-- **Being Eichler is a local property** (Voight 2021, 23.4.2), as a named proposition about the number field $F$: an
order $\mathcal O \subseteq B = (a,b)_F$ is an Eichler order (`IsEichlerOrder`, the intersection of two maximal orders) iff for
every finite place $v$ the completion $\mathcal O_v$ is an Eichler $\mathfrak o_v$-order of $B_v$. Stated, not proved. -/
@[kb "voight2021" "23.4.2, p. 382"]
def EichlerIsLocal (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O →
    (IsEichlerOrder O ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      IsEichler (v.adicCompletionIntegers F) (v.adicCompletion F) (localOrder (v := v) a b O))

/-- **The completions of an Eichler order of level $\mathfrak M$** (Voight 2021, 23.4.19), as a named proposition about the
number field $F$: let $\mathcal O \subseteq B = (a,b)_F$ be an Eichler order of level $\mathfrak M$ (`IsEichlerOrderOfLevel`:
$\operatorname{discrd}\mathcal O = \mathfrak D\mathfrak M$, $\mathfrak M$ coprime to $\mathfrak D$). Then at every finite place $v$:
if $v \mid \mathfrak D$ ($v \in \operatorname{Ram}_f B$) the completion $\mathcal O_v$ is the maximal order of $B_v$; if $v \nmid \mathfrak D$
there is an isomorphism $\varphi : B_v \cong \mathrm M_2(F_v)$ with $\varphi(\mathcal O_v) = \mathcal O_0(\pi_v^{e_v})$,
$e_v = \operatorname{ord}_v\mathfrak M$ (the multiplicity of $v$ among the prime factors of $\mathfrak M$). Stated, not proved. -/
@[kb "voight2021" "23.4.19, p. 385"]
def EichlerLocalLevel (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0) (O : Subalgebra (𝓞 F) (QuatF F a b)) (𝔐 : Ideal (𝓞 F)),
    IsEichlerOrderOfLevel ha hb O 𝔐 → ∀ v : HeightOneSpectrum (𝓞 F),
      (v ∈ ramFin ha hb → IsMaximalOrder (v.adicCompletionIntegers F) (v.adicCompletion F)
        (localOrder (v := v) a b O)) ∧
      (v ∉ ramFin ha hb → ∃ φ : QuatV v a b ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F),
        (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[v.adicCompletion F] _).restrictScalars
          (v.adicCompletionIntegers F)) =
          stdEichlerOrder (v.adicCompletionIntegers F) (v.adicCompletion F) (LocalDensity.NF.π v)
            ((UniqueFactorizationMonoid.normalizedFactors 𝔐).count v.asIdeal))

end QuadFormsKB.Voight.Wave4
