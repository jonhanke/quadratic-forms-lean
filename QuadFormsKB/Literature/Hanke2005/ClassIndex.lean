/-
# The classes in an indefinite genus as a quotient group (Shimura 1999, Lemma 2.4(3))

**Layer:** number fields; the double cosets `DC Q₀` $= SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ of
`ClassicalSetup.lean` and strong approximation for the spin group (`strongApproximationSpin`).

Hanke's Corollary 5.2 (thesis, p. 19) identifies the number $h$ of classes in the genus with the index
$[k^\times_{\mathbb A}:k^\times\sigma(D)]$, citing [Shi, Lemma 2.3(4)]. For $n\ge3$ and $G_a$ noncompact the statement is
Shimura's Lemma 2.4: (3) $GD$ is a normal subgroup of $G_{\mathbb A}$ and $G\backslash G_{\mathbb A}/D$ can be identified with
$G_{\mathbb A}/GD$; (4) the spinor norm $\sigma$ gives a bijection of $G\backslash G_{\mathbb A}/D$ onto $F^\times_{\mathbb A}/F^\times\sigma(D)$.

**Proves** (for the lattice $L = \mathcal O_F^n$, $Q_0$ nondegenerate, indefinite, $n\ge3$; finite-adelic form, $D = SO(\hat L)$):
* `classSub`: the subgroup $\Gamma_fK = SO(V)(F)\,SO(\hat L)$ of $SO(V)(\mathbb A_f)$ (it is a subgroup by strong approximation,
  `mem_Gamma_mul_KSO`);
* `spinorKernel_le_classSub`: it contains the rotations in the adelic spinor kernel $O'(V_{\mathbb A_f})$;
* `classSub_normal`: it is normal (it contains all commutators) — Shimura's Lemma 2.4(3), first half;
* `dcEquivQuot`: $SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)\simeq SO(V)(\mathbb A_f)/\Gamma_fK$ — Lemma 2.4(3), second half;
* `card_DC_eq_index`: the number of proper classes is the index $[SO(V)(\mathbb A_f):SO(V)(F)SO(\hat L)]$;
* `sq_mem_classSub`, `exists_card_DC_eq_two_pow`: the quotient has exponent $2$, so the number of proper classes is a power of $2$.

Lemma 2.4(4), the identification of $SO(V)(\mathbb A_f)/\Gamma_fK$ with the idèle class group
$F^\times_{\mathbb A}/F^\times\sigma(D)$ through the spinor norm, is proved in `Hanke2005/SpinorIdeleMain.lean`
(`shimuraLemma24_4`, `dcEquivIdele`, `card_DC_eq_index_idele`).

All unconditional, standard axioms only.
-/
import QuadFormsKB.Literature.Hanke2005.EqualMasses

open MeasureTheory MulAction Set NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005.EqualMasses

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- Strong approximation, direct form: a rotation $h$ in the adelic spinor kernel $O'(V_{\mathbb A_f})$ is $\gamma\kappa$ with
$\gamma\in SO(V)(F)$ and $\kappa\in SO(\hat L)$. -/
@[kb "omeara1963" "§104, 104:4, p. 315 (O'(V_A) ⊆ O'(V) O(L̂))"]
theorem exists_Gamma_KSO_of_spinorKernel (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF)
    (h : SOAf Q₀) (hh : (h : OAf QF) ∈ spinorKernelAf QF) :
    ∃ γ ∈ GammaSOAdele Q₀, ∃ κ ∈ KSO Q₀, h = γ.2 * κ := by
  have hQF : (QF).Nondegenerate := nondegenerate_map Q₀ hQ
  obtain ⟨γ0, hγ0, hstab⟩ := strongApproximationSpin.approx QF hn hQF hind (stdLat F n) _ hh
  have hdet : ((γ0 : GL (Fin n) F)).val.det = 1 := det_of_mem_spinorKernel QF hγ0
  let γs : soSub QF F := ⟨γ0, hdet⟩
  have hfin : (((diagSOAdele Q₀ γs).2 : SOAf Q₀) : OAf QF) = diagF QF γ0 := rfl
  refine ⟨diagSOAdele Q₀ γs, ⟨γs, rfl⟩, ((diagSOAdele Q₀ γs).2)⁻¹ * h, ?_, by group⟩
  rw [Subgroup.mem_subgroupOf]
  convert hstab using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hfin]

/-- **The subgroup $\Gamma_fK = SO(V)(F)\,SO(\hat L)$** of $SO(V)(\mathbb A_f)$ ($Q_0$ indefinite, $n\ge3$): the products
$\gamma k$, $\gamma\in SO(V)(F)$ (diagonally), $k\in SO(\hat L)$. Closed under products and inverses because
$K\Gamma_f\subseteq\Gamma_fK$ (strong approximation, `mem_Gamma_mul_KSO`). -/
@[kb "shimura1999" "Lemma 2.4(3), p. 8 (the group GD)"]
def classSub (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) : Subgroup (SOAf Q₀) where
  carrier := {g | ∃ γ ∈ GammaSOAdele Q₀, ∃ k ∈ KSO Q₀, g = γ.2 * k}
  one_mem' := ⟨1, (GammaSOAdele Q₀).one_mem, 1, (KSO Q₀).one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨γ1, hγ1, k1, hk1, rfl⟩ ⟨γ2, hγ2, k2, hk2, rfl⟩
    obtain ⟨γ', hγ', κ, hκ, he⟩ := mem_Gamma_mul_KSO Q₀ hn hQ hind 1 γ2.2 k1 hk1
    simp only [one_mul] at he
    refine ⟨γ1 * γ' * γ2, (GammaSOAdele Q₀).mul_mem ((GammaSOAdele Q₀).mul_mem hγ1 hγ') hγ2, κ * k2,
      (KSO Q₀).mul_mem hκ hk2, ?_⟩
    simp only [Prod.snd_mul]
    calc γ1.2 * k1 * (γ2.2 * k2) = γ1.2 * (k1 * γ2.2) * k2 := by group
      _ = γ1.2 * (γ'.2 * γ2.2 * κ) * k2 := by rw [he]
      _ = γ1.2 * γ'.2 * γ2.2 * (κ * k2) := by group
  inv_mem' := by
    rintro _ ⟨γ, hγ, k, hk, rfl⟩
    obtain ⟨γ', hγ', κ, hκ, he⟩ := mem_Gamma_mul_KSO Q₀ hn hQ hind 1 γ.2⁻¹ k⁻¹ ((KSO Q₀).inv_mem hk)
    simp only [one_mul] at he
    refine ⟨γ' * γ⁻¹, (GammaSOAdele Q₀).mul_mem hγ' ((GammaSOAdele Q₀).inv_mem hγ), κ, hκ, ?_⟩
    simp only [Prod.snd_mul, Prod.snd_inv, mul_inv_rev, he]

variable {Q₀} in
theorem mem_classSub {hn : 3 ≤ n} {hQ : Q₀.Nondegenerate} {hind : IsIndefinite QF} {g : SOAf Q₀} :
    g ∈ classSub Q₀ hn hQ hind ↔ ∃ γ ∈ GammaSOAdele Q₀, ∃ k ∈ KSO Q₀, g = γ.2 * k := Iff.rfl

/-- $\Gamma_fK$ contains the rotations of the adelic spinor kernel $O'(V_{\mathbb A_f})$ (strong approximation). -/
@[kb "shimura1999" "Lemma 2.4(1), p. 8 (G⁰_A ⊂ G⁰D, by strong approximation)"]
theorem spinorKernel_le_classSub (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) (h : SOAf Q₀)
    (hh : (h : OAf QF) ∈ spinorKernelAf QF) : h ∈ classSub Q₀ hn hQ hind :=
  exists_Gamma_KSO_of_spinorKernel Q₀ hn hQ hind h hh

/-- Commutators of $SO(V)(\mathbb A_f)$ lie in $\Gamma_fK$. -/
theorem commutator_mem_classSub (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) (g h : SOAf Q₀) :
    g * h * g⁻¹ * h⁻¹ ∈ classSub Q₀ hn hQ hind := by
  refine spinorKernel_le_classSub Q₀ hn hQ hind _ ?_
  have := commutator_mem_spinorKernelAf QF (nondegenerate_map Q₀ hQ) (g : OAf QF) (h : OAf QF)
  simpa using this

/-- **$\Gamma_fK$ is normal in $SO(V)(\mathbb A_f)$** (Shimura 1999, Lemma 2.4(3): "$GD$ is a normal subgroup of
$G_{\mathbb A}$"), for $Q_0$ indefinite and $n\ge3$. -/
@[kb "shimura1999" "Lemma 2.4(3), p. 8 (GD is a normal subgroup of G_A)"]
theorem classSub_normal (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) :
    (classSub Q₀ hn hQ hind).Normal where
  conj_mem x hx g := by
    have hc := commutator_mem_classSub Q₀ hn hQ hind g x
    have : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    rw [this]; exact (classSub Q₀ hn hQ hind).mul_mem hc hx

/-- Squares of $SO(V)(\mathbb A_f)$ lie in $\Gamma_fK$: the quotient has exponent $2$. -/
theorem sq_mem_classSub (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) (g : SOAf Q₀) :
    g ^ 2 ∈ classSub Q₀ hn hQ hind := by
  refine spinorKernel_le_classSub Q₀ hn hQ hind _ ?_
  have := sq_mem_spinorKernelAf QF (nondegenerate_map Q₀ hQ) (g : OAf QF)
  simpa using this

/-- The double coset relation in terms of $\Gamma_fK$: $b'\in\Gamma_f\,b\,K\iff b^{-1}b'\in\Gamma_fK$. -/
theorem dcSetoid_iff (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) (b b' : SOAf Q₀) :
    dcSetoid Q₀ b b' ↔ b⁻¹ * b' ∈ classSub Q₀ hn hQ hind := by
  have hN := classSub_normal Q₀ hn hQ hind
  constructor
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    have h1 : b⁻¹ * γ.2 * b ∈ classSub Q₀ hn hQ hind := by
      have := hN.conj_mem γ.2 ⟨γ, hγ, 1, (KSO Q₀).one_mem, by simp⟩ b⁻¹
      simpa using this
    have h2 : k ∈ classSub Q₀ hn hQ hind := ⟨1, (GammaSOAdele Q₀).one_mem, k, hk, by simp⟩
    have := (classSub Q₀ hn hQ hind).mul_mem h1 h2
    simpa [mul_assoc] using this
  · intro h
    -- `b γ k b⁻¹ ∈ Γ_f K`, and `κ b ∈ Γ_f b K`
    have hc : b * (b⁻¹ * b') * b⁻¹ ∈ classSub Q₀ hn hQ hind := hN.conj_mem _ h b
    obtain ⟨γ, hγ, κ, hκ, he⟩ := hc
    obtain ⟨γ', hγ', κ', hκ', he'⟩ := mem_Gamma_mul_KSO Q₀ hn hQ hind 1 b κ hκ
    simp only [one_mul] at he'
    refine ⟨γ * γ', (GammaSOAdele Q₀).mul_mem hγ hγ', κ', hκ', ?_⟩
    have hb' : b' = γ.2 * κ * b := by
      have : b' = b * (b⁻¹ * b') * b⁻¹ * b := by group
      rw [this, he]
    rw [hb', mul_assoc, he']
    simp only [Prod.snd_mul]
    group

/-- **The proper classes as a quotient group** (Shimura 1999, Lemma 2.4(3): $G\backslash G_{\mathbb A}/D$ "can be identified
with $G_{\mathbb A}/GD$"): for $Q_0$ indefinite and $n\ge3$,
$$SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)\ \simeq\ SO(V)(\mathbb A_f)/SO(V)(F)\,SO(\hat L).$$ -/
@[kb "shimura1999" "Lemma 2.4(3), p. 8 (G\\G_A/D identified with G_A/GD)"]
def dcEquivQuot (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) :
    DC Q₀ ≃ SOAf Q₀ ⧸ classSub Q₀ hn hQ hind :=
  Quotient.congr (Equiv.refl _) fun b b' => by
    rw [dcSetoid_iff Q₀ hn hQ hind]
    exact (QuotientGroup.leftRel_apply).symm

/-- **The number of proper classes is an index** (Shimura 1999, Lemma 2.4(3)): for $Q_0$ indefinite and $n\ge3$,
$h = \#\mathrm{Cl} = [SO(V)(\mathbb A_f) : SO(V)(F)\,SO(\hat L)]$. -/
@[kb "shimura1999" "Lemma 2.4(3), p. 8"]
theorem card_DC_eq_index (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) :
    Nat.card (DC Q₀) = (classSub Q₀ hn hQ hind).index := by
  rw [Subgroup.index, Nat.card_congr (dcEquivQuot Q₀ hn hQ hind)]

/-- **The number of proper classes in an indefinite genus is a power of $2$** ($n\ge3$): the quotient
$SO(V)(\mathbb A_f)/SO(V)(F)SO(\hat L)$ is finite (`finite_DC`) of exponent $2$. -/
@[kb "shimura1999" "Lemma 2.4(3)–(4), p. 8 (G\\G_A/D ≅ F_A^×/F^×σ(D), an elementary abelian 2-group)"]
theorem exists_card_DC_eq_two_pow (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hind : IsIndefinite QF) :
    ∃ k : ℕ, Nat.card (DC Q₀) = 2 ^ k := by
  have := classSub_normal Q₀ hn hQ hind
  have := finite_DC Q₀ hQ
  have : Finite (SOAf Q₀ ⧸ classSub Q₀ hn hQ hind) := Finite.of_equiv _ (dcEquivQuot Q₀ hn hQ hind)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (SOAf Q₀ ⧸ classSub Q₀ hn hQ hind) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact sq_mem_classSub Q₀ hn hQ hind g
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  exact ⟨k, by rw [Nat.card_congr (dcEquivQuot Q₀ hn hQ hind), hk]⟩

open Eq57 in
/-- **Corollary 5.2, second assertion (class number one), with explicit conditions** (Hanke thesis, p. 19: "If $k$ has
class number one, then $\mathrm{vol}(\Gamma_a\backslash Z) = \varepsilon\,\mathrm{Mass}(\Lambda,\varphi)$"). Here: $\mathcal O_F$ a
principal ideal domain, $Q$ isotropic at **every** infinite place (`hinf`; no compact archimedean factor), and the local
spinor norm condition `LocalSpinorUnits` at the primes $\mathfrak p\mid2\det H$ (`hbad`; Shimura's Lemma 2.5 gives it for
maximal lattices, not formalized). Then there is one proper class (`subsingleton_DC_of_bad`) and
$\mathrm{vol}_Z(D) = s\cdot\mathrm{Mass}$.

*Update (candidate):* when some real places $\mathbf c$ are compact, the index
$[k^\times_{\mathbb A}:k^\times\sigma(D)]$ is a class number with signs at $\mathbf c$, which can exceed the class number of $k$
when $\lvert\mathbf c\rvert\ge2$; hence the hypothesis `hinf` here. -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (second assertion; corrected form)"]
theorem corollary52_classNumberOne_PID [IsPrincipalIdealRing (𝓞 F)] (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate)
    (hinf : ∀ w : InfinitePlace F, (QF).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (QF) v (Tamagawa.stdLat F n))
    (D : DC Q₀ → Set (ZQ Q₀ hQ)) (hD : ∀ i, MeasurableSet (D i)) (s : DC Q₀ → ℝ≥0∞) (hs0 : ∀ i, s i ≠ 0)
    (hsT : ∀ i, s i ≠ ⊤)
    (hDs : ∀ i, ∀ᵐ z ∂(muZQ Q₀ hQ), ∑' γ : unitGroup Q₀ i, (D i).indicator 1 (γ • z) = s i) (i : DC Q₀) :
    muZQ Q₀ hQ (D i) = s i * hankeMass Q₀ hQ := by
  have hind : IsIndefinite QF := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact ⟨w, hinf w⟩
  have hsub := subsingleton_DC_of_bad Q₀ (nondegenerate_map Q₀ hQ) hn hinf hbad
  have hcard : Nat.card (DC Q₀) = 1 := by
    have : Unique (DC Q₀) := ⟨⟨i⟩, fun j => hsub.elim _ _⟩
    exact Nat.card_unique
  exact corollary52_indefinite_classNumberOne Q₀ hn hQ hind D hD s hs0 hsT hDs hcard i

end QuadFormsKB.Hanke2005.EqualMasses
