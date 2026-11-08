/-
# Cassels, Chapter 11, §3: the number of proper spinor genera of a genus is $|G|$

J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Theorem 3.1 (pp. 211–212), counted.

**Layer:** $\mathbb Z$-lattices `Lat ℚ n` in $V = \mathbb Q^n$ with a regular form $Q$, $n \ge 3$; a finite set $P$ of
primes with Cassels' condition (3.7) (`hP`); Cassels' group $G = R/ST$ (`CasselsG`).

**Proves** that $g \mapsto g\mathcal S_\Lambda$ (Cassels' action (3.32), `CasselsAct`) is a bijection from $G$ onto the
set of proper spinor genera in the genus of $\Lambda$ (`casselsGEquiv`), so the number $g^+(\Lambda)$ of proper spinor
genera (`properSpinorGenusNumber`) is the order of $G$ (`properSpinorGenusNumber_eq_card_casselsG`). This is the
content of Cassels' remark after Theorem 3.1 that the spinor genera in a genus are in one-one correspondence with the
elements of $G$. *Proof:* Theorem 3.1 (i) (`casselsAct_exists`) defines the map, (ii) (`casselsAct_unique`) makes it
injective, (iii) (`casselsAct_transitive`) surjective; that $g\mathcal S_\Lambda$ is a single spinor genus is Lemma 3.5,
Corollary (`sameProperSpinorGenus_casselsShift`). Corollaries: an element of $R$ outside $ST$ gives at least two
proper spinor genera (`one_lt_properSpinorGenusNumber_of_not_mem`, for an integral lattice, where the set of spinor
genera is finite), and $|G| = 2$ gives exactly two (`properSpinorGenusNumber_eq_two_of_card`).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3Thm
import QuadFormsKB.Literature.Cassels.Ch11Sec1

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-- Helper: $g\mathcal S_\Gamma$ depends only on the spinor genus of the target: if $\Delta \in g\mathcal S_\Gamma$ and
$\Delta'$ is in the proper spinor genus of $\Delta$, then $\Delta' \in g\mathcal S_\Gamma$. Arguments: `g` the element
of $G$, `Γ Δ Δ'` the lattices (`h`: $\Delta \in g\mathcal S_\Gamma$, `hΔ`: $\Delta, \Delta'$ in one proper spinor
genus). -/
theorem casselsAct_of_sameProperSpinorGenus {g : CasselsG Q hQ L P} {Γ Δ Δ' : Lat ℚ n}
    (h : CasselsAct Q hQ L P g Γ Δ) (hΔ : SameProperSpinorGenus Q Δ Δ') : CasselsAct Q hQ L P g Γ Δ' := by
  obtain ⟨Γ', hΓΓ', hΓ'P, α, hα, hα1, x, hx, hxg, hΔα⟩ := h
  exact ⟨Γ', hΓΓ', hΓ'P, α, hα, hα1, x, hx, hxg,
    SameProperSpinorGenus.trans Q (SameProperSpinorGenus.symm Q hΔ) hΔα⟩

/-- Helper (Cassels, Lemma 3.5, Corollary): $g\mathcal S_\Gamma$ is a single proper spinor genus: if $\Delta_1, \Delta_2
\in g\mathcal S_\Gamma$, they are in one proper spinor genus. Arguments: `hP` Cassels' condition (3.7), `g` the element of
$G$, `Γ Δ₁ Δ₂` the lattices (`hΓ`: $\Gamma$ in the genus of $\Lambda$ = `L`; `h₁ h₂`: $\Delta_i \in g\mathcal S_\Gamma$). -/
theorem sameProperSpinorGenus_of_casselsAct
    (hP : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P → ∀ u : (v.adicCompletion ℚ)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    {g : CasselsG Q hQ L P} {Γ Δ₁ Δ₂ : Lat ℚ n} (hΓ : SameGenus Q L.1 Γ.1)
    (h₁ : CasselsAct Q hQ L P g Γ Δ₁) (h₂ : CasselsAct Q hQ L P g Γ Δ₂) :
    SameProperSpinorGenus Q Δ₁ Δ₂ := by
  have : IsPrincipalIdealRing (𝓞 ℚ) := pid_rat
  obtain ⟨Γ₁, hΓ₁, h1P, α₁, hα₁, hα₁1, x₁, hx₁, hx₁g, hΔ₁⟩ := h₁
  obtain ⟨Γ₂, hΓ₂, h2P, α₂, hα₂, hα₂1, x₂, hx₂, hx₂g, hΔ₂⟩ := h₂
  have hG₁ : SameGenus Q L.1 Γ₁.1 :=
    SameGenus.trans Q hΓ (SameSpinorGenus.sameGenus Q (SameProperSpinorGenus.sameSpinorGenus Q hΓ₁))
  have key := sameProperSpinorGenus_casselsShift Q hQ L P hP hG₁ h1P h2P
    (SameProperSpinorGenus.trans Q (SameProperSpinorGenus.symm Q hΓ₁) hΓ₂) α₁ α₂
    (soSub_of_P Q P α₁ hα₁ hα₁1) (soSub_of_P Q P α₂ hα₂ hα₂1) hα₁1 hα₂1 x₁ x₂ hx₁ hx₂ (hx₁g.trans hx₂g.symm)
  exact SameProperSpinorGenus.trans Q hΔ₁
    (SameProperSpinorGenus.trans Q key (SameProperSpinorGenus.symm Q hΔ₂))

variable (hn : 3 ≤ n)
  (hP : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P → ∀ u : (v.adicCompletion ℚ)ˣ,
    u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))

include hn hP

/-- Helper: the proper spinor genus $g\mathcal S_\Lambda$, as an element of the set of proper spinor genera of the
genus of $\Lambda$ = `L` (a representative chosen by Theorem 3.1 (i)). Argument `g`: the element of $G$. -/
def casselsGToGenera (g : CasselsG Q hQ L P) : genusProperSpinorGenera Q L :=
  ⟨Quotient.mk (properSpnSetoid Q) (casselsAct_exists Q hQ L P hn hP g (SameGenus.refl Q L.1)).choose,
    _, rfl, (casselsAct_exists Q hQ L P hn hP g (SameGenus.refl Q L.1)).choose_spec.1⟩

/-- Helper: the representative of `casselsGToGenera g` lies in $g\mathcal S_\Lambda$. Argument `g`: the element of
$G$. -/
theorem casselsAct_casselsGToGenera (g : CasselsG Q hQ L P) :
    CasselsAct Q hQ L P g L (casselsAct_exists Q hQ L P hn hP g (SameGenus.refl Q L.1)).choose :=
  (casselsAct_exists Q hQ L P hn hP g (SameGenus.refl Q L.1)).choose_spec.2

/-- Helper: $g \mapsto g\mathcal S_\Lambda$ is a bijection from $G$ onto the proper spinor genera of the genus of
$\Lambda$ (Cassels, Theorem 3.1 (i)–(iii) and Lemma 3.5, Corollary). -/
theorem casselsGToGenera_bijective : Function.Bijective (casselsGToGenera Q hQ L P hn hP) := by
  constructor
  · intro g₁ g₂ h
    have h' := congrArg Subtype.val h
    simp only [casselsGToGenera] at h'
    have hsg : SameProperSpinorGenus Q _ _ := Quotient.exact h'
    exact casselsAct_unique Q hQ L P hn hP (SameGenus.refl Q L.1)
      (casselsAct_casselsGToGenera Q hQ L P hn hP g₁)
      (casselsAct_of_sameProperSpinorGenus Q hQ L P (casselsAct_casselsGToGenera Q hQ L P hn hP g₂)
        (SameProperSpinorGenus.symm Q hsg))
  · rintro ⟨c, M, rfl, hM⟩
    obtain ⟨g, hg⟩ := casselsAct_transitive Q hQ L P hn hP (SameGenus.refl Q L.1) hM
    refine ⟨g, Subtype.ext ?_⟩
    simp only [casselsGToGenera]
    exact Quotient.sound (sameProperSpinorGenus_of_casselsAct Q hQ L P hP (SameGenus.refl Q L.1)
      (casselsAct_casselsGToGenera Q hQ L P hn hP g) hg)

/-- **Cassels' group $G$ and the proper spinor genera** (Cassels, Ch. 11, Theorem 3.1, pp. 211–212): the map
$g \mapsto g\mathcal S_\Lambda$ is a bijection from $G = R/ST$ onto the set of proper spinor genera in the genus of
$\Lambda$ = `L`. -/
@[kb "cassels1978" "Ch. 11, Thm. 3.1, pp. 211–212 (G ≅ spinor genera of the genus)"]
def casselsGEquiv : CasselsG Q hQ L P ≃ genusProperSpinorGenera Q L :=
  Equiv.ofBijective _ (casselsGToGenera_bijective Q hQ L P hn hP)

/-- **The number of proper spinor genera is $|G|$** (Cassels, Ch. 11, Theorem 3.1, pp. 211–212, with Lemmas 3.4–3.5
and their Corollaries): for a regular rational form $Q$ in $n \ge 3$ variables, a lattice $\Lambda$ = `L`, and a finite
set $P$ of primes with Cassels' condition (3.7) (`hP`: away from $P$, $\theta(\Lambda_p)$ consists of the unit square
classes), the number $g^+(\Lambda)$ of proper spinor genera in the genus of $\Lambda$ equals the order
`Nat.card` of $G = R/ST$ (both $0$ if infinite). -/
@[kb "cassels1978" "Ch. 11, Lemmas 3.4–3.5 and Cor., Thm. 3.1, pp. 209–212 (number of proper spinor genera = |G|)"]
theorem properSpinorGenusNumber_eq_card_casselsG :
    properSpinorGenusNumber Q L = Nat.card (CasselsG Q hQ L P) := by
  rw [properSpinorGenusNumber, Set.ncard_def]
  exact (Nat.card_congr (casselsGEquiv Q hQ L P hn hP)).symm

/-- **Two proper spinor genera when $|G| = 2$** (Cassels, Ch. 11, Theorem 3.1). Argument `h`: $G$ has order $2$. -/
theorem properSpinorGenusNumber_eq_two_of_card (h : Nat.card (CasselsG Q hQ L P) = 2) :
    properSpinorGenusNumber Q L = 2 := by
  rw [properSpinorGenusNumber_eq_card_casselsG Q hQ L P hn hP, h]

/-- **More than one proper spinor genus** (Cassels, Ch. 11, Theorem 3.1 and (3.15)): if $\Lambda$ = `L` is integral
(`hLi`) and some $x \in R$ is not in $ST$ (`hx`), the genus of $\Lambda$ contains at least two proper spinor genera.
(Integrality makes the set of spinor genera finite, `properSpinorGenusNumber_eq_two_pow`.) -/
@[kb "cassels1978" "Ch. 11, Thm. 3.1, p. 211 (G ≠ 1 gives several spinor genera)"]
theorem one_lt_properSpinorGenusNumber_of_not_mem (hLi : IsIntegral Q L.1) (x : CasselsR P)
    (hx : x ∉ casselsST Q hQ L P) : 1 < properSpinorGenusNumber Q L := by
  have hfin := (properSpinorGenusNumber_eq_two_pow Q hQ L hLi).1
  have : Finite (genusProperSpinorGenera Q L) := hfin.to_subtype
  have : Finite (CasselsG Q hQ L P) := Finite.of_equiv _ (casselsGEquiv Q hQ L P hn hP).symm
  rw [properSpinorGenusNumber_eq_card_casselsG Q hQ L P hn hP]
  have hne : (QuotientGroup.mk x : CasselsG Q hQ L P) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]; exact hx
  exact Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hne⟩⟩

end QuadFormsKB.Lattices
