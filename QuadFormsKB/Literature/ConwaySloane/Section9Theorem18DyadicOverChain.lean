/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ through chains of canonical overlattices

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicOverlattice.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a basis
$\gamma$ of a local lattice $M = \gamma\mathbb Z_2^n$ with Gram matrix $G$ = `locGram Q v γ`.

**Defines**
* `OverChain Q v γ` (a **condition**, an inductive predicate): $M = \gamma\mathbb Z_2^n$ is, for some scalar $c$,
  scaled even unimodular, or a scaled $E \perp \langle 2u\rangle$; or a halving step (`HalfStep.Data`) leads to a
  basis $\gamma W$ with `OverChain`; or a pair-glue-and-halving step (`PairHalf.Data`) does. Each step passes to an
  overlattice $M^+ \supseteq M$ that is defined canonically from $M$, $B$ and $Q$, so that every automorphism of $M$
  is an automorphism of $M^+$.
* `UnitRoots Q v γ` (a **condition**): $cG$ is integral and even with a unit entry, or $G$ has an orthogonal pair
  $b_{l_1}, b_{l_2}$ with $cG_{l_1l_1}/2$, $cG_{l_2l_2}/2$ units and $c(G_{l_1l_1} + G_{l_2l_2})/2 \in 4\mathbb Z_2$.

**Proves**
* `evenStable_of_overChain`: `OverChain Q v γ` implies that every rotation preserving $\gamma\mathbb Z_2^n$ has a
  spinor norm of even order;
* `units_of_unitRoots`: under `UnitRoots`, every unit class lies in the root group of $L$ ($L_2 = \gamma\mathbb Z_2^n$);
* `theorem18OnlyIf_of_overChain` (**Theorem 18, "only if", at $p = 2$ for the overlattice chains**, unconditional).

*Examples* (checked by a computer calculation (outside Lean), in the Jordan basis; $K, K'$ even unimodular
binary, the form $Q(x) = x^{\mathsf T}Mx$): $\langle a, b\rangle \perp 2K$, $\langle a, b\rangle \perp 4\langle c\rangle$,
$\langle a, b\rangle \perp 4\langle c, d\rangle$, $\langle a, b\rangle \perp 8K$ with $a + b \equiv c + d \equiv 0 \pmod 4$;
$K \perp 8\langle a\rangle$, $K \perp 8\langle a, b\rangle$ ($a + b \equiv 0 \pmod 4$), $K \perp 4K'$,
$K \perp 2\langle a\rangle \perp 8\langle b\rangle$ ($a + b \equiv 0 \pmod 4$).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicPairHalfStep
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicPairUnits

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section OverChain

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

variable (Q v) in
/-- **Chains of canonical overlattices** (a **condition** on a basis $\gamma$ of a local lattice; see the module
docstring). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adic shapes reached by a chain of canonical overlattices)"]
inductive OverChain : GL (Fin n) (v.adicCompletion ℚ) → Prop
  /-- $cG$ even unimodular. -/
  | even {γ : GL (Fin n) (v.adicCompletion ℚ)} {c : v.adicCompletion ℚ} (hc : c ≠ 0)
      (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1)
      (hdet : Valued.v (c • locGram Q v γ).det = 1)
      (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1) : OverChain γ
  /-- $cG$ of the shape $E \perp \langle 2u\rangle$. -/
  | glue {γ : GL (Fin n) (v.adicCompletion ℚ)} {c : v.adicCompletion ℚ} (l : Fin n) (hc : c ≠ 0)
      (hint : ∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1)
      (heven : ∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1)
      (hl : ∀ i, i ≠ l → locGram Q v γ i l = 0) (hu : Valued.v (c * locGram Q v γ l l / 2) = 1)
      (hdet : Valued.v (c • locGram Q v γ).det = Valued.v (2 : v.adicCompletion ℚ)) : OverChain γ
  /-- A halving step. -/
  | half {γ : GL (Fin n) (v.adicCompletion ℚ)} {c : v.adicCompletion ℚ} {C D : Finset (Fin n)}
      (hD : HalfStep.Data Q v γ c C D) (h : OverChain (HalfStep.gamH γ C)) : OverChain γ
  /-- A pair-glue-and-halving step. -/
  | pairHalf {γ : GL (Fin n) (v.adicCompletion ℚ)} {c : v.adicCompletion ℚ} {C : Finset (Fin n)} {l₁ l₂ : Fin n}
      (hD : PairHalf.Data Q v γ c C l₁ l₂) (h : OverChain (PairHalf.gamP γ C hD.hl)) : OverChain γ

/-- **Even spinor norms along a chain of canonical overlattices.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (spinor norms of the automorphisms of a lattice with a chain of canonical overlattices have even order)"]
theorem evenStable_of_overChain (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {γ : GL (Fin n) Fv}
    (h : OverChain Q v γ) : EvenStable Q γ := by
  induction h with
  | even hc hint hdet heven => exact evenStable_of_scaledEvenUnimodular hQ _ hc hint hdet heven
  | glue l hc hint heven hl hu hdet => exact evenStable_of_glue hQ h2 _ hc l hint heven hl hu hdet
  | half hD _ ih => exact HalfStep.evenStable_of_half h2 hD ih
  | pairHalf hD _ ih => exact PairHalf.evenStable_of_pairHalf h2 hD ih

variable (Q v) in
/-- **Root vectors for every unit class** (a **condition** on a basis $\gamma$): either some $cG$ is integral and
even with a unit entry, or $G$ has an orthogonal pair $b_{l_1}, b_{l_2}$ with $cG_{l_1l_1}/2$, $cG_{l_2l_2}/2$ units
and $\lvert c(G_{l_1l_1} + G_{l_2l_2})/2\rvert \le \lvert 4\rvert$. -/
def UnitRoots (γ : GL (Fin n) (v.adicCompletion ℚ)) : Prop :=
  (∃ (c : v.adicCompletion ℚ) (i0 j : Fin n), c ≠ 0 ∧ (∀ i j, Valued.v (c * locGram Q v γ i j) ≤ 1) ∧
      (∀ i, Valued.v (c * locGram Q v γ i i / 2) ≤ 1) ∧ Valued.v (c * locGram Q v γ i0 j) = 1) ∨
    (∃ (c : v.adicCompletion ℚ) (l₁ l₂ : Fin n), l₁ ≠ l₂ ∧ c ≠ 0 ∧ (∀ i, i ≠ l₁ → locGram Q v γ i l₁ = 0) ∧
      (∀ i, i ≠ l₂ → locGram Q v γ i l₂ = 0) ∧ Valued.v (c * locGram Q v γ l₁ l₁ / 2) = 1 ∧
      Valued.v (c * locGram Q v γ l₂ l₂ / 2) = 1 ∧
      Valued.v (c * (locGram Q v γ l₁ l₁ + locGram Q v γ l₂ l₂) / 2) ≤ Valued.v (4 : v.adicCompletion ℚ))

theorem units_of_unitRoots (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (h : UnitRoots Q v γ) :
    ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v := by
  rcases h with ⟨c, i0, j, hc, hint, heven, hj⟩ | ⟨c, l₁, l₂, hne, hc, h₁, h₂, ha, hb, hab⟩
  · exact units_le_rootGroup_of_unit_entry h2 γ hγ hc hint heven i0 j hj
  · exact units_le_rootGroup_of_pair' h2 γ hγ hne h₁ h₂ hc ha hb hab

/-- **Theorem 18, "only if", at $p = 2$ for lattices with a chain of canonical overlattices** (Conway–Sloane §9.5,
p. 391; unconditional): every element of $\theta(O^+(L_2))$ has even order (`evenStable_of_overChain`) and every unit
class is a product of two norms of root vectors (`units_of_unitRoots`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': lattices with a chain of canonical overlattices)"]
theorem theorem18OnlyIf_of_overChain (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (hc : OverChain Q v γ) (hu : UnitRoots Q v γ) :
    Theorem18OnlyIf Q L v hQ :=
  theorem18OnlyIf_of_evenStable hQ h2 γ hγ (evenStable_of_overChain hQ h2 hc) (units_of_unitRoots h2 γ hγ hu)

end OverChain

end QuadFormsKB.ConwaySloane
