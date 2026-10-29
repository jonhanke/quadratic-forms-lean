/-
# O'Meara §71B: the cyclotomic special case 71:13 of Hilbert reciprocity

**Setting.** $F$ an algebraic number field, places as in `QuadFormsKB/Defs/NumberField.lean` (`NFPlace F`: infinite
places `InfinitePlace F` and finite places, the nonzero primes of $\mathcal O_F$); the local Hilbert symbol
$\big(\tfrac{a,b}{v}\big)$ is `NFPlace.hilbert v a b`.

**Proves**
* `even_card_infinite_hilbert_neg_one` (**71:13**): if $\alpha \in F^\times$ has $\big(\tfrac{\alpha,-1}{\mathfrak p}\big) = 1$
  at every discrete spot $\mathfrak p$, then $\prod_{\mathfrak p\ \text{real}} \big(\tfrac{\alpha,-1}{\mathfrak p}\big) = 1$,
  i.e. the number of infinite places at which the symbol is $-1$ is even. (The conclusion of the book's statement is lost
  in the machine-read text; it is restored from the proof, which shows that the number of real spots at which $\alpha$
  is negative is even. At a complex place the symbol is $1$, so "infinite" and "real" agree.)

**Proof notes.** O'Meara proves 71:13 from the Frobenius automorphism of $F(\zeta_4)/F$ as a step towards Hilbert's
reciprocity law (71:18). The library proves the reciprocity law for number fields independently, by the Weil index
(`HN.hilbert_product_formula_nf`), so 71:13 is derived here as a special case of it.
-/
import QuadFormsKB.Literature.HasseNorm.Reciprocity

namespace QuadFormsKB.OMeara

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

/-- **Proposition 71:13** (O'Meara 1963, p. 196): let $\alpha \in F^\times$ with $\big(\tfrac{\alpha,-1}{\mathfrak p}\big) = 1$
for all discrete spots $\mathfrak p$ of the number field $F$. Then the Hilbert symbol $\big(\tfrac{\alpha,-1}{w}\big)$ is
$-1$ at an even number of infinite places $w$, i.e. $\prod_{w \mid \infty}\big(\tfrac{\alpha,-1}{w}\big) = 1$. -/
@[kb "omeara1963" "§71B, 71:13, p. 196 (via the library's Hilbert reciprocity)"]
theorem even_card_infinite_hilbert_neg_one (α : F) (hα : α ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hilbert α (-1) = 1) :
    Even {w : InfinitePlace F | (NFPlace.infinite w).hilbert α (-1) = -1}.ncard := by
  obtain ⟨-, heven⟩ := HN.hilbert_product_formula_nf α (-1) hα (by norm_num)
  have hS : {v : NFPlace F | v.hilbert α (-1) = -1} =
      NFPlace.infinite '' {w : InfinitePlace F | (NFPlace.infinite w).hilbert α (-1) = -1} := by
    ext v
    cases v with
    | infinite w => simp
    | finite v => simp [h v]
  rw [hS, Set.ncard_image_of_injective _ (fun _ _ e => NFPlace.infinite.inj e)] at heven
  exact heven

end QuadFormsKB.OMeara
