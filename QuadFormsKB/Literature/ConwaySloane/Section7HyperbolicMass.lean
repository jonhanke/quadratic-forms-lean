/-
# Conway–Sloane 1988, §11, Lemma 1, from Conway–Sloane Ch. 15, §7

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula* (1988), §11, Lemma 1, p. 280
(`conwaysloane1988`): two positive definite integral lattices $f$, $g$ are in the same genus if and only if
$f \oplus H$ and $g \oplus H$ are integrally equivalent, $H = \begin{pmatrix}0&1\\1&0\end{pmatrix}$. The paper states it
without proof (citing Kneser–Puppe 1953), and the library had it as the named statement `Mass.Lemma1Statement`.

**Proves** `lemma1Statement_proof : Mass.Lemma1Statement`, from the general statement of *Sphere Packings, Lattices
and Groups*, Ch. 15, §7, p. 378 (`sameGenus_iff_intEquiv_add_hyperbolic`, proved for every nonsingular symmetric
integral Gram matrix: Eichler's theorem for "⇒", cancellation of $H$ over $\mathbb Z_p$ (O'Meara 93:14) and over
$\mathbb R$ for "⇐"). The two formalizations agree definitionally: `ofMatrixZ A` is `Cassels.Ch8Ex2.gramForm A`, and
`blockMat A 0 0 hypGram` is `orthSumMat A !![0, 1; 1, 0]`. So the input `Mass.Lemma1Statement` is now a theorem.
-/
import QuadFormsKB.Literature.ConwaySloane.Section7Hyperbolic
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemmas

namespace QuadFormsKB.ConwaySloane

/-- **Conway–Sloane 1988, §11, Lemma 1, proved** (it was the named statement `Mass.Lemma1Statement`): for positive
definite integral Gram matrices $A$, $B$, the forms are in the same genus iff $A \oplus H$ and $B \oplus H$ are
integrally equivalent. A special case of Ch. 15, §7, p. 378 (`sameGenus_iff_intEquiv_add_hyperbolic`). -/
@[kb "conwaysloane1988" "§11, Lemma 1, p. 280 (proved from Ch. 15 §7)"]
theorem lemma1Statement_proof : Mass.Lemma1Statement where
  iff _ _ _ hA hB := sameGenus_iff_intEquiv_add_hyperbolic hA.1 hB.1 hA.det_ne

end QuadFormsKB.ConwaySloane
