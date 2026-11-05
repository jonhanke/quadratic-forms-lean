/-
# Conway–Sloane, Ch. 15, §9: source tags on existing declarations

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9, pp. 388–393
(`conwaysloane1999`).

Conway–Sloane quote Theorems 14–17 from Eichler, Watson and Cassels without proof. The library proves Cassels' versions;
this file tags them with the Conway–Sloane locators and records the translation.

* **Theorem 15** (Watson Thm. 70): (a) $SG(M) = SG(L)\cdot\Delta(r)$ for $r = [L : L \cap M]$ prime to $2d$ (36) is
  Cassels Ch. 11, Thm. 4.1 (`Lattices.sameProperSpinorGenus_latSMul_of_casselsI`, with $I(\Gamma, \Delta)$ =
  `Lattices.casselsI` the index of (36)): $\Gamma$ is in the spinor genus of $\alpha\Delta$ with
  $\theta(\alpha_p) = r$ at the primes of $P$ — the action of the spinor operator $\Delta(r)$ (`deltaR`).
  (b) "$SG(f)\cdot\Delta(r)$ is defined for every natural $r$ prime to $2d$" ($n \ge 3$) is Cassels Thm. 3.1 (i)
  (`Lattices.casselsAct_exists`: $g\mathcal S$ is defined for every $g \in G$).
* §9.2: forms in the same genus are rationally equivalent by a transformation with denominator prime to $2d$: Cassels
  Ch. 11, Thm. 6.2 (`Lattices.exists_chain_of_sameGenus`).
* §9.3: the spinor norm $f(v_1)\cdots f(v_k)$ of a product of reflections (`Lattices.spinorNormHom`,
  `Lattices.spinorNorm_symmProd`, `Lattices.exists_symmProd_eq`); automorphous numbers = spinor norms of proper integral
  automorphisms, $\theta(O^+(\Lambda))$ (`Lattices.latSpinorNormGroup`, Cassels (1.20)); $p$-adically automorphous
  numbers, $\theta(O^+(\Lambda_p))$ (`Lattices.localSpinorNormGroup`).
* Theorem 14 (Eichler) in Cassels' form, Thm. 1.4 (`Lattices.isProperIsometric_of_sameProperSpinorGenus`).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Kernel

namespace QuadFormsKB.ConwaySloane

attribute [kb "conwaysloane1999" "Ch. 15, §9.2, Thm. 15 (a), (36), p. 389 (SG(M) = SG(L)·Δ(r), r = [L : L ∩ M]; via Cassels Ch. 11, Thm. 4.1)"]
  Lattices.sameProperSpinorGenus_latSMul_of_casselsI

attribute [kb "conwaysloane1999" "Ch. 15, §9.2, (36), p. 389 (the index r = [L : L ∩ M])"]
  Lattices.casselsI

attribute [kb "conwaysloane1999" "Ch. 15, §9.2, Thm. 15 (b), p. 389 (SG(f)·Δ(r) is defined, n ≥ 3; via Cassels Ch. 11, Thm. 3.1 (i))"]
  Lattices.casselsAct_exists

attribute [kb "conwaysloane1999" "Ch. 15, §9.2, p. 389 (same genus: rationally equivalent with denominator prime to 2d)"]
  Lattices.exists_chain_of_sameGenus

attribute [kb "conwaysloane1999" "Ch. 15, §9.3, p. 390 (spinor norm of a product of reflections)"]
  Lattices.spinorNormHom Lattices.spinorNorm_symmProd Lattices.exists_symmProd_eq

attribute [kb "conwaysloane1999" "Ch. 15, §9.3, p. 390 (automorphous numbers: spinor norms of proper integral automorphisms)"]
  Lattices.latSpinorNormGroup

attribute [kb "conwaysloane1999" "Ch. 15, §9.3, p. 390 (p-adically automorphous numbers)"]
  Lattices.localSpinorNormGroup

attribute [kb "conwaysloane1999" "Ch. 15, §9.1, Thm. 14, p. 388 (Eichler; Cassels Ch. 11, Thm. 1.4)"]
  Lattices.isProperIsometric_of_sameProperSpinorGenus

end QuadFormsKB.ConwaySloane
