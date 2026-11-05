/-
# Conway–Sloane 1988, §11, remarks 4 and 5: the four genera of determinant $p$ and of determinant $2p$

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §11, p. 281 (bibliography key `conwaysloane1988`):
* (remark 4) "if $d = p$ is an odd prime ... there are four possible genera in two vines, belonging to
  $\mathrm I_n(p^+)$ and $\mathrm{II}_n(p^+)$, $\mathrm I_n(p^-)$ and $\mathrm{II}_n(p^-)$ (the $+$ sign if $a$ is a residue,
  the $-$ sign for a non-residue)";
* (remark 5) "in the case of determinant $d = 2p$ ... there are four genera in two vines:
  $\mathrm I_n(d^+)$ and $\mathrm{II}_n(d^+)$, $\mathrm I_n(d^-)$ and $\mathrm{II}_n(d^-)$".

**Layer: systems of symbols.** As in the Chapter 15 files (`SmallDet.lean`, `SmallDetTables*.lean`), a genus is
represented by its system of local symbols, a `GenusSymbolData` satisfying `GenusSymbolData.Conditions` (the
conditions (29)–(35) of *Sphere Packings, Lattices and Groups*, Ch. 15, §7.7); "the genus exists" means that such a
system exists. The lattices of the paper are positive definite of dimension $n$: $(-1)$-adic symbol $+^n-^0$
(`G.real = ⟨n, 0⟩`). A genus is labelled by
* its type $T$: the scaled type `(G.two 0).type` of the 2-adic constituent of scale $1$ (I = odd lattice, II = even
  lattice; for $d$ odd or $d = 2p$ the lattice is even iff this constituent is even);
* the sign $e$ of the $p$-adic constituent $p^{e1}$, `(G.odd p 1).sign`.

The paper's sign is the quadratic residuosity mod $p$ of the integer $a$ with $v_p\cdot v_p = a/p$, $v_p$ a generator of
the $p$-part of $L^*/L$. In a $p$-adic Jordan decomposition $L \cong_p \langle u_0, \ldots, u_{n-2}\rangle \perp \langle pu\rangle$
one may take $v_p = e_{n-1}/p$, of norm $u/p$, so $a \equiv u$ and the paper's sign is $e = \left(\frac{u}{p}\right)$; this
identification is explanatory and is not formalized here.

**Proves**
* `detP_symbols_unique`: two systems with $(-1)$-adic symbol $+^r-^s$, $\lvert\det\rvert = p$, the same type and the same
  sign $e$ have identical 2-adic and $p$-adic symbols at every prime: at most one genus for each $(T, e)$.
* `genera_det_prime` (§11, remark 4): for positive definite lattices of dimension $n$ and determinant $p$, the genus is
  determined by $(T, e) \in \{\mathrm I, \mathrm{II}\} \times \{+, -\}$ (at most four genera
  $\mathrm I_n(p^\pm)$, $\mathrm{II}_n(p^\pm)$), and $\mathrm I_n(p^e)$, $\mathrm{II}_n(p^e)$ exist iff `TypeIRhs p 1 n 0 e`,
  `TypeIIRhs p 1 n 0 e` (Conway–Sloane, *Sphere Packings, Lattices and Groups*, Ch. 15, Thm. 13 (a)).
* `genera_det_two_prime` (§11, remark 5): the same for determinant $2p$: the $p$-adic and $(-1)$-adic symbols are
  determined and the 2-adic symbols are determined up to sign walking and oddity fusion (`MoveEquiv`) by $(T, e)$; the
  genus $\mathrm I_n(d^e)$ (resp. $\mathrm{II}_n(d^e)$) exists iff `Rhs2p p n 0 e .I` (resp. `.II`) (*Sphere Packings, Lattices and Groups*, Ch. 15,
  Table 15.4, rows $\pm6$, $\pm10$).

The passage from systems of symbols to genera of lattices is Thm. 11 of *Sphere Packings, Lattices and Groups* Ch. 15 (not part of this file).
-/
import QuadFormsKB.Literature.ConwaySloane.SmallDetTables4

namespace QuadFormsKB.ConwaySloane.Mass

open QuadFormsKB.ConwaySloane

/-- **The symbols of determinant $\pm p$ are determined by the type and the sign $e$** (Conway–Sloane 1988, §11,
remark 4, p. 281; the symbol-level form): two systems satisfying the conditions, with equal $(-1)$-adic symbols,
$\lvert\det\rvert = p$, equal types of the scale-1 2-adic constituent and equal signs of $p^{e1}$, have identical 2-adic
symbols and identical $q$-adic symbols at every odd prime $q$. -/
theorem detP_symbols_unique (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (G G' : GenusSymbolData)
    (hc : G.Conditions) (hc' : G'.Conditions) (hr : G.real = G'.real) (hd : G.det.natAbs = p)
    (hd' : G'.det.natAbs = p) (hT : (G.two 0).type = (G'.two 0).type)
    (he : (G.odd p 1).sign = (G'.odd p 1).sign) :
    (∀ k, G.two k = G'.two k) ∧ (∀ q, q.Prime → q ≠ 2 → G.odd q = G'.odd q) := by
  have hr1 : G.real = ⟨G.real.pos, G.real.neg⟩ := rfl
  have hr2 : G'.real = ⟨G.real.pos, G.real.neg⟩ := hr.symm.trans hr1
  generalize G.real.pos = r at hr1 hr2
  generalize G.real.neg = s at hr1 hr2
  have hn : G.n = r + s := by rw [← hc.real_dim, hr1]
  have hn' : G'.n = r + s := by rw [← hc'.real_dim, hr2]
  have hdet : G.det = (p : ℤ) ^ 1 * (-1) ^ s := by
    have := G.det_eq_of hc (m := p) hp.pos hd hr1
    rw [this]; ring
  have hdet' : G'.det = (p : ℤ) ^ 1 * (-1) ^ s := by
    have := G'.det_eq_of hc' (m := p) hp.pos hd' hr2
    rw [this]; ring
  have hd1 : G.det.natAbs = p ^ 1 := by rw [hd, pow_one]
  have hd1' : G'.det.natAbs = p ^ 1 := by rw [hd', pow_one]
  have hvp : padicValInt p G.det = 1 := by rw [hdet]; exact padicValInt_pk p 1 s hp
  have hvp' : padicValInt p G'.det = 1 := by rw [hdet']; exact padicValInt_pk p 1 s hp
  have hv2 : padicValInt 2 G.det = 0 := by
    rw [hdet]; exact padicValInt_pk_ne 2 p 1 s Nat.prime_two hp (Ne.symm hp2)
  have hv2' : padicValInt 2 G'.det = 0 := by
    rw [hdet']; exact padicValInt_pk_ne 2 p 1 s Nat.prime_two hp (Ne.symm hp2)
  obtain ⟨b1, b2, b3, b4, -, -⟩ := G.p_shape hc p hp hp2 hvp
  obtain ⟨b1', b2', b3', b4', -, -⟩ := G'.p_shape hc' p hp hp2 hvp'
  have hel : ∀ j, 2 ≤ j → (G.odd p j).dim = 0 := fun j hj => by rw [b3 j hj]; rfl
  have hel' : ∀ j, 2 ≤ j → (G'.odd p j).dim = 0 := fun j hj => by rw [b3' j hj]; rfl
  obtain ⟨-, a2, -, -⟩ := G.pk_part hc p 1 hp hp2 le_rfl hd1 hel hr1
  obtain ⟨-, a2', -, -⟩ := G'.pk_part hc' p 1 hp hp2 le_rfl hd1' hel' hr2
  obtain ⟨t1, -⟩ := G.two_part hc hv2
  obtain ⟨t1', -⟩ := G'.two_part hc' hv2'
  have hdp : G.det / p = (-1) ^ s := by rw [hdet]; simpa using pk_div p 1 s hp
  have hdp' : G'.det / p = (-1) ^ s := by rw [hdet']; simpa using pk_div p 1 s hp
  rw [hdp] at b4
  rw [hdp'] at b4'
  refine ⟨fun k => ?_, fun q hq hq2 => ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [a2, a2', hT, he]
    · rw [t1 k hk, t1' k hk]
  · by_cases hqp : q = p
    · subst hqp
      funext k
      rcases Nat.lt_or_ge k 2 with hk | hk
      · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · have hs0 : (G.odd q 0).sign = (G'.odd q 0).sign := by
            have k1 := b4
            rw [he, ← b4'] at k1
            revert k1
            cases (G.odd q 0).sign <;> cases (G'.odd q 0).sign <;> cases (G'.odd q 1).sign <;> decide
          have hd0 : (G.odd q 0).dim = (G'.odd q 0).dim := by omega
          rcases hf : G.odd q 0 with ⟨d0, s0⟩
          rcases hf' : G'.odd q 0 with ⟨d0', s0'⟩
          rw [hf, hf'] at hs0 hd0
          simp only at hs0 hd0
          rw [hs0, hd0]
        · have hd1 : (G.odd q 1).dim = (G'.odd q 1).dim := by omega
          rcases hf : G.odd q 1 with ⟨d0, s0⟩
          rcases hf' : G'.odd q 1 with ⟨d0', s0'⟩
          rw [hf, hf'] at he hd1
          simp only at he hd1
          rw [he, hd1]
      · rw [b3 k hk, b3' k hk]
    · funext k
      rw [G.odd_unit hc q hq hq2 (by rw [hdet]; exact padicValInt_pk_ne q p 1 s hq hp hqp),
        G'.odd_unit hc' q hq hq2 (by rw [hdet']; exact padicValInt_pk_ne q p 1 s hq hp hqp), hn, hn', hdet, hdet']

/-- From $\lvert\det\rvert = p$ the $p$-adic constituents of scale $p^j$, $j \ge 2$, vanish. -/
theorem detP_elementary (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (G : GenusSymbolData) (hc : G.Conditions)
    {r s : ℕ} (hr : G.real = ⟨r, s⟩) (hd : G.det.natAbs = p) : ∀ j, 2 ≤ j → (G.odd p j).dim = 0 := by
  have hdet : G.det = (p : ℤ) ^ 1 * (-1) ^ s := by
    have := G.det_eq_of hc (m := p) hp.pos hd hr
    rw [this]; ring
  have hvp : padicValInt p G.det = 1 := by rw [hdet]; exact padicValInt_pk p 1 s hp
  obtain ⟨-, -, b3, -⟩ := G.p_shape hc p hp hp2 hvp
  exact fun j hj => by rw [b3 j hj]; rfl

/-- **§11, remark 4: the four genera of determinant $p$** (Conway–Sloane 1988, p. 281). Let $p$ be an odd prime and
$n \ge 1$. For positive definite lattices of dimension $n$ and determinant $p$ (systems of symbols with
$(-1)$-adic symbol $+^n$, $\lvert\det\rvert = p$):
* the genus is determined by the type $T$ and the sign $e$ of $p^{e1}$: at most the four genera
  $\mathrm I_n(p^+)$, $\mathrm{II}_n(p^+)$, $\mathrm I_n(p^-)$, $\mathrm{II}_n(p^-)$;
* $\mathrm I_n(p^e)$ exists iff `TypeIRhs p 1 n 0 e` and $\mathrm{II}_n(p^e)$ exists iff `TypeIIRhs p 1 n 0 e`
  ($\mathrm{II}$: $n + (p - 1) + 4[e = -] \equiv 0 \pmod 8$, and $e = +$ if $n = 1$).
Unconditional (from *Sphere Packings, Lattices and Groups* Ch. 15, Thm. 13 (a), `thm13a_typeI`, `thm13a_typeII`). -/
@[kb "conwaysloane1988" "§11, remark 4, p. 281 (four genera I_n(p^±), II_n(p^±))"]
theorem genera_det_prime (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∀ G G' : GenusSymbolData, G.Conditions → G'.Conditions → G.real = ⟨n, 0⟩ → G'.real = ⟨n, 0⟩ →
      G.det.natAbs = p → G'.det.natAbs = p → (G.two 0).type = (G'.two 0).type →
      (G.odd p 1).sign = (G'.odd p 1).sign →
      (∀ k, G.two k = G'.two k) ∧ (∀ q, q.Prime → q ≠ 2 → G.odd q = G'.odd q)) ∧
    (∀ e : Sign, (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨n, 0⟩ ∧ G.det.natAbs = p ∧
        (G.two 0).type = .I ∧ (G.odd p 1).sign = e) ↔ TypeIRhs p 1 n 0 e) ∧
    (∀ e : Sign, (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨n, 0⟩ ∧ G.det.natAbs = p ∧
        (G.two 0).type = .II ∧ (G.odd p 1).sign = e) ↔ TypeIIRhs p 1 n 0 e) := by
  refine ⟨fun G G' hc hc' hr hr' hd hd' hT he =>
    detP_symbols_unique p hp hp2 G G' hc hc' (hr.trans hr'.symm) hd hd' hT he, fun e => ?_, fun e => ?_⟩
  · rw [← thm13a_typeI p 1 n 0 hp hp2 le_rfl e]
    constructor
    · rintro ⟨G, hc, hr, hd, hT, he⟩
      exact ⟨G, hc, hr, by rw [hd, pow_one], hT, he, detP_elementary p hp hp2 G hc hr hd⟩
    · rintro ⟨G, hc, hr, hd, hT, he, -⟩
      exact ⟨G, hc, hr, by rw [hd, pow_one], hT, he⟩
  · rw [← thm13a_typeII p 1 n 0 hp hp2 le_rfl e]
    constructor
    · rintro ⟨G, hc, hr, hd, hT, he⟩
      exact ⟨G, hc, hr, by rw [hd, pow_one], hT, he, detP_elementary p hp hp2 G hc hr hd⟩
    · rintro ⟨G, hc, hr, hd, hT, he, -⟩
      exact ⟨G, hc, hr, by rw [hd, pow_one], hT, he⟩

/-- **§11, remark 5: the four genera of determinant $2p$** (Conway–Sloane 1988, p. 281). Let $p$ be an odd prime and
$d = 2p$. For positive definite lattices of dimension $n$ and determinant $2p$ (systems of symbols with $(-1)$-adic
symbol $+^n$, $\lvert\det\rvert = 2p$):
* the type $T$ and the sign $e$ of $p^{e1}$ determine the $q$-adic symbols at every odd prime $q$, and the 2-adic symbol
  up to sign walking and oddity fusion (`MoveEquiv`, which does not change the genus): at most the four genera
  $\mathrm I_n(d^\pm)$, $\mathrm{II}_n(d^\pm)$;
* the genus with type $T$ and sign $e$ exists iff `Rhs2p p n 0 e T`.
Unconditional (from *Sphere Packings, Lattices and Groups* Ch. 15, Table 15.4, `table154_twoP`, `table154_twoP_unique`). -/
@[kb "conwaysloane1988" "§11, remark 5, p. 281 (four genera I_n(d^±), II_n(d^±), d = 2p)"]
theorem genera_det_two_prime (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∀ G G' : GenusSymbolData, G.Conditions → G'.Conditions → G.real = ⟨n, 0⟩ → G'.real = ⟨n, 0⟩ →
      G.det.natAbs = 2 * p → G'.det.natAbs = 2 * p → (G.two 0).type = (G'.two 0).type →
      (G.odd p 1).sign = (G'.odd p 1).sign →
      (∀ q, q.Prime → q ≠ 2 → G.odd q = G'.odd q) ∧ MoveEquiv G.two G'.two) ∧
    (∀ (e : Sign) (T : ScaledType), (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨n, 0⟩ ∧
        G.det.natAbs = 2 * p ∧ (G.two 0).type = T ∧ (G.odd p 1).sign = e) ↔ Rhs2p p n 0 e T) :=
  ⟨fun G G' hc hc' hr hr' hd hd' hT he =>
    table154_twoP_unique p hp hp2 G G' hc hc' (hr.trans hr'.symm) hd hd' hT he,
   fun e T => table154_twoP p n 0 hp hp2 e T⟩

end QuadFormsKB.ConwaySloane.Mass
