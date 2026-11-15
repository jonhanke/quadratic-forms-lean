/-
# Kitaoka 1993, §7.1: Lemmas 7.1.2 and 7.1.4 and their consequences, unconditionally

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.1, Lemma 7.1.2 (p. 192), Theorem 7.1.1 (p. 193),
Lemma 7.1.4 and Theorem 7.1.2 (p. 194); §7.5, Theorem 7.5.1 (p. 242).

**Proves** (all unconditional)
* `lemma712` (Lemma 7.1.2): Hermite's constant satisfies $\mu_r < \sqrt r$ for $2 \le r < 43$.
* `lemma714` (Lemma 7.1.4): $\mu_n < n/6$ for $n \ge 40$.
* `theorem711` (Theorem 7.1.1): every positive lattice of rank $< 43$ is of E-type.
* `theorem712` (Theorem 7.1.2): a positive lattice with integral Gram matrix and minimum at most $6$ is of E-type.
* `theorem751` (Theorem 7.5.1): for a totally real number field $K$ and positive lattices $L$, $M$ of rank $< 43$ (or
  with the trace form of $\mathcal O_K$ of E-type), an isometry of $\mathcal O_K L$ onto $\mathcal O_K M$ is integral.

**Proof notes.** As in the book: Blichfeldt's estimate (Theorem 2.2.1, `Blichfeldt.theorem221`) bounds $\mu_m$ by
$\frac 2\pi\Gamma(2 + m/2)^{2/m}$, and the numerical bounds of `Ch2BlichfeldtConst.lean` give Lemmas 7.1.2 and 7.1.4.
The earlier conditional reductions `EType.theorem711_of_lemma712`, `EType.theorem712_of_lemmas` and
`EType.theorem751_of_lemma712` then give the theorems.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch2Blichfeldt
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Theorem711
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Theorem712
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Theorem751Proof

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

/-- **Kitaoka 1993, Lemma 7.1.2** (p. 192), *proved*: Hermite's constant satisfies $\mu_r < \sqrt r$ for
$2 \le r < 43$. Proof: $\mu_r \le \frac 2\pi\Gamma(2 + r/2)^{2/r}$ (Theorem 2.2.1) and the numerical bound
`Blichfeldt.blichfeldtConst_lt_sqrt`. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.2, p. 192"]
theorem lemma712 : Lemma712 := fun r h2 h43 =>
  (Blichfeldt.theorem221 (by omega)).trans_lt (Blichfeldt.blichfeldtConst_lt_sqrt r h2 h43)

/-- **Kitaoka 1993, Lemma 7.1.4** (p. 194), *proved*: Hermite's constant satisfies $\mu_n < n/6$ for $n \ge 40$.
Proof: Theorem 2.2.1 and the numerical bound `Blichfeldt.blichfeldtConst_lt_div_six`. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.4, p. 194"]
theorem lemma714 : Lemma714 := fun n hn =>
  (Blichfeldt.theorem221 (by omega)).trans_lt (Blichfeldt.blichfeldtConst_lt_div_six n hn)

/-- **Kitaoka 1993, Theorem 7.1.1** (p. 193), *proved*: every positive lattice of rank less than $43$ is of E-type
(the minimal vectors of $L \otimes M$ are split, for every positive lattice $M$). -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.1, p. 193"]
theorem theorem711 : Theorem711 := theorem711_of_lemma712 lemma712

/-- **Kitaoka 1993, Theorem 7.1.2** (p. 194), *proved*: a positive lattice $L$ with $sL \subseteq \mathbb Z$
(integral Gram matrix) and $\min L \le 6$ is of E-type. -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.2, p. 194"]
theorem theorem712 : Theorem712 := theorem712_of_lemmas lemma712 lemma714

/-- **Kitaoka 1993, Theorem 7.5.1** (p. 242), *proved*: for a totally real number field $K$ and positive lattices
$L$, $M$ with $\operatorname{rank} L = \operatorname{rank} M < 43$ (or the trace form of $\mathcal O_K$ of E-type), an
isometry from $\mathcal O_K L$ onto $\mathcal O_K M$ maps $L$ onto $M$ (its matrix is integral). -/
@[kb "kitaoka1993" "§7.5, Thm. 7.5.1, p. 242"]
theorem theorem751 : Theorem751 := theorem751_of_lemma712 lemma712

/-- **Kitaoka 1993, Theorem 7.1.1, extended to rank $43$** (*Update:* the book states rank $< 43$). Blichfeldt's bound
gives $\mu_{43} \le b_{43} \approx 6.5244 < \sqrt{43} \approx 6.5574$ (`Blichfeldt.blichfeldtConst_lt_sqrt_of_le`), so
Kitaoka's argument applies verbatim to rank $43$; Kitaoka's Stirling estimate of $b_r$ is what stops at $42$. The
estimate fails from $r = 44$ on ($b_{44} \approx 6.647 > \sqrt{44}$), so this argument gives nothing further. -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.1, p. 193 (extended to rank ≤ 43)"]
theorem theorem711_of_le_fortyThree (n : ℕ) (hn : n ≤ 43) (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsPosGram A) :
    IsEType A :=
  isEType_of_hermite 43 (fun r h2 h43 => (Blichfeldt.theorem221 (by omega)).trans_lt
    (Blichfeldt.blichfeldtConst_lt_sqrt_of_le r h2 h43)) n hn A hA

end QuadFormsKB.Kitaoka.EType
