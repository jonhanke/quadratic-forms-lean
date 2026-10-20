/-
# Local zeta functions of a quadratic form as generating series of local densities

**Layer:** local, non-archimedean: a finite place $v$ of a number field $F$, **dyadic places included**.

**Setting.** $F_v$ = `v.adicCompletion F`, $\mathcal O_v$ = `v.adicCompletionIntegers F`, uniformizer $\pi$ = `NF.π v`,
$q = N(v) = |\mathcal O_v/\mathfrak p_v|$. $Q$ is a quadratic form over $\mathcal O_v$ in $n$ variables (`QuadForm 𝔬 n`,
0-based indices), evaluated on $V_v = F_v^n$ by `Q.evalIn Fv`. $L_v = \mathcal O_v^n$ (`latL`), $\Phi_v = \mathbf 1_{L_v}$.
The absolute value is Mathlib's norm on $F_v$, which is the **normalized** one, $|x|_v = q^{-\mathrm{ord}_v x}$
(`norm_eq_absNorm_pow`; equal to the Haar modulus, `WeilRep.modK_eq_norm`).

**Measures.** $\nu$ is any translation-invariant measure on $F_v$, finite on $\mathcal O_v$, and $dx = \nu^{\otimes n}$ on $V_v$
(`Measure.pi`). The two instances used are the **standard** Haar measure `haarV` ($\operatorname{vol}(\mathcal O_v) = 1$; Weil's
$(dx)_\mathfrak p$, p. 89) and the **self-dual** measure `selfDualV` for the standard character
($\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$). Every formula below carries the factor $\nu(\mathcal O_v)^n$ explicitly.

**The local zeta function** (Weil 1982, §4.3, (1)–(2), p. 89):
$$Z_v(s) = \int_{V_v}|Q(x)|_v^s\,\Phi_v(x)\,dx = \int_{L_v}|Q(x)|_v^s\,dx \qquad (s \in \mathbb R,\ s \ge 0)$$
(`zetaInt ν Q s`). Weil's $Z_\mathfrak p$ uses $d'x = (1 - q^{-1})^{-1}(dx)_\mathfrak p$, so Weil's $Z_\mathfrak p = (1-q^{-1})^{-1}$`zetaV`.

**Results of this file.**
* `volume_congSet` (**volumes of congruence sets**, every finite place): for $t \in \mathcal O_v$ and $j \ge 0$,
  $\nu^{\otimes n}\{x \in L_v : Q(x) \equiv t \bmod \mathfrak p_v^j\} = r_{\mathfrak p^j}(t)\,\nu(\mathfrak p_v^j)^n$, and
  `real_latticeV_eq`: $\nu(\mathfrak p_v^j) = q^{-j}\nu(\mathcal O_v)$.
* `volume_ballQ_eq_localDensity` (**the pushforward of $dx$ along $Q$ has density $\beta_v$**): for $t \ne 0$ and all large $k$,
  $\nu^{\otimes n}\{x \in L_v : Q(x) \in t + \mathfrak p_v^k\} = \beta_v(t)\cdot\nu(t + \mathfrak p_v^k)\cdot\nu(\mathcal O_v)^{n-1}$.
* `aSeq`, `aSeq_rec` (**the recursion**): $a_j = r_{\mathfrak p^j}(0)/q^{jn} = \operatorname{vol}\{x \in L_v : |Q(x)|_v \le q^{-j}\}/\nu(\mathcal O_v)^n$
  satisfies $a_j = c_j + q^{-n}a_{j-2}$ ($j \ge 2$), $c_j = r^{*}_{\mathfrak p^j}(0)/q^{jn}$ the primitive part, and
  $c_j = \gamma q^{-j}$ for $j \ge K_0 = \mathrm{ord}_\pi(4N) + 1$ (Hanke's Lemma 3.4, `DVR.repCountOf_nonZero_add`).
* `volume_nullCone`: $\{x \in L_v : Q(x) = 0\}$ is a null set ($n \ge 1$, $Q$ nondegenerate).
* **`hasSum_zetaInt`** (**the generating-series identity**, every finite place): for $s \ge 0$,
  $$Z_v(s) = \nu(\mathcal O_v)^n\sum_{j \ge 0} q^{-js}\,(a_j - a_{j+1}),\qquad
    a_j - a_{j+1} = \frac{\operatorname{vol}\{x \in L_v : \mathrm{ord}_v Q(x) = j\}}{\nu(\mathcal O_v)^n}.$$
* **`zetaInt_rational`** (**rationality**, every finite place, dyadic included): there is a polynomial $P \in \mathbb Q[X]$ with
  $$Z_v(s)\,(1 - q^{-1-s})(1 - q^{-n-2s}) = \nu(\mathcal O_v)^n\,P(q^{-s}) \qquad (s \ge 0).$$
* `zetaInt_zero`, `zetaInt_pos`: $Z_v(0) = \nu(\mathcal O_v)^n$ and $Z_v(s) > 0$.

The closed form at good places and the convergence-factor bound are in `LocalZetaGood.lean`.

Sources: A. Weil, *Adeles and Algebraic Groups* (1982), §4.3, Lemma 4.3.2 and its proof, pp. 89–90 (the level-set
decomposition $Z_\mathfrak p(s) = q^{-m}(q^m - 1 - N_1) + \sum_{\nu\ge 1}q^{-\nu s}(q^{-m\nu}N_\nu - q^{-m(\nu+1)}N_{\nu+1})$ is Weil's,
there at good places); J. Igusa, *An Introduction to the Theory of Local Zeta Functions* (2000), Ch. 8, 10 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.LocalDensity.NFLocal
import QuadFormsKB.LocalDensity.NFDepth
import QuadFormsKB.Analysis.LocalFourierNF

open IsDedekindDomain NumberField MeasureTheory WithZero Filter Topology
open QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalZeta

open QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v

/-! ### The normalized absolute value -/

/-- Mathlib's norm on $F_v$ is the normalized absolute value: $\|x\| = N(v)^{\log v(x)}$, i.e. $|x|_v = q^{-\mathrm{ord}_v x}$. -/
lemma norm_eq_absNorm_pow {x : Fv} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log (Valued.v x) := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ ((Valued.v).ne_zero_iff.mpr hx)]
  push_cast; rfl

/-! ### The lattice $L_v$ and the reduction maps -/

variable {n : ℕ}

/-- **The lattice** $L_v = \mathcal O_v^n \subset F_v^n$. -/
def latL (n : ℕ) : Set (Fin n → Fv) := {x | ∀ i, Valued.v (x i) ≤ 1}

/-- **The congruence set** $\{x \in L_v : Q(x) \equiv t \bmod \mathfrak p_v^j\}$, for $Q$ over $\mathcal O_v$ and $t \in F_v$. -/
def congSet (Q : QuadForm 𝔬 n) (t : Fv) (j : ℕ) : Set (Fin n → Fv) :=
  {x | x ∈ latL v n ∧ Valued.v (Q.evalIn Fv x - t) ≤ exp (-(j : ℤ))}

/-- The residue ring $\mathcal O_v/\mathfrak p_v^j$ (uniformizer `NF.π v`). -/
abbrev RQ (j : ℕ) : Type := 𝔬 ⧸ Ideal.span {πv ^ j}

lemma valued_sub_le_iff_mk_eq (j : ℕ) (x y : 𝔬) :
    Ideal.Quotient.mk (Ideal.span {πv ^ j}) x = Ideal.Quotient.mk _ y ↔
      Valued.v ((x : Fv) - (y : Fv)) ≤ exp (-(j : ℤ)) := by
  rw [Ideal.Quotient.eq, LocalDensity.NF.mem_span_π_pow]
  rfl

/-- The lift of a residue vector to $L_v$ (by `Quotient.out`). -/
def liftR (j : ℕ) (y : Fin n → RQ v j) : Fin n → Fv := fun i => ((Quotient.out (y i) : 𝔬) : Fv)

/-- The fiber of the reduction map over $y$: the coset $\tilde y + (\mathfrak p_v^j)^n$. -/
def fiberR (j : ℕ) (y : Fin n → RQ v j) : Set (Fin n → Fv) :=
  Set.univ.pi fun i => {z : Fv | Valued.v (z - liftR v j y i) ≤ exp (-(j : ℤ))}

lemma valued_le_one_of_mem_fiberR {j : ℕ} {y : Fin n → RQ v j} {x : Fin n → Fv} (hx : x ∈ fiberR v j y)
    (i : Fin n) : Valued.v (x i) ≤ 1 := by
  have h1 : Valued.v (x i - liftR v j y i) ≤ 1 :=
    (hx i (Set.mem_univ _)).trans (by rw [← exp_zero, exp_le_exp]; omega)
  have h2 : Valued.v (liftR v j y i) ≤ 1 := (Quotient.out (y i)).2
  calc Valued.v (x i) = Valued.v ((x i - liftR v j y i) + liftR v j y i) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ 1 := max_le h1 h2

/-- The point of $\mathcal O_v^n$ underlying $x \in L_v$. -/
def toO (x : Fin n → Fv) (hx : ∀ i, Valued.v (x i) ≤ 1) : Fin n → 𝔬 :=
  fun i => ⟨x i, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hx i)⟩

/-- The reduction $L_v \to (\mathcal O_v/\mathfrak p_v^j)^n$. -/
def redR (j : ℕ) (x : Fin n → Fv) (hx : ∀ i, Valued.v (x i) ≤ 1) : Fin n → RQ v j :=
  fun i => Ideal.Quotient.mk _ (toO v x hx i)

lemma mem_fiberR_iff {j : ℕ} {y : Fin n → RQ v j} {x : Fin n → Fv} :
    x ∈ fiberR v j y ↔ ∃ hx : ∀ i, Valued.v (x i) ≤ 1, redR v j x hx = y := by
  constructor
  · intro h
    refine ⟨valued_le_one_of_mem_fiberR v h, funext fun i => ?_⟩
    have := h i (Set.mem_univ _)
    rw [redR, ← Ideal.Quotient.mk_out (y i), valued_sub_le_iff_mk_eq]
    exact this
  · rintro ⟨hx, rfl⟩ i -
    show Valued.v (x i - ((Quotient.out (redR v j x hx i) : 𝔬) : Fv)) ≤ _
    exact (valued_sub_le_iff_mk_eq v j (toO v x hx i) (Quotient.out (redR v j x hx i))).mp
      (by rw [Ideal.Quotient.mk_out]; rfl)

/-- On $L_v$, $Q(x) \in F_v$ is the image of $Q(x) \in \mathcal O_v$. -/
lemma evalIn_toO (Q : QuadForm 𝔬 n) (x : Fin n → Fv) (hx : ∀ i, Valued.v (x i) ≤ 1) :
    Q.evalIn Fv x = ((Q.eval (toO v x hx) : 𝔬) : Fv) := by
  have := DVR.evalIn_algebraMap Fv Q (toO v x hx)
  exact this

lemma evalIn_redR (Q : QuadForm 𝔬 n) (j : ℕ) (x : Fin n → Fv) (hx : ∀ i, Valued.v (x i) ≤ 1) :
    Q.evalIn (RQ v j) (redR v j x hx) = Ideal.Quotient.mk _ (Q.eval (toO v x hx)) :=
  DVR.evalIn_mk Q _ (toO v x hx)

lemma congSet_eq_biUnion (Q : QuadForm 𝔬 n) (t : 𝔬) (j : ℕ) [Fintype (RQ v j)] [DecidableEq (RQ v j)] :
    congSet v Q (t : Fv) j = ⋃ y ∈ (Finset.univ.filter fun y : Fin n → RQ v j =>
      Q.evalIn (RQ v j) y = Ideal.Quotient.mk _ t), fiberR v j y := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
  constructor
  · rintro ⟨hx, hQ⟩
    have hx : ∀ i, Valued.v (x i) ≤ 1 := hx
    refine ⟨redR v j x hx, ?_, (mem_fiberR_iff v).mpr ⟨hx, rfl⟩⟩
    rw [evalIn_redR, valued_sub_le_iff_mk_eq, ← evalIn_toO]
    exact hQ
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨hx, rfl⟩ := (mem_fiberR_iff v).mp hxy
    refine ⟨hx, ?_⟩
    rw [evalIn_redR, valued_sub_le_iff_mk_eq, ← evalIn_toO] at hy
    exact hy

lemma measurableSet_fiberR (j : ℕ) (y : Fin n → RQ v j) : MeasurableSet (fiberR v j y) := by
  refine MeasurableSet.univ_pi fun i => ?_
  have : {z : Fv | Valued.v (z - liftR v j y i) ≤ exp (-(j : ℤ))} =
      (fun z => z + -liftR v j y i) ⁻¹' (latticeV v j : Set Fv) := by
    ext z; simp [mem_latticeV, sub_eq_add_neg]
  rw [this]
  exact (measurableSet_latticeV v j).preimage (measurable_add_const _)

lemma fiberR_disjoint {j : ℕ} {y y' : Fin n → RQ v j} (h : y ≠ y') :
    Disjoint (fiberR v j y) (fiberR v j y') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨h1, rfl⟩ := (mem_fiberR_iff v).mp hx
  obtain ⟨h2, e⟩ := (mem_fiberR_iff v).mp hx'
  exact h e

/-! ### Volumes of congruence sets, for any translation-invariant measure -/

section Volume


lemma measure_fiberR (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν] (j : ℕ) (y : Fin n → RQ v j) :
    (Measure.pi fun _ : Fin n => ν) (fiberR v j y) = ν (latticeV v j) ^ n := by
  rw [fiberR, Measure.pi_pi]
  have : ∀ i, ν {z : Fv | Valued.v (z - liftR v j y i) ≤ exp (-(j : ℤ))} = ν (latticeV v j) := by
    intro i
    have e : {z : Fv | Valued.v (z - liftR v j y i) ≤ exp (-(j : ℤ))} =
        (fun z => z + -liftR v j y i) ⁻¹' (latticeV v j : Set Fv) := by
      ext z; simp [mem_latticeV, sub_eq_add_neg]
    rw [e]
    exact measure_preimage_add_right ν _ _
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma measurableSet_congSet (Q : QuadForm 𝔬 n) (t : 𝔬) (j : ℕ) : MeasurableSet (congSet v Q (t : Fv) j) := by
  classical
  have := DVR.finite_quot_pow πv (NF.irreducible_π v) j
  have : Fintype (RQ v j) := Fintype.ofFinite _
  rw [congSet_eq_biUnion v Q t j]
  exact Finset.measurableSet_biUnion _ fun y _ => measurableSet_fiberR v j y

/-- **The volume of a congruence set** (every finite place, dyadic included): for $t \in \mathcal O_v$ and $j \ge 0$,
$$\nu^{\otimes n}\{x \in L_v : Q(x) \equiv t \bmod \mathfrak p_v^j\} = r_{\mathfrak p^j}(t)\cdot\nu(\mathfrak p_v^j)^n,$$
$r_{\mathfrak p^j}(t)$ = `DVR.repCount Q (NF.π v) j t` the number of solutions mod $\mathfrak p_v^j$. *Proof:* the set is the
disjoint union of the cosets $\tilde y + (\mathfrak p_v^j)^n$ over the solutions $y$; each has volume $\nu(\mathfrak p_v^j)^n$.
(The diagonal even-dimensional case is `SiegelWeil.muN_congSet`.) -/
@[kb "weil1982" "§4.3, proof of Lemma 4.3.2, p. 89 (measure of {F(x) ≡ 0 mod p^ν} is q^{-mν}N_ν)"]
theorem volume_congSet (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    (Q : QuadForm 𝔬 n) (t : 𝔬) (j : ℕ) :
    (Measure.pi fun _ : Fin n => ν) (congSet v Q (t : Fv) j) =
      (DVR.repCount Q πv j t : ENNReal) * ν (latticeV v j) ^ n := by
  classical
  have := DVR.finite_quot_pow πv (NF.irreducible_π v) j
  haveI : Fintype (RQ v j) := Fintype.ofFinite _
  rw [congSet_eq_biUnion v Q t j, measure_biUnion_finset]
  · simp only [measure_fiberR v ν, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [DVR.repCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro y _ y' _ h
    exact fiberR_disjoint v h
  · intro y _; exact measurableSet_fiberR v j y

end Volume

/-! ### Lattice volumes -/

/-- The zero form in one variable. -/
def zeroForm1 : QuadForm 𝔬 1 := QuadForm.diag 0

lemma latL_one : latL v 1 = Set.univ.pi fun _ : Fin 1 => (latticeV v 0 : Set Fv) := by
  ext x; simp [latL, mem_latticeV]

/-- **$\nu(\mathcal O_v) = q^j\,\nu(\mathfrak p_v^j)$** for every translation-invariant $\nu$ (the case $n = 1$, $Q = 0$ of
`volume_congSet`: $\mathcal O_v$ is the disjoint union of $q^j$ translates of $\mathfrak p_v^j$). -/
theorem measure_latticeV_zero (ν : Measure (v.adicCompletion F)) [SigmaFinite ν]
    [Measure.IsAddRightInvariant ν] (j : ℕ) :
    ν (latticeV v 0) = (DVR.q 𝔬 : ENNReal) ^ j * ν (latticeV v j) := by
  have h := volume_congSet v ν (zeroForm1 v) 0 j
  have e1 : congSet v (zeroForm1 v) ((0 : 𝔬) : Fv) j = latL v 1 := by
    ext x
    simp only [congSet, Set.mem_ofPred_eq, and_iff_left_iff_imp]
    intro _
    simp [zeroForm1, QuadForm.evalIn, QuadForm.diag]
  rw [e1, latL_one, Measure.pi_pi] at h
  simp only [Finset.univ_unique, Finset.prod_singleton, pow_one] at h
  rw [h]
  congr 1
  have := DVR.finite_quot_pow πv (NF.irreducible_π v) j
  have hc : DVR.repCount (zeroForm1 v) πv j 0 = DVR.q 𝔬 ^ j := by
    rw [DVR.repCount]
    have : ∀ x : Fin 1 → RQ v j, (zeroForm1 v).evalIn (RQ v j) x = Ideal.Quotient.mk _ 0 := by
      intro x; simp [zeroForm1, QuadForm.evalIn, QuadForm.diag]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv this), Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 1),
      Fintype.card_fin, pow_one, DVR.natCard_quot_pow πv (NF.irreducible_π v)]
  rw [hc]; push_cast; rfl

lemma q_pos : 0 < DVR.q 𝔬 := DVR.q_pos

lemma q_ge_two : 2 ≤ DVR.q 𝔬 := by
  have : 1 < Nat.card (IsLocalRing.ResidueField 𝔬) := Finite.one_lt_card
  exact this

/-- **$\nu(\mathfrak p_v^j) = q^{-j}\nu(\mathcal O_v)$** (real volumes). -/
theorem real_latticeV_eq (ν : Measure (v.adicCompletion F)) [SigmaFinite ν]
    [Measure.IsAddRightInvariant ν] (j : ℕ) :
    ν.real (latticeV v j) = ν.real (latticeV v 0) * ((DVR.q 𝔬 : ℝ) ^ j)⁻¹ := by
  have hq : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast q_pos v
  rw [Measure.real, Measure.real, measure_latticeV_zero v ν j, ENNReal.toReal_mul]
  rw [ENNReal.toReal_pow, ENNReal.toReal_natCast]
  field_simp

/-! ### The sequence $a_j = r_{\mathfrak p^j}(0)/q^{jn}$ and its recursion -/

/-- **$a_j = r_{\mathfrak p^j}(0)/q^{jn}$**, the normalized volume of $\{x \in L_v : |Q(x)|_v \le q^{-j}\}$ (`real_congSet_zero`). Rational. -/
def aSeq (Q : QuadForm 𝔬 n) (j : ℕ) : ℚ := (DVR.repCount Q πv j 0 : ℚ) / (DVR.q 𝔬 : ℚ) ^ (j * n)

/-- **$c_j = r^{*}_{\mathfrak p^j}(0)/q^{jn}$**, the primitive (non-Zero-type, $x \not\equiv 0 \bmod \mathfrak p$) part of $a_j$. -/
def cSeq (Q : QuadForm 𝔬 n) (j : ℕ) : ℚ :=
  (DVR.repCountOf Q πv j 0 (fun x => ¬ DVR.IsZeroType πv j x) : ℚ) / (DVR.q 𝔬 : ℚ) ^ (j * n)

/-- **The volume of the level set** $\{x \in L_v : |Q(x)|_v \le q^{-j}\}$ is $\nu(\mathcal O_v)^n\,a_j$. -/
theorem real_congSet_zero (ν : Measure (v.adicCompletion F)) [SigmaFinite ν]
    [Measure.IsAddRightInvariant ν] (Q : QuadForm 𝔬 n) (j : ℕ) :
    (Measure.pi fun _ : Fin n => ν).real (congSet v Q ((0 : 𝔬) : Fv) j) =
      ν.real (latticeV v 0) ^ n * (aSeq v Q j : ℝ) := by
  rw [Measure.real, volume_congSet, ENNReal.toReal_mul, ENNReal.toReal_pow, ← Measure.real,
    real_latticeV_eq, ENNReal.toReal_natCast, aSeq]
  push_cast
  rw [mul_pow, inv_pow, ← pow_mul, mul_comm j n]
  ring

/-- **The recursion** (Weil 1982, proof of Lemma 4.3.2, p. 89, $x = \pi^\nu x'$; Hanke's Zero type): for $j \ge 2$,
$a_j = c_j + q^{-n}a_{j-2}$, because the Zero-type solutions mod $\mathfrak p^j$ are $x = \pi y$ with $Q(y) \equiv 0 \bmod \mathfrak p^{j-2}$,
and there are $q^n r_{\mathfrak p^{j-2}}(0)$ of them (`DVR.repCountZero_eq`). -/
theorem aSeq_rec (Q : QuadForm 𝔬 n) (j : ℕ) (hj : 2 ≤ j) :
    aSeq v Q j = cSeq v Q j + ((DVR.q 𝔬 : ℚ) ^ n)⁻¹ * aSeq v Q (j - 2) := by
  have hq : (0 : ℚ) < DVR.q 𝔬 := by exact_mod_cast q_pos v
  have h1 := DVR.repCount_eq_zero_add_nonZero Q πv (NF.irreducible_π v) j 0
  have h2 := DVR.repCountZero_eq Q πv (NF.irreducible_π v) 0 0 (by ring) j hj
  rw [aSeq, cSeq, aSeq, h1, h2]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  rw [show k + 2 - 2 = k by omega]
  generalize (DVR.repCountOf Q πv (k + 2) 0 fun x => ¬DVR.IsZeroType πv (k + 2) x) = B
  generalize DVR.repCount Q πv k 0 = A
  push_cast
  rw [show (k + 2) * n = n + k * n + n by ring, pow_add, pow_add]
  field_simp
  ring

/-- **The residue $2 \ne 0$ in $\mathcal O_v$.** -/
lemma two_ne_zero_O : (2 : 𝔬) ≠ 0 := by
  intro h
  have : ((2 : 𝔬) : Fv) = 0 := by rw [h]; rfl
  simp at this

/-- **The primitive part is geometric** (Hanke 2004, Lemma 3.4, p. 361, at every prime, dyadic included): with
$e = \mathrm{ord}_\pi 2$ and $K_0 = $ `DVR.depthLevel Q π e` $= \mathrm{ord}_\pi(4N) + 1$,
$c_j = \gamma\,q^{-j}$ for all $j \ge K_0$, where $\gamma = r^{*}_{\mathfrak p^{K_0}}(0)/q^{(n-1)K_0}$. -/
theorem cSeq_geom (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (e : ℕ)
    (he : πv ^ e ∣ 2 ∧ ¬ πv ^ (e + 1) ∣ 2) (j : ℕ) (hj : DVR.depthLevel Q πv e ≤ j) :
    cSeq v Q j = cSeq v Q (DVR.depthLevel Q πv e) * (DVR.q 𝔬 : ℚ) ^ (DVR.depthLevel Q πv e) *
      ((DVR.q 𝔬 : ℚ)⁻¹) ^ j := by
  have hq : (0 : ℚ) < DVR.q 𝔬 := by exact_mod_cast q_pos v
  set K := DVR.depthLevel Q πv e
  obtain ⟨l, rfl⟩ : ∃ l, j = K + l := ⟨j - K, by omega⟩
  have h := DVR.repCountOf_nonZero_add Q hQ πv (NF.irreducible_π v) (two_ne_zero_O v) e he 0 K l le_rfl
  rw [cSeq, cSeq, h]
  generalize DVR.repCountOf Q πv K 0 (fun x => ¬ DVR.IsZeroType πv K x) = B
  push_cast
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, inv_pow, show (K + l) * (m + 1) = K * (m + 1) + m * l + l by ring,
    pow_add, pow_add, show K + l = K + l from rfl, pow_add]
  field_simp

/-! ### Basic set facts -/

lemma latL_eq : latL v n = Set.univ.pi fun _ : Fin n => (latticeV v 0 : Set Fv) := by
  ext x; simp [latL, mem_latticeV]

lemma measure_latL (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] :
    (Measure.pi fun _ : Fin n => ν) (latL v n) = ν (latticeV v 0) ^ n := by
  rw [latL_eq, Measure.pi_pi]; simp

lemma measurableSet_latL : MeasurableSet (latL v n) := by
  rw [latL_eq]; exact MeasurableSet.univ_pi fun _ => measurableSet_latticeV v 0

lemma congSet_subset_latL (Q : QuadForm 𝔬 n) (t : Fv) (j : ℕ) : congSet v Q t j ⊆ latL v n :=
  fun _ hx => hx.1

lemma congSet_anti (Q : QuadForm 𝔬 n) (t : Fv) {i j : ℕ} (hij : i ≤ j) : congSet v Q t j ⊆ congSet v Q t i := by
  rintro x ⟨hx, h⟩
  exact ⟨hx, h.trans (by rw [exp_le_exp]; omega)⟩

lemma valued_evalIn_le_one (Q : QuadForm 𝔬 n) {x : Fin n → Fv} (hx : x ∈ latL v n) :
    Valued.v (Q.evalIn Fv x) ≤ 1 := by
  rw [evalIn_toO v Q x hx]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (Q.eval (toO v x hx)).2

lemma congSet_zero_eq (Q : QuadForm 𝔬 n) : congSet v Q ((0 : 𝔬) : Fv) 0 = latL v n := by
  ext x
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  simpa using valued_evalIn_le_one v Q h

lemma norm_le_one_of_valued {x : Fv} (hx : Valued.v x ≤ 1) : ‖x‖ ≤ 1 := by
  by_cases h0 : x = 0
  · simp [h0]
  rw [norm_eq_absNorm_pow v h0]
  have hl : WithZero.log (Valued.v x) ≤ 0 := by
    have := (WithZero.log_le_log ((Valued.v).ne_zero_iff.mpr h0) one_ne_zero).mpr hx
    simpa using this
  have hN : (1 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
    have : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    exact_mod_cast this
  exact zpow_le_one_of_nonpos₀ hN hl

/-- **On the level set $\mathrm{ord}_v Q(x) = j$, $|Q(x)|_v = q^{-j}$.** -/
lemma norm_evalIn_of_mem_diff (Q : QuadForm 𝔬 n) (j : ℕ) {x : Fin n → Fv}
    (hx : x ∈ congSet v Q ((0 : 𝔬) : Fv) j \ congSet v Q ((0 : 𝔬) : Fv) (j + 1)) :
    ‖Q.evalIn Fv x‖ = ((DVR.q 𝔬 : ℝ) ^ j)⁻¹ := by
  obtain ⟨⟨hL, h1⟩, h2⟩ := hx
  simp only [congSet, Set.mem_ofPred_eq, not_and] at h2
  have h2 := h2 hL
  simp only [ZeroMemClass.coe_zero, sub_zero] at h1 h2
  have h0 : Q.evalIn Fv x ≠ 0 := by
    intro h; apply h2; rw [h]; simp
  have hne := (Valued.v).ne_zero_iff.mpr h0
  have e : WithZero.log (Valued.v (Q.evalIn Fv x)) = -(j : ℤ) := by
    rw [← WithZero.exp_log hne, exp_le_exp] at h1 h2
    push_cast at h2
    omega
  rw [norm_eq_absNorm_pow v h0, e, ← NF.q_completion, zpow_neg, zpow_natCast]

/-! ### The sequence $a_j$: monotonicity and limit -/

lemma haarV_real_O : (haarV v).real (latticeV v 0) = 1 := by
  rw [haarV_real_latticeV]; simp

lemma aSeq_eq_haar (Q : QuadForm 𝔬 n) (j : ℕ) :
    (aSeq v Q j : ℝ) = (Measure.pi fun _ : Fin n => haarV v).real (congSet v Q ((0 : 𝔬) : Fv) j) := by
  rw [real_congSet_zero, haarV_real_O]; simp

lemma measure_latL_haar_ne_top : (Measure.pi fun _ : Fin n => haarV v) (latL v n) ≠ ⊤ := by
  rw [measure_latL]
  exact ENNReal.pow_ne_top (isCompact_latticeV v 0).measure_lt_top.ne

lemma aSeq_zero (Q : QuadForm 𝔬 n) : (aSeq v Q 0 : ℝ) = 1 := by
  rw [aSeq_eq_haar, congSet_zero_eq, Measure.real, measure_latL, ENNReal.toReal_pow, ← Measure.real,
    haarV_real_O, one_pow]

lemma aSeq_antitone (Q : QuadForm 𝔬 n) : Antitone fun j => (aSeq v Q j : ℝ) := by
  intro i j hij
  simp only [aSeq_eq_haar]
  exact measureReal_mono (congSet_anti v Q _ hij)
    (measure_ne_top_of_subset (congSet_subset_latL v Q _ i) (measure_latL_haar_ne_top v))

lemma aSeq_nonneg (Q : QuadForm 𝔬 n) (j : ℕ) : 0 ≤ (aSeq v Q j : ℝ) := by
  rw [aSeq_eq_haar]; exact measureReal_nonneg

/-- **$a_j \to 0$** ($n \ge 1$, $Q$ nondegenerate, every finite place): the limit $\ell$ of the decreasing sequence $a_j$
satisfies $\ell = q^{-n}\ell$ by `aSeq_rec`, since $c_j = \gamma q^{-j} \to 0$ (`cSeq_geom`). -/
theorem tendsto_aSeq (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) :
    Tendsto (fun j => (aSeq v Q j : ℝ)) atTop (𝓝 0) := by
  obtain ⟨e, he⟩ := DVR.exists_pow_dvd_not_dvd πv (NF.irreducible_π v) (two_ne_zero_O v)
  set K := DVR.depthLevel Q πv e
  have hq1 : (1 : ℝ) < DVR.q 𝔬 := by exact_mod_cast (q_ge_two v)
  have hq0 : (0 : ℝ) < DVR.q 𝔬 := by linarith
  have hT := tendsto_atTop_ciInf (aSeq_antitone v Q) ⟨0, by rintro _ ⟨j, rfl⟩; exact aSeq_nonneg v Q j⟩
  set ℓ := ⨅ j, (aSeq v Q j : ℝ)
  -- c_{j} → 0
  have hc : Tendsto (fun j => (cSeq v Q (j + 2) : ℝ)) atTop (𝓝 0) := by
    have hg : Tendsto (fun j : ℕ => ((cSeq v Q K : ℝ) * (DVR.q 𝔬 : ℝ) ^ K) * ((DVR.q 𝔬 : ℝ)⁻¹) ^ (j + 2))
        atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ hq1)).comp
        (tendsto_add_atTop_nat 2)
      simpa using this.const_mul ((cSeq v Q K : ℝ) * (DVR.q 𝔬 : ℝ) ^ K)
    refine hg.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    refine ⟨K, fun j hj => ?_⟩
    rw [cSeq_geom v Q hQ hn e he (j + 2) (by omega)]
    push_cast; ring
  have h2 : Tendsto (fun j => (aSeq v Q (j + 2) : ℝ)) atTop (𝓝 (0 + ((DVR.q 𝔬 : ℝ) ^ n)⁻¹ * ℓ)) := by
    refine (hc.add (hT.const_mul _)).congr fun j => ?_
    rw [aSeq_rec v Q (j + 2) (by omega), show j + 2 - 2 = j by omega]
    push_cast; ring
  have h3 : Tendsto (fun j => (aSeq v Q (j + 2) : ℝ)) atTop (𝓝 ℓ) := hT.comp (tendsto_add_atTop_nat 2)
  have hl := tendsto_nhds_unique h3 h2
  have hlt : ((DVR.q 𝔬 : ℝ) ^ n)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))
  have : ℓ = 0 := by nlinarith [show ℓ * (1 - ((DVR.q 𝔬 : ℝ) ^ n)⁻¹) = 0 by linarith]
  rwa [this] at hT

/-! ### The null cone -/

/-- **The null cone** $\{x \in L_v : Q(x) = 0\}$. -/
def nullCone (Q : QuadForm 𝔬 n) : Set (Fin n → Fv) := {x | x ∈ latL v n ∧ Q.evalIn Fv x = 0}

lemma nullCone_subset (Q : QuadForm 𝔬 n) (j : ℕ) : nullCone v Q ⊆ congSet v Q ((0 : 𝔬) : Fv) j := by
  rintro x ⟨hx, h⟩
  exact ⟨hx, by simp [h]⟩

/-- **The null cone is a null set** for every translation-invariant $\nu$ finite on compacts ($n \ge 1$, $Q$ nondegenerate,
every finite place): its measure is at most $\nu(\mathcal O_v)^na_j \to 0$. -/
@[kb "weil1982" "§4.3, p. 89 (V = {F ≠ 0} carries the full measure)"]
theorem measure_nullCone (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin n => ν) (nullCone v Q) = 0 := by
  have hfin : ∀ j, (Measure.pi fun _ : Fin n => ν) (congSet v Q ((0 : 𝔬) : Fv) j) ≠ ⊤ := fun j =>
    measure_ne_top_of_subset (congSet_subset_latL v Q _ j)
      (by rw [measure_latL]; exact ENNReal.pow_ne_top (isCompact_latticeV v 0).measure_lt_top.ne)
  have hle : ∀ j, (Measure.pi fun _ : Fin n => ν) (nullCone v Q) ≤
      ENNReal.ofReal (ν.real (latticeV v 0) ^ n * (aSeq v Q j : ℝ)) := by
    intro j
    rw [← real_congSet_zero, Measure.real, ENNReal.ofReal_toReal (hfin j)]
    exact measure_mono (nullCone_subset v Q j)
  have ht : Tendsto (fun j => ENNReal.ofReal (ν.real (latticeV v 0) ^ n * (aSeq v Q j : ℝ))) atTop (𝓝 0) := by
    have := ((tendsto_aSeq v Q hQ hn).const_mul (ν.real (latticeV v 0) ^ n))
    rw [mul_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le

/-! ### The local zeta function and the generating-series identity -/

/-- **The local zeta function** (Weil 1982, §4.3, (1)–(2), p. 89), for a measure $\nu$ on $F_v$ and $s \in \mathbb R$:
$$Z_v(s) = \int_{V_v}|Q(x)|_v^s\,\mathbf 1_{L_v}(x)\,d\nu^{\otimes n}(x) = \int_{L_v}|Q(x)|_v^s\,d\nu^{\otimes n}(x),$$
with $|\cdot|_v = \|\cdot\|$ the normalized absolute value and $L_v = \mathcal O_v^n$. For $\nu$ = `haarV` this is
$(1 - q^{-1})\cdot$ Weil's $Z_\mathfrak p(s)$ (Weil uses $d'x = (1-q^{-1})^{-1}(dx)_\mathfrak p$). -/
@[kb "weil1982" "§4.3, (1)–(2), p. 89 (local zeta-function)"]
def zetaInt (ν : Measure (v.adicCompletion F)) (Q : QuadForm 𝔬 n) (s : ℝ) : ℝ :=
  ∫ x in latL v n, ‖Q.evalIn Fv x‖ ^ s ∂(Measure.pi fun _ : Fin n => ν)

/-- The level set $\{x \in L_v : \mathrm{ord}_v Q(x) = j\}$. -/
def levelSet (Q : QuadForm 𝔬 n) (j : ℕ) : Set (Fin n → Fv) :=
  congSet v Q ((0 : 𝔬) : Fv) j \ congSet v Q ((0 : 𝔬) : Fv) (j + 1)

lemma measurableSet_levelSet (Q : QuadForm 𝔬 n) (j : ℕ) : MeasurableSet (levelSet v Q j) :=
  (measurableSet_congSet v Q 0 j).diff (measurableSet_congSet v Q 0 (j + 1))

lemma levelSet_disjoint (Q : QuadForm 𝔬 n) : Pairwise (Function.onFun Disjoint (levelSet v Q)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact Set.disjoint_left.mpr fun x hx hy => hx.2 (congSet_anti v Q _ (by omega) hy.1)
  · exact Set.disjoint_left.mpr fun x hx hy => hy.2 (congSet_anti v Q _ (by omega) hx.1)

lemma iUnion_levelSet (Q : QuadForm 𝔬 n) : (⋃ j, levelSet v Q j) = latL v n \ nullCone v Q := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_sdiff, nullCone, Set.mem_ofPred_eq, not_and]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨hj.1.1, fun _ h0 => ?_⟩
    exact hj.2 (nullCone_subset v Q (j + 1) ⟨hj.1.1, h0⟩)
  · rintro ⟨hL, h0⟩
    have h0 := h0 hL
    have hne := (Valued.v).ne_zero_iff.mpr h0
    have h1 := valued_evalIn_le_one v Q hL
    set k := WithZero.log (Valued.v (Q.evalIn Fv x))
    have hk : k ≤ 0 := by
      have := (WithZero.log_le_log hne one_ne_zero).mpr h1; simpa using this
    refine ⟨(-k).toNat, ⟨hL, ?_⟩, fun h => ?_⟩
    · simp only [ZeroMemClass.coe_zero, sub_zero]
      rw [← WithZero.exp_log hne, exp_le_exp]; omega
    · have h2 := h.2
      simp only [ZeroMemClass.coe_zero, sub_zero] at h2
      rw [← WithZero.exp_log hne, exp_le_exp] at h2; omega

lemma real_levelSet (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (Q : QuadForm 𝔬 n) (j : ℕ) :
    (Measure.pi fun _ : Fin n => ν).real (levelSet v Q j) =
      ν.real (latticeV v 0) ^ n * ((aSeq v Q j : ℝ) - aSeq v Q (j + 1)) := by
  rw [levelSet, measureReal_sdiff (congSet_anti v Q _ (Nat.le_succ j)) (measurableSet_congSet v Q 0 (j + 1))
    (measure_ne_top_of_subset (congSet_subset_latL v Q _ j)
      (by rw [measure_latL]; exact ENNReal.pow_ne_top (isCompact_latticeV v 0).measure_lt_top.ne)),
    real_congSet_zero, real_congSet_zero]
  ring

lemma rpow_inv_pow (q : ℝ) (hq : 0 < q) (s : ℝ) (j : ℕ) : ((q ^ j)⁻¹) ^ s = (q ^ (-s)) ^ j := by
  rw [Real.inv_rpow (pow_nonneg hq.le _), ← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hq.le, ← Real.rpow_neg hq.le]
  congr 1; ring

/-- **The generating-series identity** (every finite place, dyadic included; Weil 1982, proof of Lemma 4.3.2, p. 89):
for $Q$ nondegenerate over $\mathcal O_v$ in $n \ge 1$ variables, $\nu$ translation-invariant and finite on compacts, and real $s \ge 0$,
$$Z_v(s) = \nu(\mathcal O_v)^n\sum_{j \ge 0}(q^{-s})^j\,(a_j - a_{j+1}),\qquad a_j = \frac{r_{\mathfrak p^j}(0)}{q^{jn}},$$
where $\nu(\mathcal O_v)^n(a_j - a_{j+1}) = \operatorname{vol}\{x \in L_v : \mathrm{ord}_v Q(x) = j\}$ (`real_levelSet`) and
$\nu(\mathcal O_v)^na_j = \operatorname{vol}\{x \in L_v : Q(x) \equiv 0 \bmod \mathfrak p_v^j\}$ (`real_congSet_zero`).
*Proof:* $L_v$ minus the null cone (`measure_nullCone`) is the disjoint union of the level sets, on which $|Q(x)|_v^s = q^{-js}$. -/
@[kb "weil1982" "§4.3, proof of Lemma 4.3.2, p. 89 (Z'_p(s) as a series over the levels ν)"]
theorem hasSum_zetaInt (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun j : ℕ => ((DVR.q 𝔬 : ℝ) ^ (-s)) ^ j *
      (ν.real (latticeV v 0) ^ n * ((aSeq v Q j : ℝ) - aSeq v Q (j + 1)))) (zetaInt v ν Q s) := by
  set μ := Measure.pi fun _ : Fin n => ν
  have hq0 : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast q_pos v
  have hLfin : μ (latL v n) ≠ ⊤ := by
    rw [measure_latL]; exact ENNReal.pow_ne_top (isCompact_latticeV v 0).measure_lt_top.ne
  have hcont : Continuous fun x : Fin n → Fv => Q.evalIn Fv x := by
    unfold QuadForm.evalIn
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
      split_ifs <;> fun_prop
  have hmeas : Measurable fun x : Fin n → Fv => ‖Q.evalIn Fv x‖ ^ s :=
    (continuous_norm.comp hcont).measurable.pow_const s
  have hint : IntegrableOn (fun x : Fin n → Fv => ‖Q.evalIn Fv x‖ ^ s) (⋃ j, levelSet v Q j) μ := by
    rw [iUnion_levelSet]
    refine (Measure.integrableOn_of_bounded (M := 1) hLfin hmeas.aestronglyMeasurable ?_).mono_set
      Set.sdiff_subset
    refine (ae_restrict_iff' (measurableSet_latL v)).mpr (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one (norm_nonneg _) (norm_le_one_of_valued v (valued_evalIn_le_one v Q hx)) hs
  have h := hasSum_integral_iUnion (measurableSet_levelSet v Q) (levelSet_disjoint v Q) hint
  have e1 : ∫ x in ⋃ j, levelSet v Q j, ‖Q.evalIn Fv x‖ ^ s ∂μ = zetaInt v ν Q s := by
    rw [iUnion_levelSet, zetaInt]
    exact setIntegral_congr_set (sdiff_null_ae_eq_self (measure_nullCone v ν Q hQ hn))
  rw [e1] at h
  convert h using 1
  funext j
  rw [setIntegral_congr_fun (measurableSet_levelSet v Q j)
    (g := fun _ => ((DVR.q 𝔬 : ℝ) ^ (-s)) ^ j) (fun x hx => by
      simp only
      rw [norm_evalIn_of_mem_diff v Q j hx, rpow_inv_pow _ hq0]),
    setIntegral_const, real_levelSet, smul_eq_mul, mul_comm]

/-- **$Z_v(0) = \nu(\mathcal O_v)^n$** (the null cone is null). -/
theorem zetaInt_zero (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (Q : QuadForm 𝔬 n) :
    zetaInt v ν Q 0 = ν.real (latticeV v 0) ^ n := by
  simp only [zetaInt, Real.rpow_zero, setIntegral_const, smul_eq_mul, mul_one, Measure.real, measure_latL,
    ENNReal.toReal_pow]

/-! ### Rationality -/

/-- **A series lemma.** If $\sum_j X^jd_j = T$, $|\rho X| < 1$, and $d_j = \alpha\rho^j + \beta d_{j-2}$ for $j \ge K \ge 2$, then
$$(1 - \rho X)(1 - \beta X^2)\,T = (1 - \rho X)\sum_{j<K}X^j e_j + \alpha(\rho X)^K,\qquad e_j = d_j - \beta\,d_{j-2}\ (d_{-1} = d_{-2} = 0).$$ -/
theorem series_rational (d : ℕ → ℝ) (X ρ α β T : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hT : HasSum (fun j => X ^ j * d j) T) (hρ : |ρ * X| < 1)
    (hrec : ∀ j, K ≤ j → d j = α * ρ ^ j + β * d (j - 2)) :
    (1 - ρ * X) * ((1 - β * X ^ 2) * T) =
      (1 - ρ * X) * ∑ j ∈ Finset.range K, X ^ j * (d j - β * if 2 ≤ j then d (j - 2) else 0) +
        α * (ρ * X) ^ K := by
  set e : ℕ → ℝ := fun j => d j - β * if 2 ≤ j then d (j - 2) else 0
  -- the shifted series
  have hS : HasSum (fun j => X ^ j * (β * if 2 ≤ j then d (j - 2) else 0)) (β * X ^ 2 * T) := by
    rw [← hasSum_nat_add_iff' 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, show ¬ (2 ≤ 0) by omega,
      show ¬ (2 ≤ 1) by omega, ite_false, mul_zero, add_zero, sub_zero, le_add_iff_nonneg_left,
      zero_le, ite_true, Nat.add_sub_cancel]
    convert hT.mul_left (β * X ^ 2) using 1
    funext j; ring
  have hE : HasSum (fun j => X ^ j * e j) ((1 - β * X ^ 2) * T) := by
    convert hT.sub hS using 1
    · funext j; simp only [e]; ring
    · ring
  have hE2 := (hasSum_nat_add_iff' K).mpr hE
  have hG : HasSum (fun j => X ^ (j + K) * e (j + K)) (α * (ρ * X) ^ K * (1 - ρ * X)⁻¹) := by
    convert (hasSum_geometric_of_abs_lt_one hρ).mul_left (α * (ρ * X) ^ K) using 1
    funext j
    simp only [e, show 2 ≤ j + K by omega, ite_true]
    rw [hrec (j + K) (by omega), show j + K - 2 = j + K - 2 from rfl]
    ring
  have hu := hE2.unique hG
  have hne : 1 - ρ * X ≠ 0 := by
    have := (abs_lt.mp hρ).2; linarith
  have hu' : (1 - β * X ^ 2) * T = ∑ i ∈ Finset.range K, X ^ i * e i + α * (ρ * X) ^ K * (1 - ρ * X)⁻¹ := by
    linarith
  rw [hu']
  simp only [e]
  field_simp

/-- **The local zeta function is a rational function of $q^{-s}$** (every finite place, **dyadic included**): for $Q$
nondegenerate over $\mathcal O_v$ in $n \ge 1$ variables and $\nu$ translation-invariant and finite on compacts, there is a polynomial
$P \in \mathbb Q[X]$ (depending only on $Q$, not on $\nu$) such that for all real $s \ge 0$, with $X = q^{-s}$,
$$Z_v(s)\,(1 - q^{-1}X)(1 - q^{-n}X^2) = \nu(\mathcal O_v)^n\,P(X).$$
$P$ is explicit: $P = (1 - q^{-1}X)\sum_{j<K}e_jX^j + \gamma(1-q^{-1})q^{-K}X^K$, $K = \max(K_0, 2)$, $K_0 = \mathrm{ord}_\pi(4N)+1$,
$e_j = (a_j - a_{j+1}) - q^{-n}(a_{j-2} - a_{j-1})$, from the finitely many counts $r_{\mathfrak p^j}(0)$, $j \le K + 1$
(stabilization, Hanke 2004, Lemma 3.4). -/
@[kb "weil1982" "§4.3, Lemma 4.3.2, p. 89 (rationality; the closed form is at almost all p)"]
theorem zetaInt_rational (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) :
    ∃ P : Polynomial ℚ, ∀ (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
      [IsFiniteMeasureOnCompacts ν] (s : ℝ), 0 ≤ s →
      zetaInt v ν Q s * ((1 - (DVR.q 𝔬 : ℝ)⁻¹ * (DVR.q 𝔬 : ℝ) ^ (-s)) *
        (1 - ((DVR.q 𝔬 : ℝ) ^ n)⁻¹ * ((DVR.q 𝔬 : ℝ) ^ (-s)) ^ 2)) =
      ν.real (latticeV v 0) ^ n * Polynomial.aeval ((DVR.q 𝔬 : ℝ) ^ (-s)) P := by
  obtain ⟨e, he⟩ := DVR.exists_pow_dvd_not_dvd πv (NF.irreducible_π v) (two_ne_zero_O v)
  set K0 := DVR.depthLevel Q πv e
  set K := max K0 2
  set qQ : ℚ := ((DVR.q 𝔬 : ℕ) : ℚ)
  set dQ : ℕ → ℚ := fun j => aSeq v Q j - aSeq v Q (j + 1)
  set γ : ℚ := cSeq v Q K0 * qQ ^ K0
  set αQ : ℚ := γ * (1 - qQ⁻¹)
  set eQ : ℕ → ℚ := fun j => dQ j - (qQ ^ n)⁻¹ * if 2 ≤ j then dQ (j - 2) else 0
  refine ⟨(1 - Polynomial.C qQ⁻¹ * Polynomial.X) *
      ∑ j ∈ Finset.range K, Polynomial.C (eQ j) * Polynomial.X ^ j +
      Polynomial.C (αQ * qQ⁻¹ ^ K) * Polynomial.X ^ K, ?_⟩
  intro ν _ _ _ s hs
  have hq1 : (1 : ℝ) < DVR.q 𝔬 := by exact_mod_cast (q_ge_two v)
  have hq0 : (0 : ℝ) < DVR.q 𝔬 := by linarith
  set c := ν.real (latticeV v 0) ^ n
  set X : ℝ := (DVR.q 𝔬 : ℝ) ^ (-s)
  have hX0 : 0 < X := Real.rpow_pos_of_pos hq0 _
  have hX1 : X ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1.le (by linarith)
  -- the recursion for d_j = c (a_j - a_{j+1})
  have hrecQ : ∀ j, K ≤ j → dQ j = αQ * qQ⁻¹ ^ j + (qQ ^ n)⁻¹ * dQ (j - 2) := by
    intro j hj
    simp only [dQ]
    rw [aSeq_rec v Q j (by omega), aSeq_rec v Q (j + 1) (by omega),
      cSeq_geom v Q hQ hn e he j (by omega), cSeq_geom v Q hQ hn e he (j + 1) (by omega),
      show j + 1 - 2 = j - 2 + 1 by omega]
    simp only [αQ, γ, qQ]
    ring
  have key := series_rational (fun j => c * ((aSeq v Q j : ℝ) - aSeq v Q (j + 1))) X (DVR.q 𝔬 : ℝ)⁻¹
    (c * (αQ : ℝ)) ((DVR.q 𝔬 : ℝ) ^ n)⁻¹ (zetaInt v ν Q s) K (le_max_right _ _)
    (hasSum_zetaInt v ν Q hQ hn hs)
    (by
      rw [abs_of_nonneg (by positivity)]
      calc (DVR.q 𝔬 : ℝ)⁻¹ * X ≤ (DVR.q 𝔬 : ℝ)⁻¹ * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hq1)
    (by
      intro j hj
      have := congrArg (fun r : ℚ => (r : ℝ)) (hrecQ j hj)
      simp only [dQ, qQ] at this
      push_cast at this
      rw [this]; ring)
  rw [mul_comm (zetaInt v ν Q s), mul_assoc, key]
  simp only [map_add, map_mul, map_sub, map_one, map_sum, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    eq_ratCast, eQ, dQ, αQ, γ, qQ]
  push_cast
  rw [mul_add]
  congr 1
  · simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun (j : ℕ) (_ : j ∈ Finset.range K) => ?_
    split_ifs <;> push_cast <;> ring
  · ring

/-- **$Z_v(s) > 0$** for $s \ge 0$ when $\nu(\mathcal O_v) > 0$ ($n \ge 1$, $Q$ nondegenerate, every finite place): some level set has
positive volume, since $a_0 = 1$ and $a_j \to 0$. -/
theorem zetaInt_pos (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (hν : 0 < ν.real (latticeV v 0)) (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate)
    (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) : 0 < zetaInt v ν Q s := by
  have hq0 : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast q_pos v
  have hX : 0 < (DVR.q 𝔬 : ℝ) ^ (-s) := Real.rpow_pos_of_pos hq0 _
  have hd : ∀ j, 0 ≤ (aSeq v Q j : ℝ) - aSeq v Q (j + 1) := fun j =>
    sub_nonneg.mpr (aSeq_antitone v Q (Nat.le_succ j))
  obtain ⟨j, hj⟩ : ∃ j, 0 < (aSeq v Q j : ℝ) - aSeq v Q (j + 1) := by
    by_contra h
    push Not at h
    have hc : ∀ j, (aSeq v Q j : ℝ) = 1 := by
      intro j
      induction j with
      | zero => exact aSeq_zero v Q
      | succ j ih => linarith [h j, hd j]
    have := tendsto_aSeq v Q hQ hn
    simp only [hc] at this
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)
  have h := hasSum_zetaInt v ν Q hQ hn hs
  refine lt_of_lt_of_le ?_ (le_hasSum h j fun i _ => by have := hd i; positivity)
  have := hd j
  positivity

/-! ### The density of the pushforward of $dx$ along $Q$ is $\beta_v$ -/

/-- **The pushforward of $dx|_{L_v}$ along $Q$ has density $\beta_v$** (every finite place, dyadic included): for $t \in \mathcal O_v$,
$t \ne 0$, and all large $k$,
$$\nu^{\otimes n}\{x \in L_v : Q(x) \in t + \mathfrak p_v^k\} = \beta_v(t)\cdot\nu(\mathfrak p_v^k)\cdot\nu(\mathcal O_v)^{n-1},$$
where $\nu(\mathfrak p_v^k) = \nu(t + \mathfrak p_v^k)$ and $\beta_v(t)$ = `DVR.localDensity Q (NF.π v) t` (Hanke (5.1)–(5.2)). So
$Q_*(\mathbf 1_{L_v}dx) = \nu(\mathcal O_v)^{n-1}\beta_v(t)\,dt$ on all small balls around every $t \ne 0$: Weil's "local zeta function =
Mellin transform of the local density". *Proof:* `volume_congSet` and stabilization (`DVR.localDensity_eventually_eq`). -/
@[kb "weil1982" "§4.3, proof of Lemma 4.3.2, p. 89 (measure of {F(x) ≡ ρ mod p^ν})"]
theorem volume_ballQ_eq_localDensity (ν : Measure (v.adicCompletion F)) [SigmaFinite ν]
    [Measure.IsAddRightInvariant ν] (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (t : 𝔬) (ht : t ≠ 0) :
    ∀ᶠ k in atTop, (Measure.pi fun _ : Fin n => ν).real (congSet v Q (t : Fv) k) =
      DVR.localDensity Q πv t * ν.real (latticeV v k) * ν.real (latticeV v 0) ^ (n - 1) := by
  filter_upwards [DVR.localDensity_eventually_eq Q hQ πv (NF.irreducible_π v) t ht (two_ne_zero_O v)] with k hk
  have hq0 : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast q_pos v
  rw [← hk, Measure.real, volume_congSet, ENNReal.toReal_mul, ENNReal.toReal_pow, ← Measure.real,
    ENNReal.toReal_natCast, real_latticeV_eq]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, mul_pow, inv_pow, ← pow_mul, pow_succ,
    show k * (m + 1) = k * m + k by ring, pow_add]
  field_simp

/-! ### Standard and self-dual normalizations -/

/-- **Change of measure:** $Z_v^{\nu}(s) = \nu(\mathcal O_v)^n\,Z_v^{\mathrm{std}}(s)$, $Z^{\mathrm{std}}$ for `haarV` ($\operatorname{vol}(\mathcal O_v) = 1$). -/
theorem zetaInt_eq_mul_haar (ν : Measure (v.adicCompletion F)) [SigmaFinite ν] [Measure.IsAddRightInvariant ν]
    [IsFiniteMeasureOnCompacts ν] (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    zetaInt v ν Q s = ν.real (latticeV v 0) ^ n * zetaInt v (haarV v) Q s := by
  have h1 := hasSum_zetaInt v ν Q hQ hn hs
  have h2 := (hasSum_zetaInt v (haarV v) Q hQ hn hs).mul_left (ν.real (latticeV v 0) ^ n)
  refine h1.unique (h2.congr_fun fun j => ?_)
  rw [haarV_real_O, one_pow]; ring

/-- **The self-dual local zeta function** (measure `selfDualV`, self-dual for the standard character $\psi_v$):
$Z_v^{\mathrm{sd}}(s) = N(\mathfrak d_v)^{-n/2}\,Z_v^{\mathrm{std}}(s)$, $\mathfrak d_v = \mathfrak p_v^{d_v}$ the local different. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, vol(O_v) = N(d_v)^{-1/2} [unverified]"]
theorem zetaInt_selfDual (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    zetaInt v (selfDualV v) Q s =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2)) ^ n * zetaInt v (haarV v) Q s := by
  rw [zetaInt_eq_mul_haar v (selfDualV v) Q hQ hn hs, selfDualV_real_Ov]

/-- **Forms over $\mathcal O_F$:** for $Q$ over $\mathcal O_F$, the sequence $a_j$ of its completion $Q \otimes \mathcal O_v$ (`NF.Qp`) is
$r_{\mathfrak p^j}(0)/N(\mathfrak p)^{jn}$ with the global count `NF.repCount` mod $\mathfrak p^j$. -/
theorem aSeq_Qp (Q : QuadForm (𝓞 F) n) (j : ℕ) :
    aSeq v (NF.Qp v Q) j = (NF.repCount v Q j 0 : ℚ) / (Ideal.absNorm v.asIdeal : ℚ) ^ (j * n) := by
  rw [aSeq, NF.repCount_eq_completion, NF.q_completion, map_zero]

end QuadFormsKB.LocalZeta
