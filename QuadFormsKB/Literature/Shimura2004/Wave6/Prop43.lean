/-
# Shimura 2004, Proposition 4.3: the matrix description (4.10) of $P'_1$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, §4.2,
Proposition 4.3 and (4.10) (printed p. 30). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave4/MatrixModel.lean` and `Wave4/Lemma315.lean`: $F$ a field of characteristic
$\ne 2$ (`Invertible (2 : F)`), `Q : QuadraticForm F V` nondegenerate on a finite-dimensional $V$, a weak Witt
decomposition $V = U + Fe + Ff$ (`Q e = 0`, `Q f = 0`, `polar Q e f = 1`), $U$ = `uSpace Q e f`, $A(U)$ =
`AU Q e f`, and Shimura's $\Psi : A(V) \cong M_2(A(U))$ = `psi`. For $\alpha \in A(V)$ the entries of $\Psi(\alpha)$
are written $a, b, c, d$ (rows $(a, b)$, $(c, d)$; in Lean `ξ 0 0`, `ξ 0 1`, `ξ 1 0`, `ξ 1 1`), and Shimura writes
$c = c_\alpha$. $G'(V)$ = `homogeneousCliffordGroup Q`, $G^+(V)$ = `M0 Q`, and (4.9a) $P'_1 = \{a \in G'(V) \mid
a^{-1}ea \in Fe\}$ is `parabolicG' Q (F ∙ e)` (wave 2, `mem_parabolicG'_span_iff`). $\nu$ = `multiplier`, and
$\mu = \pm\nu$ of (3.21) is `muHom`.

**Proves** (all unconditional; standard axioms only): **Proposition 4.3**,
* $P'_1$ consists of the $a \in G'(V)$ with $c_a = 0$ (`mem_P1_iff`);
* (4.10): every $a \in P'_1$ has $\Psi(a) = \begin{pmatrix} rd & yd \\ 0 & d\end{pmatrix}$ with $d \in G'(U)$,
  $r \in F^\times$, $y \in U$ (`prop_4_3_shape`), and conversely every such matrix is $\Psi(a)$ for some
  $a \in P'_1$ (`prop_4_3_converse`);
* for such $a$: $a \in G^+(V)$ if and only if $d \in G^+(U)$ (`prop_4_3_M0_iff`), and $\nu(a) = \pm r\nu(d)$
  with $\nu(d) = dd^*$ (`prop_4_3_nu`).

The assertion $G^+(V) = P_1^+G^1(V)$ of the same proposition is the library's `prop_4_3_M0_eq_mul`. The explicit
matrix (4.10a) of $\tau(a)$ is not formalized here.

The proof follows Shimura's: $ea = r\,ae$ forces $c = 0$; conversely $c = 0$ makes $\Psi(a^{-1}ea)$ upper
triangular with zero diagonal, i.e. $a^{-1}ea \in Fe$. With $c = 0$, (3.9) gives $ad^* = d^*a = \mu(a)$, so $a$ and
$d$ are invertible, $d \in G'(U)$ by Lemma 3.15 (iii), $dd^* = d^*d \in F^\times$ by Lemma 3.15 (ii), hence
$a = rd$; and $bd^* \in U$ by Lemma 3.15 (i), hence $b \in Ud$. The converse writes the matrix as
$\Psi(\gamma)\Psi(\beta)$ with $\gamma = 1 + ye$ and $\beta = e(r, \pm 1)\,d$ (Lemmas 3.10, 3.11).
-/
import QuadFormsKB.Literature.Shimura2004.Wave4.Lemma315
import QuadFormsKB.Literature.Shimura2004.Wave2.Parabolic
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace Prop43

open MatrixModel

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {e f : V}

local notation "A" => CliffordAlgebra Q

section Hyp

variable (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1)
  (hQ : (QuadraticMap.associated Q).Nondegenerate)
include he hf hef

theorem e_ne_zero : e ≠ 0 := by
  rintro rfl
  simp at hef

/-! ### The first assertion: $P'_1 = \{a \in G'(V) \mid c_a = 0\}$ -/

include hQ in
/-- **Proposition 4.3** (Shimura 2004, p. 30), first assertion: $a \in G'(V)$ lies in $P'_1$ if and only if the
lower-left entry $c_a$ of $\Psi(a)$ vanishes. -/
@[kb "shimura2004" "Prop. 4.3, p. 30 (P'_1 consists of all a ∈ G'(V) such that c_a = 0)"]
theorem mem_P1_iff (α : homogeneousCliffordGroup Q) :
    (α : Aˣ) ∈ parabolicG' Q (F ∙ e) ↔ psi he hf hef ((α : Aˣ) : A) 1 0 = 0 := by
  rw [mem_parabolicG'_span_iff e (e_ne_zero he hf hef) (α : Aˣ) α.2]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : ι Q e * ((α : Aˣ) : A) = c • (((α : Aˣ) : A) * ι Q e) := by
      calc ι Q e * ((α : Aˣ) : A)
          = ((α : Aˣ) : A) * (((α : Aˣ)⁻¹ : Aˣ) * ι Q e * ((α : Aˣ) : A)) := by
            rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
        _ = c • (((α : Aˣ) : A) * ι Q e) := by rw [hc, map_smul, mul_smul_comm]
    have h2 := congrArg (fun x => psi he hf hef x 0 0) h1
    simpa [map_mul, psi_e, Matrix.mul_apply, Fin.sum_univ_two] using h2
  · intro hc
    obtain ⟨y, hy⟩ := (mem_cliffordGroup_iff (α : Aˣ)).1 α.2.1 e
    refine ⟨QuadraticMap.polar Q y f, ?_⟩
    have hinv := psi_inv_eq he hf hef hQ α
    have hpsi : psi he hf hef (ι Q y) = (((muHom hQ α : Fˣ) : F))⁻¹ •
        (adjU (psi he hf hef ((α : Aˣ) : A)) * !![0, 1; 0, 0] * psi he hf hef ((α : Aˣ) : A)) := by
      rw [hy, map_mul, map_mul, psi_e]
      change psi he hf hef (((α⁻¹ : homogeneousCliffordGroup Q) : Aˣ) : A) * _ * _ = _
      rw [hinv, Matrix.smul_mul, Matrix.smul_mul]
    rw [adjU_mul_e_mul, hc, psi_ι, psiVec_apply] at hpsi
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (AU Q e f) => M 0 0) hpsi
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (AU Q e f) => M 1 0) hpsi
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.smul_apply,
      mul_zero, neg_zero, smul_zero, reverse.map_zero, zero_mul] at h00 h10
    have hp : proj he hf hef y = 0 := by
      have := cliffordι_injective (QU Q e f) (h00.trans (map_zero _).symm)
      exact this
    have hpe : QuadraticMap.polar Q y e = 0 :=
      (algebraMap F (AU Q e f)).injective (h10.trans (map_zero _).symm)
    rw [← hy]
    congr 1
    conv_lhs => rw [decomp he hf hef y]
    rw [hp, hpe]
    simp

/-! ### (4.10): the shape of $\Psi(a)$ for $a \in P'_1$ -/

include hQ in
/-- With $c_a = 0$, (3.9) gives $ad^* = d^*a = \mu(a)$. -/
theorem ad_eq_mu (α : homogeneousCliffordGroup Q) (hc : psi he hf hef ((α : Aˣ) : A) 1 0 = 0) :
    psi he hf hef ((α : Aˣ) : A) 0 0 * reverse (psi he hf hef ((α : Aˣ) : A) 1 1) =
        algebraMap F (AU Q e f) ((muHom hQ α : Fˣ) : F) ∧
      reverse (psi he hf hef ((α : Aˣ) : A) 1 1) * psi he hf hef ((α : Aˣ) : A) 0 0 =
        algebraMap F (AU Q e f) ((muHom hQ α : Fˣ) : F) := by
  have h39 := formula_3_9 (⟨psiUnits he hf hef (α : Aˣ), psi_mem_matGroup he hf hef hQ α⟩ :
    matGroup (QU Q e f))
  rw [matMu_psi he hf hef hQ α] at h39
  obtain ⟨h1, h2, -⟩ := h39
  change psi he hf hef ((α : Aˣ) : A) 0 0 * reverse (psi he hf hef ((α : Aˣ) : A) 1 1) -
    psi he hf hef ((α : Aˣ) : A) 0 1 * reverse (psi he hf hef ((α : Aˣ) : A) 1 0) = _ at h1
  change reverse (psi he hf hef ((α : Aˣ) : A) 1 1) * psi he hf hef ((α : Aˣ) : A) 0 0 -
    reverse (psi he hf hef ((α : Aˣ) : A) 0 1) * psi he hf hef ((α : Aˣ) : A) 1 0 = _ at h2
  rw [hc, reverse.map_zero, mul_zero, sub_zero] at h1
  rw [hc, mul_zero, sub_zero] at h2
  exact ⟨h1, h2⟩

include hQ in
/-- With $c_a = 0$, the entry $d$ of $\Psi(a)$ is invertible. -/
theorem isUnit_d (α : homogeneousCliffordGroup Q) (hc : psi he hf hef ((α : Aˣ) : A) 1 0 = 0) :
    IsUnit (psi he hf hef ((α : Aˣ) : A) 1 1) := by
  obtain ⟨h1, h2⟩ := ad_eq_mu he hf hef hQ α hc
  set ξ := psi he hf hef ((α : Aˣ) : A)
  set m : F := ((muHom hQ α : Fˣ) : F)
  have hm : m ≠ 0 := Units.ne_zero _
  -- $d^*$ has the two-sided inverse $m^{-1}a$, so $d = (d^*)^*$ is a unit
  have hl : (m⁻¹ • ξ 0 0) * reverse (ξ 1 1) = 1 := by
    rw [smul_mul_assoc, h1, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hm, map_one]
  have hr : reverse (ξ 1 1) * (m⁻¹ • ξ 0 0) = 1 := by
    rw [mul_smul_comm, h2, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hm, map_one]
  refine ⟨⟨ξ 1 1, reverse (m⁻¹ • ξ 0 0), ?_, ?_⟩, rfl⟩
  · have := congrArg reverse hl
    rwa [reverse.map_mul, reverse_reverse, reverse.map_one] at this
  · have := congrArg reverse hr
    rwa [reverse.map_mul, reverse_reverse, reverse.map_one] at this

include hQ in
/-- **(4.10)**, p. 30 (Proposition 4.3): for $a \in P'_1$, $\Psi(a) = \begin{pmatrix} rd & yd \\ 0 & d
\end{pmatrix}$ with $d \in G'(U)$, $r \in F^\times$ and $y \in U$. -/
@[kb "shimura2004" "Prop. 4.3, (4.10), p. 30 (Ψ(a) = [[rd, yd], [0, d]] with d ∈ G'(U), r ∈ F^×, y ∈ U)"]
theorem prop_4_3_shape (α : homogeneousCliffordGroup Q) (hα : (α : Aˣ) ∈ parabolicG' Q (F ∙ e)) :
    ∃ (r : F) (hd : IsUnit (psi he hf hef ((α : Aˣ) : A) 1 1)) (y : uSpace Q e f),
      r ≠ 0 ∧ hd.unit ∈ homogeneousCliffordGroup (QU Q e f) ∧
      psi he hf hef ((α : Aˣ) : A) =
        !![r • psi he hf hef ((α : Aˣ) : A) 1 1, ι (QU Q e f) y * psi he hf hef ((α : Aˣ) : A) 1 1;
          0, psi he hf hef ((α : Aˣ) : A) 1 1] := by
  have hc := (mem_P1_iff he hf hef hQ α).1 hα
  have hd := isUnit_d he hf hef hQ α hc
  obtain ⟨h1, -⟩ := ad_eq_mu he hf hef hQ α hc
  set ξ := psi he hf hef ((α : Aˣ) : A) with hξ
  set m : F := ((muHom hQ α : Fˣ) : F)
  have hm : m ≠ 0 := Units.ne_zero _
  obtain ⟨hdd, ⟨s, hs⟩, -⟩ := lemma_3_15_ii he hf hef hQ α 1 1
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero] at hs
    have h0 : reverse (ξ 1 1) = 0 := hd.mul_right_eq_zero.1 hs
    have h1 : ξ 1 1 = 0 := by simpa using congrArg reverse h0
    exact hd.ne_zero h1
  obtain ⟨-, -, ⟨hdb, ⟨u, hu⟩, -, -⟩, -⟩ := lemma_3_15_i he hf hef hQ α
  refine ⟨m / s, hd, s⁻¹ • u, div_ne_zero hm hs0, lemma_3_15_iii he hf hef hQ α 1 1 hd, ?_⟩
  -- $a s = a d^* d = m d$ and $b s = b d^* d = (ys) d$
  have ha : ξ 0 0 = (m / s) • ξ 1 1 := by
    have : ξ 0 0 * algebraMap F _ s = algebraMap F _ m * ξ 1 1 := by
      rw [← hs, hdd, ← mul_assoc, h1]
    have h' := congrArg (fun x => s⁻¹ • x) this
    simp only [← Algebra.commutes s, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hs0, one_smul] at h'
    rw [h', div_eq_inv_mul]
  have hb : ξ 0 1 = ι (QU Q e f) (s⁻¹ • u) * ξ 1 1 := by
    have : ξ 0 1 * algebraMap F _ s = ι (QU Q e f) u * ξ 1 1 := by
      rw [← hs, hdd, ← mul_assoc, ← hdb, ← hu]
    have h' := congrArg (fun x => s⁻¹ • x) this
    simp only [← Algebra.commutes s, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hs0, one_smul] at h'
    rw [h', map_smul, smul_mul_assoc]
  conv_lhs => rw [ξ.eta_fin_two]
  rw [ha, hb, hc]

include hQ in
/-- **Proposition 4.3** (Shimura 2004, p. 30): for $a \in P'_1$ with $\Psi(a)$ as in (4.10), $a \in G^+(V)$ if and
only if $d \in G^+(U)$. -/
@[kb "shimura2004" "Prop. 4.3, p. 30 (a ∈ G⁺(V) if and only if d ∈ G⁺(U))"]
theorem prop_4_3_M0_iff (α : homogeneousCliffordGroup Q) (hα : (α : Aˣ) ∈ parabolicG' Q (F ∙ e))
    (hd : IsUnit (psi he hf hef ((α : Aˣ) : A) 1 1)) :
    (α : Aˣ) ∈ M0 Q ↔ hd.unit ∈ M0 (QU Q e f) := by
  have hdG := lemma_3_15_iii he hf hef hQ α 1 1 hd
  constructor
  · intro h
    exact ⟨((psi_mem_evenOdd_zero_iff he hf hef _).1 h.1).2.2.2, hdG.1⟩
  · intro h
    refine ⟨?_, α.2.1⟩
    rcases α.2.2 with h0 | h1
    · exact h0
    · exfalso
      have hodd := ((psi_mem_evenOdd_one_iff he hf hef _).1 h1).2.2.2
      have h0 : psi he hf hef ((α : Aˣ) : A) 1 1 = 0 :=
        (evenOdd_isCompl (QU Q e f)).disjoint.le_bot ⟨h.1, hodd⟩
      exact hd.ne_zero h0

include hQ in
/-- **Proposition 4.3** (Shimura 2004, p. 30): for $a \in P'_1$ with $\Psi(a)$ as in (4.10), $\mu(a) = r\,dd^*$,
hence $\nu(a) = \pm r\nu(d)$ (with $\nu(d) = dd^* \in F^\times$). -/
@[kb "shimura2004" "Prop. 4.3, p. 30 (ν(a) = ±rν(d))"]
theorem prop_4_3_nu (α : homogeneousCliffordGroup Q) (hα : (α : Aˣ) ∈ parabolicG' Q (F ∙ e)) {r s : F}
    (hr : psi he hf hef ((α : Aˣ) : A) 0 0 = r • psi he hf hef ((α : Aˣ) : A) 1 1)
    (hs : psi he hf hef ((α : Aˣ) : A) 1 1 * reverse (psi he hf hef ((α : Aˣ) : A) 1 1) =
      algebraMap F (AU Q e f) s) :
    ((muHom hQ α : Fˣ) : F) = r * s ∧
      (((multiplier hQ α : Fˣ) : F) = r * s ∨ ((multiplier hQ α : Fˣ) : F) = -(r * s)) := by
  have hc := (mem_P1_iff he hf hef hQ α).1 hα
  obtain ⟨h1, -⟩ := ad_eq_mu he hf hef hQ α hc
  rw [hr, smul_mul_assoc, hs, Algebra.smul_def, ← map_mul] at h1
  have hμ : ((muHom hQ α : Fˣ) : F) = r * s := ((algebraMap F (AU Q e f)).injective h1).symm
  refine ⟨hμ, ?_⟩
  rcases (mem_homogeneous_iff (α : Aˣ)).1 α.2 with h | h
  · left
    rw [← muHom_of_mem_M0 hQ α h]
    exact hμ
  · right
    rw [← hμ, muHom_of_mem_odd hQ α h, Units.val_neg, neg_neg]

/-! ### The converse part of (4.10) -/

omit he hf hef in
/-- The unit of $A(V)$ given by a unit $d$ of $A(U) \subseteq A(V)$. -/
def inclUnit (d : (AU Q e f)ˣ) : Aˣ := Units.map (incl Q e f).toMonoidHom d

omit he hf hef in
theorem coe_inclUnit (d : (AU Q e f)ˣ) : ((inclUnit d : Aˣ) : A) = incl Q e f (d : AU Q e f) := rfl

omit he hf hef in
theorem coe_inclUnit_inv (d : (AU Q e f)ˣ) :
    (((inclUnit d)⁻¹ : Aˣ) : A) = incl Q e f ((d⁻¹ : (AU Q e f)ˣ) : AU Q e f) := by
  rw [inclUnit, ← map_inv]; rfl

/-- For $d \in G(U)$ with $d' = \sigma d$: $dxd^{-1} \in V$ for every $x \in V$. -/
theorem incl_conj_mem {d : (AU Q e f)ˣ} (hd1 : d ∈ cliffordGroup (QU Q e f)) {σ : F}
    (hσ : involute (d : AU Q e f) = σ • (d : AU Q e f)) (x : V) :
    ∃ y : V, ι Q y = ((inclUnit d : Aˣ) : A) * ι Q x * (((inclUnit d)⁻¹ : Aˣ) : A) := by
  rw [coe_inclUnit, coe_inclUnit_inv]
  obtain ⟨u', hu'⟩ := hd1 (proj he hf hef x)
  have key : ∀ w : V, (∀ b, ι Q w * incl Q e f b = incl Q e f (involute b) * ι Q w) →
      incl Q e f (d : AU Q e f) * ι Q w * incl Q e f ((d⁻¹ : (AU Q e f)ˣ) : AU Q e f) = σ • ι Q w := by
    intro w hw
    have h1 := hw (involute (d : AU Q e f))
    rw [involute_involute] at h1
    rw [← h1, hσ, map_smul, mul_smul_comm, smul_mul_assoc, mul_assoc, ← map_mul, Units.mul_inv, map_one,
      mul_one]
  have hU : incl Q e f (d : AU Q e f) * ι Q (proj he hf hef x : V) *
      incl Q e f ((d⁻¹ : (AU Q e f)ˣ) : AU Q e f) = ι Q (u' : V) := by
    rw [← incl_ι, ← map_mul, ← map_mul, ← hu', incl_ι]
  refine ⟨(u' : V) + σ • (QuadraticMap.polar Q x f • e + QuadraticMap.polar Q x e • f), ?_⟩
  have hsplit : incl Q e f (d : AU Q e f) * ι Q x * incl Q e f ((d⁻¹ : (AU Q e f)ˣ) : AU Q e f) =
      incl Q e f (d : AU Q e f) * ι Q (proj he hf hef x : V) * incl Q e f ((d⁻¹ : (AU Q e f)ˣ) : AU Q e f) +
        QuadraticMap.polar Q x f • (incl Q e f (d : AU Q e f) * ι Q e *
          incl Q e f ((d⁻¹ : (AU Q e f)ˣ) : AU Q e f)) +
        QuadraticMap.polar Q x e • (incl Q e f (d : AU Q e f) * ι Q f *
          incl Q e f ((d⁻¹ : (AU Q e f)ˣ) : AU Q e f)) := by
    conv_lhs => rw [decomp he hf hef x]
    simp only [map_add, map_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [hsplit, hU, key e (ι_e_mul_incl), key f (ι_f_mul_incl)]
  simp only [map_add, map_smul]
  module

/-- $G'(U) \subseteq G'(V)$ (Shimura, §3.2 and (3.15)). -/
theorem inclUnit_mem_homogeneous {d : (AU Q e f)ˣ} (hd : d ∈ homogeneousCliffordGroup (QU Q e f)) :
    inclUnit d ∈ homogeneousCliffordGroup Q := by
  rcases hd.2 with h0 | h1
  · refine ⟨fun x => incl_conj_mem he hf hef hd.1 (σ := 1) (by rw [one_smul]; exact involute_eq_of_mem_even h0) x,
      Or.inl ?_⟩
    rw [coe_inclUnit, psi_mem_evenOdd_zero_iff he hf hef, psi_incl, involute_eq_of_mem_even h0]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    exact ⟨h0, zero_mem _, zero_mem _, h0⟩
  · refine ⟨fun x => incl_conj_mem he hf hef hd.1 (σ := -1)
      (by rw [neg_one_smul]; exact involute_eq_of_mem_odd h1) x, Or.inr ?_⟩
    rw [coe_inclUnit, psi_mem_evenOdd_one_iff he hf hef, psi_incl, involute_eq_of_mem_odd h1]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    exact ⟨h1, zero_mem _, zero_mem _, neg_mem h1⟩

/-- $\Psi(e(a, b)\,x) = \mathrm{diag}[ax, bx']$ for $x \in A(U)$ (Lemma 3.10 and (2.11)). -/
theorem psi_eab_mul_incl (a b : F) (x : AU Q e f) :
    psi he hf hef (eab Q e f a b * incl Q e f x) = !![a • x, 0; 0, b • involute x] := by
  rw [map_mul, psi_incl, eab, map_add, map_smul, map_smul, psi_ef, psi_fe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- $\Psi(1 + ye) = \begin{pmatrix} 1 & y \\ 0 & 1\end{pmatrix}$ for $y \in U$. -/
theorem psi_one_add_ye (y : uSpace Q e f) :
    psi he hf hef (rxy Q 1 (y : V) e) = !![1, ι (QU Q e f) y; 0, 1] := by
  rw [rxy, map_add, map_mul, AlgHom.commutes, map_one, psi_ι_of_mem, psi_e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The element $1 + ye$ ($y \in U$) lies in $G^+(V)$ (Lemma 3.11; $(1 + ye)(1 + ye)^* = 1$). -/
theorem exists_one_add_ye (y : uSpace Q e f) :
    ∃ g : Aˣ, (g : A) = rxy Q 1 (y : V) e ∧ g ∈ M0 Q :=
  rxy_mem_M0 1 (y : V) e (by rw [(mem_uSpace.1 y.2).1, he]; simp)

include hQ in
/-- **Proposition 4.3** (Shimura 2004, p. 30), converse part of (4.10): for every $d \in G'(U)$, $r \in F^\times$
and $y \in U$ there is $a \in P'_1$ with $\Psi(a) = \begin{pmatrix} rd & yd \\ 0 & d\end{pmatrix}$. -/
@[kb "shimura2004" "Prop. 4.3, (4.10), p. 30 (every [[rd, yd], [0, d]] with d ∈ G'(U), r ∈ F^×, y ∈ U is Ψ(a), a ∈ P'_1)"]
theorem prop_4_3_converse {d : (AU Q e f)ˣ} (hd : d ∈ homogeneousCliffordGroup (QU Q e f)) (r : Fˣ)
    (y : uSpace Q e f) :
    ∃ α : homogeneousCliffordGroup Q, (α : Aˣ) ∈ parabolicG' Q (F ∙ e) ∧
      psi he hf hef ((α : Aˣ) : A) = !![(r : F) • (d : AU Q e f), ι (QU Q e f) y * d; 0, d] := by
  obtain ⟨g, hg, hgM⟩ := exists_one_add_ye he hf hef y
  have hD := inclUnit_mem_homogeneous he hf hef hd
  -- $\sigma = \pm 1$ with $d' = \sigma d$
  obtain ⟨σ, hσ, hσ2⟩ : ∃ σ : Fˣ, involute (d : AU Q e f) = (σ : F) • (d : AU Q e f) ∧ (σ : F) * σ = 1 := by
    rcases hd.2 with h0 | h1
    · exact ⟨1, by rw [Units.val_one, one_smul]; exact involute_eq_of_mem_even h0, by simp⟩
    · exact ⟨-1, by rw [Units.val_neg, Units.val_one, neg_one_smul]; exact involute_eq_of_mem_odd h1, by simp⟩
  have hE := eabHom_mem_M0 he hf hef (r, σ)
  set α : homogeneousCliffordGroup Q :=
    ⟨g * eabHom he hf hef (r, σ) * inclUnit d,
      (homogeneousCliffordGroup Q).mul_mem ((homogeneousCliffordGroup Q).mul_mem (M0_le_homogeneous hgM)
        (M0_le_homogeneous hE)) hD⟩ with hα
  have hpsi : psi he hf hef ((α : Aˣ) : A) = !![(r : F) • (d : AU Q e f), ι (QU Q e f) y * d; 0, d] := by
    have : ((α : Aˣ) : A) = rxy Q 1 (y : V) e * (eab Q e f r σ * incl Q e f (d : AU Q e f)) := by
      rw [hα]
      simp only [Units.val_mul, coe_eabHom, coe_inclUnit, hg, mul_assoc]
    rw [this, map_mul, psi_one_add_ye, psi_eab_mul_incl, hσ, smul_smul, hσ2, one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨α, (mem_P1_iff he hf hef hQ α).2 ?_, hpsi⟩
  rw [hpsi]
  rfl

end Hyp

end Prop43

end QuadFormsKB.Shimura2004
