/-
# O'Meara §106: facts about unimodular $\mathbb Z$-lattices, even and odd lattices, $\mathcal G(L)$, adjacency

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^n$ with a form `Q : QuadForm ℚ n`; lattices are $\mathcal O_{\mathbb Q} = \mathbb Z$-submodules
of $\mathbb Q^n$ (`Submodule (𝓞 ℚ) (Fin n → ℚ)`, with `Submodule.IsLattice ℚ` when they are finitely generated and span
$V$; `Lat ℚ n` in the statements about $\mathcal G(L)$). O'Meara's bilinear form is $B = \tfrac12$ `bil Q`
($B(x, x) = Q(x)$); unimodular means `IsUnimodularZ Q L` ($L^\# = L$, `Sec106Defs.lean`); adjacency is the
$2$-neighbour relation `Nbr.IsNbrL Q 2 L K` (see `Sec106C.lean`). The scale, norm and volume are those of the abstract §82
layer (`OMeara.scale`, `OMeara.normIdeal`, `OMeara.volume`) for the Mathlib form `Q.toQuadraticForm`, with
$R = \mathcal O_{\mathbb Q}$ and $\mathfrak o = \mathbb Z$ the submodule `(1 : Submodule (𝓞 ℚ) ℚ)`.

**Defines** (technical) `locEval` (the value $Q(x)$ at a vector of the completion $\mathbb Q_v^n$, stated for a general
number field so that the library's $F$-algebra structure of $F_v$ is used, not `DivisionRing.toRatAlgebra`).

**Proves** (O'Meara 1973, §106, pp. 323–328; the ids `106.rN` number the items of the running text, `106:N` the numbered
propositions of the book)
* `omeara106_r4` (**106.r4**, p. 323): $V_\infty$ anisotropic iff definite;
* `omeara106_r11` (**106.r11**, p. 324): $\mathfrak sL = \mathbb Z$ and $2\mathbb Z \subseteq \mathfrak nL \subseteq \mathbb Z$ for a
  unimodular lattice;
* `omeara106_r14` (**106.r14**, p. 324): at an odd prime the norm of a unimodular lattice is the whole local ring;
* `omeara106_r15` (**106.r15**, p. 324): a unimodular lattice is even iff its localization at $2$ is even;
* `omeara106_r17` (**106.r17**, p. 325): $\sigma\mathcal G(L) = \mathcal G(\sigma L)$;
* `omeara106_r21` (**106.r21**, p. 326): $K$ adjacent to $L$ implies $K \in \mathcal G(L)$;
* `omeara106_r24` (**106.r24**, p. 326): only finitely many lattices are adjacent to a given one;
* `omeara106_r10` (**106.r10**, p. 324): a unimodular lattice on $I_n$ is completely decomposable iff it has matrix $I_n$;
* `omeara106_5` (**106:5**, p. 328): $K$ adjacent to $L$ iff $\mathfrak v(K + L) = \tfrac14\mathbb Z$ iff
  $\mathfrak v(K \cap L) = 4\mathbb Z$;
* `omeara106_r22` (**106.r22**, p. 326, reconstructed): a base of $V$ adapted to two adjacent lattices.

*Deviations and remarks.* (1) The book's $V$ is a regular space; for the statements with a lattice hypothesis this is
automatic (a lattice with $L^\# = L$ is regular, see `isUnimodular_of_isUnimodularZ`), and no regularity is assumed.
(2) The statements on a unimodular lattice need $n \ge 1$ (for $n = 0$ the scale is $0$) and that $L$ is a *lattice on
$V$* (finitely generated and spanning), as in the book. (3) `omeara106_5` is proved for every form $Q$, not only
$I_n$. (4) `omeara106_r21` does not need unimodularity of $L$. (5) The book's adjacency is defined by the invariant
factors $\tfrac12\mathbb Z, \mathbb Z, \dots, \mathbb Z, 2\mathbb Z$; for unimodular lattices it is the library's
$2$-neighbour relation (`Sec106C.lean`), and `omeara106_r22` recovers the invariant-factor description from it
(`omeara106_5` is the bridge between the two descriptions). (6) Helper lemmas are not tagged: the bridge from the
library's `omearaDual` to the abstract layer (`isUnimodular_of_isUnimodularZ`), the volume–index formula
(`volume_eq_index_sq_mul`) and the normal form of two lattices (`exists_adapted_basis_pid`).
-/
import QuadFormsKB.Literature.OMeara.Sec106C
import QuadFormsKB.Literature.OMeara.Sec106E
import QuadFormsKB.Literature.OMeara.Sec82Dual
import QuadFormsKB.Literature.OMeara.Sec81Index
import QuadFormsKB.HilbertModular.GenusTheta

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ} (Q : QuadForm ℚ n)

/-! ### Helpers -/

/-- O'Meara's bilinear form of the abstract §82 layer, for the form `Q.toQuadraticForm`, is $\tfrac12$ `bil Q`. -/
theorem omeara_bil_eq (x y : Fin n → ℚ) :
    OMeara.bil Q.toQuadraticForm x y = bil Q x y / 2 := by
  have h1 := QuadForm.polar_eq_hessian ℚ Q x y
  have e : Q.hessian.map (algebraMap ℚ ℚ) = Q.hessian := by ext; simp
  rw [e] at h1
  rw [OMeara.bil, QuadraticMap.associated_apply, QuadForm.toQuadraticForm_apply,
    QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply]
  show ⅟(2:ℚ) * (Q.evalIn ℚ (x + y) - Q.evalIn ℚ x - Q.evalIn ℚ y) = _
  rw [h1]
  simp [bil, div_eq_inv_mul]

/-- The value of the abstract form `Q.toQuadraticForm` is `Q.eval`. -/
theorem omeara_Q_eq (x : Fin n → ℚ) : Q.toQuadraticForm x = Q.eval x :=
  QuadForm.toQuadraticForm_apply Q x

/-- **106.r4: a space over $\mathbb Q$ is definite at infinity iff it is anisotropic over $\mathbb R$** (O'Meara 1973,
§106, p. 323). For a quadratic form `Q : QuadForm ℚ n`, the real space $V_\infty = \mathbb R^n$ is anisotropic
(`¬ Q.IsotropicIn ℝ`: $Q(x) \ne 0$ for all $x \ne 0$) if and only if it is positive definite
($Q(x) > 0$ for all $x \ne 0$) or negative definite ($Q(x) < 0$ for all $x \ne 0$). O'Meara: the set $S$ of all discrete
spots is definite for $V$ iff $V_\infty$ is positive or negative definite; this is the equivalence of the
anisotropy of $V_\infty$ with definiteness (a form taking both signs has a nontrivial real zero). -/
@[kb "omeara1963" "§106, p. 323 (S definite for V iff V_∞ is positive or negative definite)"]
theorem omeara106_r4 :
    ¬ Q.IsotropicIn ℝ ↔ ((∀ x : Fin n → ℝ, x ≠ 0 → 0 < Q.evalIn ℝ x) ∨
      (∀ x : Fin n → ℝ, x ≠ 0 → Q.evalIn ℝ x < 0)) := by
  constructor
  · intro hni
    have hne : ∀ x : Fin n → ℝ, x ≠ 0 → Q.evalIn ℝ x ≠ 0 := fun x hx h => hni ⟨x, hx, h⟩
    by_cases hpos : ∃ x : Fin n → ℝ, x ≠ 0 ∧ 0 < Q.evalIn ℝ x
    · left
      obtain ⟨x, hx, hxp⟩ := hpos
      intro y hy
      by_contra hle
      have hneg : Q.evalIn ℝ y < 0 := lt_of_le_of_ne (not_lt.mp hle) (hne y hy)
      set B : ℝ := x ⬝ᵥ (Q.hessian.map (algebraMap ℚ ℝ) *ᵥ y) with hB
      have hq : ∀ t : ℝ, Q.evalIn ℝ (x + t • y) =
          Q.evalIn ℝ y * t * t + B * t + Q.evalIn ℝ x := by
        intro t
        have h1 := QuadForm.polar_eq_hessian ℝ Q x (t • y)
        rw [Matrix.mulVec_smul, dotProduct_smul, QuadForm.evalIn_smul] at h1
        simp only [smul_eq_mul] at h1
        rw [← hB] at h1
        nlinarith [h1]
      have hdisc : discrim (Q.evalIn ℝ y) B (Q.evalIn ℝ x) =
          Real.sqrt (discrim (Q.evalIn ℝ y) B (Q.evalIn ℝ x)) *
          Real.sqrt (discrim (Q.evalIn ℝ y) B (Q.evalIn ℝ x)) := by
        rw [Real.mul_self_sqrt]
        unfold discrim
        nlinarith [sq_nonneg B, mul_pos_of_neg_of_neg hneg (neg_neg_of_pos hxp)]
      obtain ⟨t, ht⟩ := exists_quadratic_eq_zero hneg.ne ⟨_, hdisc⟩
      have hz : Q.evalIn ℝ (x + t • y) = 0 := by rw [hq]; linarith
      have hne0 : x + t • y ≠ 0 := by
        intro h0
        have hx' : x = (-t) • y := by
          have : x = x + t • y - t • y := by abel
          rw [this, h0]; simp
        have := QuadForm.evalIn_smul ℝ Q (-t) y
        rw [← hx'] at this
        nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) (neg_nonneg.mpr hneg.le)]
      exact hni ⟨_, hne0, hz⟩
    · right
      simp only [not_exists, not_and, not_lt] at hpos
      intro x hx
      exact lt_of_le_of_ne (hpos x hx) (hne x hx)
  · rintro (h | h) ⟨x, hx, h0⟩
    · exact (h x hx).ne' h0
    · exact (h x hx).ne h0

/-! ### Bridge to the abstract §82 layer -/

/-- Membership in $\mathfrak o = \mathbb Z$ (the submodule `1` of $\mathbb Q$). -/
theorem mem_one_iff_int (r : ℚ) : r ∈ (1 : Submodule (𝓞 ℚ) ℚ) ↔ ∃ m : ℤ, r = m := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Rat.ringOfIntegersEquiv a, (Rat.ringOfIntegersEquiv_apply_coe a).symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨Rat.ringOfIntegersEquiv.symm m, by
      rw [← Rat.ringOfIntegersEquiv_apply_coe]; simp⟩

theorem exists_int_smul_eq (c : 𝓞 ℚ) (y : Fin n → ℚ) : ∃ k : ℤ, c • y = (k : ℚ) • y := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ((k : ℤ) : 𝓞 ℚ) = c :=
    ⟨Rat.ringOfIntegersEquiv c, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
      (Rat.ringOfIntegersEquiv.symm_apply_apply c)⟩
  subst hk
  exact ⟨k, by rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]⟩

theorem intCast_smul_mem {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} {x : Fin n → ℚ} (hx : x ∈ M) (k : ℤ) :
    (k : ℚ) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx k

theorem bil_smul_left' (c : ℚ) (x y : Fin n → ℚ) : bil Q (c • x) y = c * bil Q x y := by
  simp [bil, smul_dotProduct]

theorem bil_smul_right' (c : ℚ) (x y : Fin n → ℚ) : bil Q x (c • y) = c * bil Q x y := by
  simp [bil, Matrix.mulVec_smul, dotProduct_smul]

theorem bil_add_left' (x x' y : Fin n → ℚ) : bil Q (x + x') y = bil Q x y + bil Q x' y := by
  simp [bil, add_dotProduct]

theorem bil_add_right' (x y y' : Fin n → ℚ) : bil Q x (y + y') = bil Q x y + bil Q x y' := by
  simp [bil, Matrix.mulVec_add, dotProduct_add]

theorem bil_sub_left' (x x' y : Fin n → ℚ) : bil Q (x - x') y = bil Q x y - bil Q x' y := by
  simp [bil, sub_dotProduct]

theorem bil_self_eq (x : Fin n → ℚ) : bil Q x x = 2 * Q.eval x := by
  have h := two_mul_evalIn Q (R := ℚ) x
  have e : Q.hessian.map (algebraMap ℚ ℚ) = Q.hessian := by ext; simp
  rw [e] at h
  rw [bil, ← h]

/-- For $x, y$ in a unimodular lattice, $B(x, y) \in \mathbb Z$. -/
theorem uni_mem' {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : IsUnimodularZ Q L) {x y : Fin n → ℚ}
    (hx : x ∈ L) (hy : y ∈ L) : ∃ m : ℤ, bil Q x y / 2 = m := by
  have : x ∈ omearaDual Q L := by rw [hL]; exact hx
  exact this y hy

/-- $Q(x) \in \mathbb Z$ on a unimodular lattice. -/
theorem uni_Q_int {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : IsUnimodularZ Q L) {x : Fin n → ℚ}
    (hx : x ∈ L) : ∃ m : ℤ, Q.eval x = m := by
  obtain ⟨m, hm⟩ := uni_mem' Q hL hx hx
  exact ⟨m, by rw [bil_self_eq] at hm; linarith⟩

/-- A vector divisible by every positive integer inside a lattice is zero. -/
theorem eq_zero_of_div_mem {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) {x : Fin n → ℚ}
    (hx : ∀ m : ℕ, (((m : ℚ) + 1)⁻¹) • x ∈ L) : x = 0 := by
  obtain ⟨d, hd0, -, hd⟩ := exists_global_bounds hL
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨dz, hdz⟩ : ∃ dz : ℤ, (dz : ℚ) = algebraMap (𝓞 ℚ) ℚ d :=
    ⟨Rat.ringOfIntegersEquiv d, Rat.ringOfIntegersEquiv_apply_coe d⟩
  have hdz0 : (dz : ℚ) ≠ 0 := by
    rw [hdz]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).mpr hd0
  set c : ℚ := dz * x i with hc
  have hc0 : c ≠ 0 := mul_ne_zero hdz0 hi
  obtain ⟨m, hm⟩ := exists_nat_gt |c|
  obtain ⟨a, ha⟩ := hd _ (hx m) i
  rw [smul_apply_int, Pi.smul_apply, smul_eq_mul, ← hdz] at ha
  have hz : ((Rat.ringOfIntegersEquiv a : ℤ) : ℚ) * ((m : ℚ) + 1) = c := by
    rw [Rat.ringOfIntegersEquiv_apply_coe, ha, hc]
    field_simp
  have hz0 : Rat.ringOfIntegersEquiv a ≠ 0 := by
    intro h0
    rw [h0] at hz
    simp at hz
    exact hc0 hz.symm
  have h1 : (1 : ℚ) ≤ |((Rat.ringOfIntegersEquiv a : ℤ) : ℚ)| := by
    have : (1 : ℤ) ≤ |Rat.ringOfIntegersEquiv a| := Int.one_le_abs hz0
    exact_mod_cast this
  have h2 : |c| = |((Rat.ringOfIntegersEquiv a : ℤ) : ℚ)| * ((m : ℚ) + 1) := by
    rw [← hz, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < (m : ℚ) + 1)]
  nlinarith [h1, h2, hm, (by positivity : (0 : ℚ) ≤ m)]

/-- **The dual of §82F is $L^\#$ of §106** (for a lattice on $V$): $\{x \in FL : B(x, L) \subseteq \mathfrak o\}$
equals `omearaDual Q L`. -/
theorem dual_eq_omearaDual {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) :
    OMeara.dual Q.toQuadraticForm L = omearaDual Q L := by
  ext x
  rw [OMeara.mem_dual]
  constructor
  · rintro ⟨-, h⟩ y hy
    obtain ⟨m, hm⟩ := (mem_one_iff_int _).mp (h y hy)
    exact ⟨m, by rw [← omeara_bil_eq]; exact hm⟩
  · intro h
    refine ⟨by rw [hL.span_eq_top]; trivial, fun y hy => ?_⟩
    obtain ⟨m, hm⟩ := h y hy
    exact (mem_one_iff_int _).mpr ⟨m, by rw [omeara_bil_eq]; exact hm⟩

/-- A lattice on $V$ is nonzero when $n \ge 1$. -/
theorem lattice_ne_bot {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) (hn : 0 < n) : L ≠ ⊥ := by
  intro h
  have h1 := hL.span_eq_top
  rw [h] at h1
  have h2 : (Pi.single ⟨0, hn⟩ (1 : ℚ) : Fin n → ℚ) ∈ (⊤ : Submodule ℚ (Fin n → ℚ)) := trivial
  rw [← h1] at h2
  simp at h2

/-- **A unimodular lattice on $V$ (in the sense $L^\# = L$) is unimodular in the abstract sense of §82G**
(`OMeara.IsUnimodular`, i.e. $\mathfrak o$-modular: $\mathfrak sL = \mathfrak o$, $\mathfrak vL = \mathfrak o^r$), for
$n \ge 1$. -/
theorem isUnimodular_of_isUnimodularZ {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) (hn : 0 < n)
    (hu : IsUnimodularZ Q L) : OMeara.IsUnimodular Q.toQuadraticForm L := by
  have hreg : OMeara.IsRegular Q.toQuadraticForm L := by
    intro x hx hx0
    refine eq_zero_of_div_mem hL fun m => ?_
    have : (((m : ℚ) + 1)⁻¹) • x ∈ omearaDual Q L := by
      intro y hy
      refine ⟨0, ?_⟩
      have h0 := hx0 y hy
      rw [omeara_bil_eq] at h0
      rw [bil_smul_left']
      have : bil Q x y = 0 := by linarith
      rw [this]; simp
    rw [hu] at this
    exact this
  rw [OMeara.isUnimodular_iff_dual_eq _ hL.fg (lattice_ne_bot hL hn) hreg, dual_eq_omearaDual Q hL]
  exact hu

/-! ### 106.r11 and 106.r14: scale and norm of a unimodular lattice -/

/-- **106.r11: scale and norm of a unimodular lattice** (O'Meara 1973, §106A, p. 324). Let $L$ be a unimodular
lattice on $V = \mathbb Q^n$ (a lattice, that is, finitely generated and spanning, with $L^\# = L$; $n \ge 1$).
Then $\mathfrak sL = \mathbb Z$ and $2\mathbb Z \subseteq \mathfrak nL \subseteq \mathbb Z$, hence $\mathfrak nL = \mathbb Z$
or $\mathfrak nL = 2\mathbb Z$. Here $\mathfrak s$ and $\mathfrak n$ are `OMeara.scale` and `OMeara.normIdeal` of the
abstract §82 layer over $R = \mathcal O_{\mathbb Q} = \mathbb Z$, for the form `Q.toQuadraticForm`, and
$\mathbb Z = \mathfrak o$ is `(1 : Submodule (𝓞 ℚ) ℚ)`, $2\mathbb Z$ is `Submodule.span (𝓞 ℚ) {2}`.
(O'Meara's $V$ is regular; this is automatic for a lattice with $L^\# = L$. $n \ge 1$ is needed: for $n = 0$ the
scale is $0$.) -/
@[kb "omeara1963" "§106A, p. 324 (sL = Z and 2Z ⊆ nL ⊆ Z for a unimodular lattice)"]
theorem omeara106_r11 {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) (hn : 0 < n)
    (hu : IsUnimodularZ Q L) :
    OMeara.scale Q.toQuadraticForm L = 1 ∧
    Submodule.span (𝓞 ℚ) {(2 : ℚ)} ≤ OMeara.normIdeal Q.toQuadraticForm L ∧
    OMeara.normIdeal Q.toQuadraticForm L ≤ 1 ∧
    (OMeara.normIdeal Q.toQuadraticForm L = 1 ∨
      OMeara.normIdeal Q.toQuadraticForm L = Submodule.span (𝓞 ℚ) {(2 : ℚ)}) := by
  have hm := isUnimodular_of_isUnimodularZ Q hL hn hu
  have hs : OMeara.scale Q.toQuadraticForm L = 1 := hm.2.1
  have hle : OMeara.normIdeal Q.toQuadraticForm L ≤ 1 := hs ▸ OMeara.normIdeal_le_scale _ L
  have h2mem : (2 : ℚ) ∈ OMeara.normIdeal Q.toQuadraticForm L := by
    have := OMeara.two_mul_mem_normIdeal Q.toQuadraticForm (L := L) (c := 1)
      (by rw [hs]; exact Submodule.one_le.mp le_rfl)
    simpa using this
  have hge : Submodule.span (𝓞 ℚ) {(2 : ℚ)} ≤ OMeara.normIdeal Q.toQuadraticForm L := by
    rw [Submodule.span_le]
    simpa using h2mem
  refine ⟨hs, hge, hle, ?_⟩
  by_cases h1 : (1 : ℚ) ∈ OMeara.normIdeal Q.toQuadraticForm L
  · left
    exact le_antisymm hle (Submodule.one_le.mpr h1)
  · right
    refine le_antisymm ?_ hge
    intro x hx
    obtain ⟨m, rfl⟩ := (mem_one_iff_int x).mp (hle hx)
    rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rw [Submodule.mem_span_singleton]
      refine ⟨Rat.ringOfIntegersEquiv.symm k, ?_⟩
      rw [Algebra.smul_def]
      have : algebraMap (𝓞 ℚ) ℚ (Rat.ringOfIntegersEquiv.symm k) = (k : ℚ) := by
        rw [← Rat.ringOfIntegersEquiv_apply_coe]; simp
      rw [this]; push_cast; ring
    · exfalso
      apply h1
      have e : (1 : ℚ) = (((2 * k + 1 : ℤ)) : ℚ) - ((k : ℤ) • (2 : ℚ)) := by
        rw [zsmul_eq_mul]; push_cast; ring
      rw [e]
      exact sub_mem hx (zsmul_mem h2mem k)

/-- **106.r14: no even/odd distinction at an odd prime** (O'Meara 1973, §106A, p. 324). Let $L$ be a unimodular
lattice on $V = \mathbb Q^n$ ($n \ge 1$) and $v$ an odd finite spot of $\mathbb Q$ (`(2 : 𝓞 ℚ) ∉ v.asIdeal`). Then
$\mathfrak nL_v = \mathbb Z_v$: some $x \in L$ has $Q(x)$ a unit at $v$, that is, $v$-adic absolute value
`v.valuation ℚ (Q x) = 1` (equivalently $Q(x) \in \mathbb Z$ is not divisible by the prime $p$ of $v$). -/
@[kb "omeara1963" "§106A, p. 324 (over Z_p, p odd, no distinction between odd and even)"]
theorem omeara106_r14 {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) (hn : 0 < n)
    (hu : IsUnimodularZ Q L) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ x ∈ L, v.valuation ℚ (Q.eval x) = 1 := by
  by_contra hcon
  push Not at hcon
  -- the integers divisible by `v`, as a submodule of `ℚ`
  set P : Submodule (𝓞 ℚ) ℚ := Submodule.map (Algebra.linearMap (𝓞 ℚ) ℚ) v.asIdeal with hP
  have hPmem : ∀ a : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ a ∈ P ↔ a ∈ v.asIdeal := by
    intro a
    rw [hP, Submodule.mem_map]
    constructor
    · rintro ⟨b, hb, hba⟩
      have : b = a := IsFractionRing.injective (𝓞 ℚ) ℚ hba
      rw [← this]; exact hb
    · intro ha; exact ⟨a, ha, rfl⟩
  have hQP : ∀ x ∈ L, Q.eval x ∈ P := by
    intro x hx
    obtain ⟨m, hm⟩ := uni_Q_int Q hu hx
    have hm' : Q.eval x = algebraMap (𝓞 ℚ) ℚ (Rat.ringOfIntegersEquiv.symm m) := by
      rw [hm, ← Rat.ringOfIntegersEquiv_apply_coe]; simp
    rw [hm', hPmem]
    have h1 := hcon x hx
    rw [hm'] at h1
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mp
      (lt_of_le_of_ne (v.valuation_le_one _) h1)
  have hsc : OMeara.scale Q.toQuadraticForm L ≤ P := by
    rw [OMeara.scale, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨m, hm⟩ := uni_mem' Q hu hx hy
    have hb : OMeara.bil Q.toQuadraticForm x y = algebraMap (𝓞 ℚ) ℚ (Rat.ringOfIntegersEquiv.symm m) := by
      rw [omeara_bil_eq, hm, ← Rat.ringOfIntegersEquiv_apply_coe]; simp
    have h2 : (2 : ℚ) * OMeara.bil Q.toQuadraticForm x y =
        Q.eval (x + y) - Q.eval x - Q.eval y := by
      have := OMeara.Q_add Q.toQuadraticForm x y
      rw [omeara_Q_eq, omeara_Q_eq, omeara_Q_eq] at this
      linarith
    have h3 : algebraMap (𝓞 ℚ) ℚ (2 * Rat.ringOfIntegersEquiv.symm m) ∈ P := by
      rw [map_mul, map_ofNat, ← hb, h2]
      exact sub_mem (sub_mem (hQP _ (L.add_mem hx hy)) (hQP _ hx)) (hQP _ hy)
    rw [hPmem] at h3
    have h4 : Rat.ringOfIntegersEquiv.symm m ∈ v.asIdeal :=
      ((v.isPrime.mem_or_mem h3).resolve_left hv)
    rw [hb]
    exact (hPmem _).mpr h4
  have h1P : (1 : ℚ) ∈ P := by
    have h1s : (1 : ℚ) ∈ OMeara.scale Q.toQuadraticForm L := by
      rw [(isUnimodular_of_isUnimodularZ Q hL hn hu).2.1]
      exact Submodule.one_le.mp le_rfl
    exact hsc h1s
  have : algebraMap (𝓞 ℚ) ℚ 1 ∈ P := by rwa [map_one]
  rw [hPmem] at this
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

/-! ### 106.r15: even iff even at $2$ -/

/-- **The value $Q(x)$ at a vector $x \in F_v^n$ of the completion** at a finite spot $v$ of a number field $F$
(`QuadForm.evalIn` over $F_v$, with the library's $F$-algebra structure of $F_v$). Stated for a general number field
only so that the algebra structure on $F_v$ is the one used by `loc` and `locVec` (for $F = \mathbb Q$ Lean would
otherwise pick the unrelated structure `DivisionRing.toRatAlgebra`). -/
abbrev locEval {F : Type*} [Field F] [NumberField F] (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))
    (x : Fin n → v.adicCompletion F) : v.adicCompletion F :=
  Q.evalIn (v.adicCompletion F) x

/-- The library's $F$-algebra structure on $F_v$ (used to override `DivisionRing.toRatAlgebra` for $F = \mathbb Q$). -/
@[reducible] def algAdic (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra F (v.adicCompletion F) := inferInstance

/-- For $F = \mathbb Q$ use the library's algebra structure on $\mathbb Q_v$ (file-local). -/
local instance (priority := high) algAdicQ (w : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (w.adicCompletion ℚ) := algAdic ℚ w

section DyadicEven

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem bilR_add_left' (x x' y : Fin n → Fv) :
    bilR Q Fv (x + x') y = bilR Q Fv x y + bilR Q Fv x' y := by
  simp [bilR, add_dotProduct]

theorem bilR_add_right' (x y y' : Fin n → Fv) :
    bilR Q Fv x (y + y') = bilR Q Fv x y + bilR Q Fv x y' := by
  simp [bilR, Matrix.mulVec_add, dotProduct_add]

theorem bilR_smul_left' (c : 𝔬) (x y : Fin n → Fv) :
    bilR Q Fv (c • x) y = (c : Fv) * bilR Q Fv x y := by
  have e : c • x = (c : Fv) • x := rfl
  rw [e]
  simp [bilR, smul_dotProduct]

theorem bilR_smul_right' (c : 𝔬) (x y : Fin n → Fv) :
    bilR Q Fv x (c • y) = (c : Fv) * bilR Q Fv x y := by
  have e : c • y = (c : Fv) • y := rfl
  rw [e]
  simp [bilR, Matrix.mulVec_smul, dotProduct_smul]

/-- The polar form of two vectors of the localization of a unimodular lattice lies in $2\mathfrak o_v$. -/
theorem local_bil_mem {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hu : IsUnimodularZ Q L) {x z : Fin n → Fv}
    (hx : x ∈ loc v L) (hz : z ∈ loc v L) : bilR Q Fv x z ∈ Submodule.span 𝔬 {(2 : Fv)} := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, rfl⟩ := hz
      rw [bilR_locVec]
      obtain ⟨m, hm⟩ := uni_mem' Q hu ha hb
      have e : bil Q a b = 2 * m := by linarith
      rw [e, map_mul, map_ofNat, Submodule.mem_span_singleton]
      refine ⟨(m : 𝔬), ?_⟩
      show ((m : 𝔬) : Fv) * 2 = _
      simp [mul_comm]
    | zero => simp [bilR]
    | add z z' _ _ h h' => rw [bilR_add_right']; exact add_mem h h'
    | smul c z _ h =>
      rw [bilR_smul_right']
      exact Submodule.smul_mem _ c h
  | zero => simp [bilR]
  | add x x' _ _ h h' => rw [bilR_add_left']; exact add_mem h h'
  | smul c x _ h =>
    rw [bilR_smul_left']
    exact Submodule.smul_mem _ c h

/-- **106.r15: a unimodular lattice is even iff its localization at $2$ is even** (O'Meara 1973, §106A,
p. 324). Let $L$ be a unimodular lattice on $V = \mathbb Q^n$ ($L^\# = L$) and $v$ the dyadic spot of $\mathbb Q$
(`(2 : 𝓞 ℚ) ∈ v.asIdeal`, i.e. $v$ is the spot of the prime $2$). Then $L$ is even (`IsEvenLat Q L`:
$Q(L) \subseteq 2\mathbb Z$) if and only if $L_2$ is even, that is, $Q(x) \in 2\mathbb Z_2$ for every
$x \in L_2$ (`loc v L`, the $\mathbb Z_2$-span of $L$ in $\mathbb Q_2^n$; $\mathbb Z_2$ is
`v.adicCompletionIntegers ℚ`). -/
@[kb "omeara1963" "§106A, p. 324 (L even iff the localization L_2 is even)"]
theorem omeara106_r15 {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hu : IsUnimodularZ Q L)
    (hv : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    IsEvenLat Q L ↔ ∀ x ∈ loc v L, ∃ c : v.adicCompletionIntegers ℚ,
      locEval Q v x = 2 * (c : v.adicCompletion ℚ) := by
  constructor
  · intro he x hx
    have hmem : Q.evalIn Fv x ∈ Submodule.span 𝔬 {(2 : Fv)} := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        rw [evalIn_locVec Q v, Submodule.mem_span_singleton]
        obtain ⟨m, hm⟩ := he a ha
        refine ⟨(m : 𝔬), ?_⟩
        show ((m : 𝔬) : Fv) * 2 = _
        rw [hm, map_mul, map_ofNat]
        simp [mul_comm]
      | zero =>
        have h := two_mul_evalIn Q (R := Fv) (0 : Fin n → Fv)
        have h0 : Q.evalIn Fv 0 = 0 := by simpa using h
        rw [h0]; exact zero_mem _
      | add x x' hx hx' h h' =>
        have e := QuadForm.polar_eq_hessian Fv Q x x'
        have e2 : Q.evalIn Fv (x + x') = Q.evalIn Fv x + Q.evalIn Fv x' + bilR Q Fv x x' := by
          have : bilR Q Fv x x' = x ⬝ᵥ (Q.hessian.map (algebraMap ℚ Fv) *ᵥ x') := rfl
          rw [this, ← e]; ring
        rw [e2]
        exact add_mem (add_mem h h') (local_bil_mem Q v hu hx hx')
      | smul c x hx h =>
        have e : c • x = (c : Fv) • x := rfl
        rw [e, QuadForm.evalIn_smul]
        have := Submodule.smul_mem (Submodule.span 𝔬 {(2 : Fv)}) (c ^ 2) h
        have e3 : (c ^ 2) • Q.evalIn Fv x = (c : Fv) ^ 2 * Q.evalIn Fv x := rfl
        rwa [e3] at this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨c, ?_⟩
    have h' : Q.evalIn Fv x = 2 * (c : Fv) := by
      rw [← hc]
      show ((c : Fv)) * 2 = 2 * (c : Fv)
      ring
    exact h'
  · intro h x hx
    obtain ⟨m, hm⟩ := uni_Q_int Q hu hx
    obtain ⟨c, hc⟩ := h _ (locVec_mem_loc v hx)
    rw [locEval, evalIn_locVec Q v, hm] at hc
    -- `m` is divisible by the prime `v`
    set a : 𝓞 ℚ := Rat.ringOfIntegersEquiv.symm m with ha
    have hacoe : algebraMap (𝓞 ℚ) Fv a = algebraMap ℚ Fv (m : ℚ) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 ℚ) ℚ Fv, ← Rat.ringOfIntegersEquiv_apply_coe, ha]
      simp
    have hlt : Valued.v (algebraMap (𝓞 ℚ) Fv a) < 1 := by
      rw [hacoe, hc]
      have h2 : Valued.v (algebraMap (𝓞 ℚ) Fv 2) < 1 := by
        rw [valued_algebraMap_int]
        exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v 2).mpr hv
      rw [map_mul]
      have hc1 : Valued.v (c : Fv) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2
      calc Valued.v (2 : Fv) * Valued.v (c : Fv) ≤ Valued.v (2 : Fv) * 1 := mul_le_mul_right hc1 _
        _ = Valued.v (algebraMap (𝓞 ℚ) Fv 2) := by
          rw [mul_one, map_ofNat (algebraMap (𝓞 ℚ) Fv) 2]
        _ < 1 := h2
    rw [valued_algebraMap_int] at hlt
    have hav : a ∈ v.asIdeal := (HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mp hlt
    rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩
    · exact ⟨k, by rw [hm]; push_cast; ring⟩
    · exfalso
      have e : (1 : 𝓞 ℚ) = a - (Rat.ringOfIntegersEquiv.symm k) * 2 := by
        rw [ha]; simp; ring
      have : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
        rw [e]; exact v.asIdeal.sub_mem hav (v.asIdeal.mul_mem_left _ hv)
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

end DyadicEven

/-! ### 106.r17 and 106.r21: the set $\mathcal G(L)$ -/

/-- The dual of the image of a lattice under an isometry is the image of the dual. -/
theorem omearaDual_glImage {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup Q ℚ)
    (K : Submodule (𝓞 ℚ) (Fin n → ℚ)) :
    omearaDual Q (glImage γ K) = glImage γ (omearaDual Q K) := by
  ext x
  constructor
  · intro hx
    refine ⟨γ⁻¹.val *ᵥ x, ?_, mulVec_inv_mulVec γ x⟩
    intro y hy
    obtain ⟨m, hm⟩ := hx (γ.val *ᵥ y) (mulVec_mem_glImage hy)
    refine ⟨m, ?_⟩
    have := bil_isometry Q hγ (γ⁻¹.val *ᵥ x) y
    rw [mulVec_inv_mulVec] at this
    rw [← this]
    exact hm
  · rintro ⟨x', hx', rfl⟩ y hy
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨m, hm⟩ := hx' y' hy'
    refine ⟨m, ?_⟩
    show bil Q (γ.val *ᵥ x') (γ.val *ᵥ y') / 2 = m
    rw [bil_isometry Q hγ]
    exact hm

/-- An isometry carries $\mathcal G(L)$ into $\mathcal G(\gamma L)$. -/
theorem image_mem_omearaG {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup Q ℚ) {K L : Lat ℚ n}
    (h : K ∈ omearaG Q L) : Lat.image γ K ∈ omearaG Q (Lat.image γ L) := by
  refine ⟨?_, fun v hv => ?_⟩
  · show omearaDual Q (glImage γ K.1) = glImage γ K.1
    rw [omearaDual_glImage Q hγ, show omearaDual Q K.1 = K.1 from h.1]
  · show loc v (glImage γ K.1) = loc v (glImage γ L.1)
    rw [loc_glImage, loc_glImage, h.2 v hv]

/-- **106.r17: $\sigma\mathcal G(L) = \mathcal G(\sigma L)$** (O'Meara 1973, §106B, p. 325). For a lattice $L$ on
$V = \mathbb Q^n$ and an isometry $\sigma \in O(V)$ (`γ ∈ orthGroup Q ℚ`, the full orthogonal group $O_n(V)$ of
O'Meara, acting on lattices by `Lat.image`), the image of the set $\mathcal G(L)$ (`omearaG Q L`) under $\sigma$ is
$\mathcal G(\sigma L)$. -/
@[kb "omeara1963" "§106B, p. 325 (σ G(L) = G(σL) for σ in O_n(V))"]
theorem omeara106_r17 (L : Lat ℚ n) {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup Q ℚ) :
    Lat.image γ '' omearaG Q L = omearaG Q (Lat.image γ L) := by
  ext M
  constructor
  · rintro ⟨K, hK, rfl⟩
    exact image_mem_omearaG Q hγ hK
  · intro hM
    refine ⟨Lat.image γ⁻¹ M, ?_, ?_⟩
    · have := image_mem_omearaG Q ((orthGroup Q ℚ).inv_mem hγ) hM
      have e : Lat.image γ⁻¹ (Lat.image γ L) = L := by
        apply Lat.ext
        show glImage γ⁻¹ (glImage γ L.1) = L.1
        rw [← glImage_mul, inv_mul_cancel, glImage_one]
      rwa [e] at this
    · apply Lat.ext
      show glImage γ (glImage γ⁻¹ M.1) = M.1
      rw [← glImage_mul, mul_inv_cancel, glImage_one]

/-- If $2M' \subseteq M$ and $2$ is a unit at $v$, then $M'_v \subseteq M_v$. -/
theorem loc_le_of_two_smul_mem (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal)
    {M M' : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : ∀ x ∈ M', (2 : ℚ) • x ∈ M) : loc v M' ≤ loc v M := by
  rw [loc, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have h2 : Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) 2) = 1 := by
    rw [valued_algebraMap_int]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hv
  have h2' : Valued.v ((2 : v.adicCompletion ℚ)⁻¹) ≤ 1 := by
    rw [map_inv₀, ← map_ofNat (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ)) 2, h2]
    simp
  have e : locVec v x = (toO v _ h2') • locVec v ((2 : ℚ) • x) := by
    ext i
    rw [smul_apply_coe]
    simp only [locVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, toO]
    rw [map_ofNat]
    field_simp
  rw [e]
  exact Submodule.smul_mem _ _ (locVec_mem_loc v (h x hx))

/-- **106.r21: adjacent unimodular lattices lie in the same $\mathcal G$** (O'Meara 1973, §106B, p. 326). If $K$ and
$L$ are lattices on $V = \mathbb Q^n$, $K$ unimodular and adjacent to $L$ (`Nbr.IsNbrL Q 2 L K`, the $2$-neighbour
relation, which for unimodular lattices is O'Meara's adjacency, see `Sec106C.lean`), then $K \in \mathcal G(L)$.
(Unimodularity of $L$ is not needed here: $2K \subseteq L$ and $2L \subseteq K$ give $K_p = L_p$ at every odd $p$,
and $K$ is unimodular by hypothesis.) -/
@[kb "omeara1963" "§106B, p. 326 (K adjacent to L implies K in G(L))"]
theorem omeara106_r21 (K L : Lat ℚ n) (hK : IsUnimodularZ Q K.1) (hadj : Nbr.IsNbrL Q 2 L.1 K.1) :
    K ∈ omearaG Q L := by
  refine ⟨hK, fun v hv => le_antisymm ?_ ?_⟩
  · refine loc_le_of_two_smul_mem v hv fun x hx => ?_
    have := hadj.smul_left x hx
    rwa [map_ofNat] at this
  · refine loc_le_of_two_smul_mem v hv fun x hx => ?_
    have := hadj.smul_right x hx
    rwa [map_ofNat] at this

/-! ### 106.r24: finitely many adjacent lattices -/

/-- **Finitely many lattices between $2L$ and $\tfrac12L$:** for a lattice $L$ on $V = \mathbb Q^n$, only finitely many
$\mathbb Z$-submodules $K$ of $V$ satisfy $2L \subseteq K$ and $2K \subseteq L$. (Such a $K$ lies between two boxes
$c\mathbb Z^n \subseteq K \subseteq c^{-1}\mathbb Z^n$ and is determined by its image modulo $c^2$.) -/
theorem finite_between_two (L : Submodule (𝓞 ℚ) (Fin n → ℚ)) (hL : L.IsLattice ℚ) :
    {K : Submodule (𝓞 ℚ) (Fin n → ℚ) |
      (∀ x ∈ L, (2 : 𝓞 ℚ) • x ∈ K) ∧ (∀ x ∈ K, (2 : 𝓞 ℚ) • x ∈ L)}.Finite := by
  classical
  obtain ⟨d, hd0, hd1, hd2⟩ := exists_global_bounds hL
  set c : 𝓞 ℚ := d * 2 with hc
  have hc0 : c ≠ 0 := mul_ne_zero hd0 two_ne_zero
  set I : Ideal (𝓞 ℚ) := Ideal.span {c ^ 2} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero 2 hc0
  have : Finite (𝓞 ℚ ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  set S := {K : Submodule (𝓞 ℚ) (Fin n → ℚ) |
      (∀ x ∈ L, (2 : 𝓞 ℚ) • x ∈ K) ∧ (∀ x ∈ K, (2 : 𝓞 ℚ) • x ∈ L)} with hS
  have hup : ∀ K ∈ S, ∀ x ∈ K, c • x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
    intro K hK x hx
    rw [hc, mul_smul]
    exact hd2 _ (hK.2 x hx)
  have hlow : ∀ K ∈ S, ∀ z ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)), c • z ∈ K := by
    intro K hK z hz
    rw [hc, mul_comm, mul_smul]
    exact hK.1 _ (hd1 z hz)
  let code : Submodule (𝓞 ℚ) (Fin n → ℚ) → Set (Fin n → 𝓞 ℚ ⧸ I) := fun K =>
    {ζ | ∃ y ∈ K, ∃ w : Fin n → 𝓞 ℚ, (∀ i, (c • y) i = algebraMap (𝓞 ℚ) ℚ (w i)) ∧
      ζ = fun i => Ideal.Quotient.mk I (w i)}
  refine Set.Finite.of_finite_image (f := code) (Set.toFinite _) ?_
  have hcq : algebraMap (𝓞 ℚ) ℚ c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).mpr hc0
  have hle : ∀ K ∈ S, ∀ K' ∈ S, code K ⊆ code K' → K ≤ K' := by
    intro K hK K' hK' hsub y hy
    obtain ⟨w, hw⟩ : ∃ w : Fin n → 𝓞 ℚ, ∀ i, (c • y) i = algebraMap (𝓞 ℚ) ℚ (w i) := by
      have := hup K hK y hy
      choose w hw using this
      exact ⟨w, fun i => (hw i).symm⟩
    obtain ⟨y', hy', w', hw', hq⟩ := hsub ⟨y, hy, w, hw, rfl⟩
    have hu : ∀ i, ∃ u : 𝓞 ℚ, w i - w' i = c ^ 2 * u := by
      intro i
      have h1 := congrFun hq i
      rw [Ideal.Quotient.eq, hI, Ideal.mem_span_singleton] at h1
      exact h1
    choose u hu using hu
    have hdiff : y - y' = c • (fun i => algebraMap (𝓞 ℚ) ℚ (u i)) := by
      ext i
      have e1 := hw i
      have e2 := hw' i
      rw [smul_apply_int] at e1 e2
      rw [Pi.sub_apply, smul_apply_int]
      apply mul_left_cancel₀ hcq
      have e3 : algebraMap (𝓞 ℚ) ℚ (w i - w' i) = algebraMap (𝓞 ℚ) ℚ (c ^ 2 * u i) := by rw [hu i]
      rw [map_sub, map_mul, map_pow, ← e1, ← e2] at e3
      linear_combination e3
    have hmem : (fun i => algebraMap (𝓞 ℚ) ℚ (u i)) ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) :=
      fun i => ⟨u i, rfl⟩
    have : y = y' + c • (fun i => algebraMap (𝓞 ℚ) ℚ (u i)) := by rw [← hdiff]; abel
    rw [this]
    exact K'.add_mem hy' (hlow K' hK' _ hmem)
  intro K hK K' hK' heq
  exact le_antisymm (hle K hK K' hK' heq.le) (hle K' hK' K hK heq.ge)

/-- **106.r24: only finitely many lattices are adjacent to a given lattice** (O'Meara 1973, §106B, p. 326).
For a lattice $L$ on $V = \mathbb Q^n$ the set of $K$ adjacent to $L$ (`Nbr.IsNbrL Q 2 L K`, the $2$-neighbour
relation) is finite. (O'Meara: such $K$ lie between $2L$ and $\tfrac12L$, and the index $(\tfrac12L : 2L)$ is
finite.) -/
@[kb "omeara1963" "§106B, p. 326 (finitely many lattices adjacent to L)"]
theorem omeara106_r24 {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) :
    {K : Submodule (𝓞 ℚ) (Fin n → ℚ) | Nbr.IsNbrL Q 2 L K}.Finite := by
  refine (finite_between_two L hL).subset fun K hK => ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have := hK.smul_right x hx
    rwa [algebraMap_smul] at this
  · have := hK.smul_left x hx
    rwa [algebraMap_smul] at this

/-! ### 106.r10: completely decomposable unimodular lattices on $I_n$ -/

section SumSq

private theorem sumSq_eval' (x : Fin n → ℚ) : (sumSqForm n).eval x = ∑ i, x i ^ 2 := by
  rw [sumSqForm, QuadForm.eval, QuadForm.evalIn_diag]; simp

private theorem sumSq_bil' (x y : Fin n → ℚ) :
    bil (sumSqForm n) x y = 2 * ∑ i, x i * y i := by
  have h : (sumSqForm n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
    · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]
  rw [bil, h, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, dotProduct, smul_eq_mul]

/-- Vectors of $\mathbb Q^n$ with $\sum_i b_j(i)\,b_k(i) = \delta_{jk}$ are linearly independent. -/
theorem linIndep_of_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → Fin n → ℚ)
    (h : ∀ j k, ∑ i, b j i * b k i = if j = k then 1 else 0) : LinearIndependent ℚ b := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have h1 := congrArg (fun v : Fin n → ℚ => ∑ i, v i * b k i) hc
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero] at h1
  have e : ∑ i, (∑ j, c j * b j i) * b k i = c k := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, h, mul_ite, mul_one, mul_zero]
    simp
  linarith

/-- A matrix with orthonormal columns ($\gamma^{\mathsf T}\gamma = 1$) lies in $O(I_n)$. -/
theorem mem_orthGroup_sumSq {γ : GL (Fin n) ℚ} (h : γ.valᵀ * γ.val = 1) :
    γ ∈ orthGroup (sumSqForm n) ℚ := by
  refine mem_orthGroup_of_eval _ fun z => ?_
  rw [sumSq_eval', sumSq_eval']
  have e : ∀ w : Fin n → ℚ, ∑ i, w i ^ 2 = w ⬝ᵥ w := fun w => by simp [dotProduct, sq]
  rw [e, e, dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- The columns of an element of $O(I_n)$ are orthonormal. -/
theorem orthonormal_cols {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup (sumSqForm n) ℚ) (j k : Fin n) :
    ∑ i, (γ.val *ᵥ Pi.single j (1 : ℚ)) i * (γ.val *ᵥ Pi.single k (1 : ℚ)) i = if j = k then 1 else 0 := by
  have h := bil_isometry (sumSqForm n) hγ (Pi.single j 1) (Pi.single k 1)
  rw [sumSq_bil', sumSq_bil'] at h
  have h2 : ∑ i, (Pi.single j (1 : ℚ) : Fin n → ℚ) i * (Pi.single k (1 : ℚ) : Fin n → ℚ) i =
      if j = k then 1 else 0 := by
    by_cases hjk : j = k
    · subst hjk; simp [Pi.single_apply]
    · simp only [hjk, ↓reduceIte]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hij : i = j
      · subst hij
        simp [hjk]
      · simp [Pi.single_apply, hij]
  linarith

/-- **A matrix with $\mathcal O_F$-integral... orthonormal columns:** $\gamma \in O(I_n)$ with columns
$g_j = \gamma e_j$; the lattice $\gamma\mathbb Z^n$ is the sum of the lines $\mathbb Zg_j$. -/
theorem isCompletelyDecomposable_of_isIsometric {D : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (h : IsIsometric (sumSqForm n) intVec D) : IsCompletelyDecomposable (sumSqForm n) D := by
  classical
  obtain ⟨γ, hγ, rfl⟩ := h
  set g : Fin n → Fin n → ℚ := fun j => γ.val *ᵥ Pi.single j (1 : ℚ) with hg
  have hon : ∀ j k, ∑ i, g j i * g k i = if j = k then 1 else 0 := orthonormal_cols hγ
  have hli : LinearIndependent ℚ g := linIndep_of_orthonormal g hon
  have hg0 : ∀ j, g j ≠ 0 := hli.ne_zero
  have hbil : ∀ j k, bil (sumSqForm n) (g j) (g k) = if j = k then 2 else 0 := by
    intro j k
    rw [sumSq_bil', hon]
    split_ifs <;> simp
  set K : Fin n → Submodule (𝓞 ℚ) (Fin n → ℚ) := fun j => Submodule.span (𝓞 ℚ) {g j} with hK
  have hKq : ∀ j, Submodule.span ℚ ((K j : Submodule (𝓞 ℚ) (Fin n → ℚ)) : Set (Fin n → ℚ)) =
      Submodule.span ℚ {g j} := by
    intro j
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [SetLike.mem_coe, ← algebraMap_smul ℚ r (g j)]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span (Submodule.mem_span_singleton_self _)
  have hKorth : ∀ j k, j ≠ k → LatOrth (sumSqForm n) (K j) (K k) := by
    intro j k hjk x hx y hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨r', hr'⟩ := exists_int_smul_eq r (g j)
    obtain ⟨s', hs'⟩ := exists_int_smul_eq s (g k)
    rw [hr', hs', bil_smul_left', bil_smul_right', hbil]
    simp [hjk]
  have hKinj : Function.Injective K := by
    intro j k hjk
    by_contra hne
    have hmem : g j ∈ K k := by rw [← hjk]; exact Submodule.mem_span_singleton_self _
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    obtain ⟨r', hr'⟩ := exists_int_smul_eq r (g k)
    have h1 := hbil j k
    simp only [hne, ↓reduceIte] at h1
    rw [← hr, hr', bil_smul_left', hbil] at h1
    simp only [↓reduceIte] at h1
    have h2 : (r' : ℚ) = 0 := by linarith
    rw [hr', h2] at hr
    exact hg0 j (by rw [← hr]; simp)
  have hliO : LinearIndependent (𝓞 ℚ) g := (LinearIndependent.iff_fractionRing (𝓞 ℚ) ℚ).mpr hli
  have hindep : iSupIndep K := hliO.iSupIndep_span_singleton
  refine ⟨Finset.univ.image K, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro M hM
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hM
    intro h0
    have : g j ∈ K j := Submodule.mem_span_singleton_self _
    rw [h0] at this
    exact hg0 j ((Submodule.mem_bot _).mp this)
  · intro M hM M' hM' hne
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hM'
    exact hKorth j k fun h => hne (by rw [h])
  · have hf : ∀ M : ↥(Finset.univ.image K), ∃ j, K j = M := fun M => by
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp M.2
      exact ⟨j, hj⟩
    choose f hf using hf
    have hfi : Function.Injective f := fun M M' h => Subtype.ext (by rw [← hf M, ← hf M', h])
    have := hindep.comp hfi
    convert this using 1
    funext M
    exact (hf M).symm
  · rw [Finset.sup_image]
    apply le_antisymm
    · refine Finset.sup_le fun j _ => ?_
      rw [Function.comp_apply, id]
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact mulVec_mem_glImage (single_one_mem_intVec j)
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := eq_sum_of_mem_intVec hy
      have e : γ.val *ᵥ (∑ i, c i • (Pi.single i (1 : ℚ) : Fin n → ℚ)) = ∑ i, c i • g i := by
        have := map_sum ((Matrix.mulVecLin γ.val).restrictScalars (𝓞 ℚ))
          (fun i => c i • (Pi.single i (1 : ℚ) : Fin n → ℚ)) Finset.univ
        simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, map_smul] using this
      show γ.val *ᵥ _ ∈ _
      rw [e]
      exact Submodule.sum_mem _ fun i _ =>
        (Finset.le_sup (f := fun j => K j) (Finset.mem_univ i))
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · intro M hM
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hM
    rw [hKq, finrank_span_singleton (hg0 j)]

/-- $\mathcal O_{\mathbb Q} \cong \mathbb Z$ is a principal ideal domain. -/
theorem pid_ringOfIntegers_rat : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom
    Rat.ringOfIntegersEquiv.symm.surjective

theorem bil_sum_left_aux {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℚ) (y : Fin n → ℚ) :
    bil Q (∑ i ∈ s, f i) y = ∑ i ∈ s, bil Q (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bil]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bil_add_left', ih]

/-- A sublattice $K$ of a lattice $D$ on $V$ whose $\mathbb Q$-span is a line is cyclic: $K = \mathbb Zx$. -/
theorem exists_gen_of_rank_one {K D : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hD : D.IsLattice ℚ) (hKD : K ≤ D)
    (hK0 : K ≠ ⊥) (hrk : Module.finrank ℚ (Submodule.span ℚ (K : Set (Fin n → ℚ))) = 1) :
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ K = Submodule.span (𝓞 ℚ) {x} := by
  have := pid_ringOfIntegers_rat
  have hKfg : K.FG := Submodule.FG.of_le hD.fg hKD
  obtain ⟨y, hyK, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
  have hy' : y ∈ Submodule.span ℚ (K : Set (Fin n → ℚ)) := Submodule.subset_span hyK
  obtain ⟨c, hc0, hmax⟩ := OMeara.exists_isMaxVec_of_principal
    (fun a ha => OMeara.exists_eq_span_of_fg a ha) hKfg hy' hy0
  have hspan : Submodule.span ℚ {y} = Submodule.span ℚ (K : Set (Fin n → ℚ)) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy'
    · rw [finrank_span_singleton hy0, hrk]
  refine ⟨c • y, smul_ne_zero hc0 hy0, le_antisymm ?_ ?_⟩
  · intro z hz
    have hz' : z ∈ Submodule.span ℚ {y} := by rw [hspan]; exact Submodule.subset_span hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz'
    have e : (a / c) • (c • y) = a • y := by rw [smul_smul]; field_simp
    have hmem : (a / c) • (c • y) ∈ K := by rw [e]; exact hz
    obtain ⟨r, hr⟩ := hmax.2 _ hmem
    rw [Submodule.mem_span_singleton]
    refine ⟨r, ?_⟩
    rw [← algebraMap_smul ℚ r (c • y), hr, e]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hmax.1

/-- A completely decomposable unimodular lattice on $I_n$ has an orthonormal base, hence is $\gamma\mathbb Z^n$ for an
isometry $\gamma \in O(I_n)$. -/
theorem isIsometric_of_isCompletelyDecomposable {D : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hD : D.IsLattice ℚ)
    (hu : IsUnimodularZ (sumSqForm n) D) (h : IsCompletelyDecomposable (sumSqForm n) D) :
    IsIsometric (sumSqForm n) intVec D := by
  classical
  obtain ⟨S, hS, hrk⟩ := h
  have hle : ∀ K ∈ S, K ≤ D := fun K hK => hS.sup_eq ▸ Finset.le_sup (f := id) hK
  have hgen : ∀ K : ↥S, ∃ x : Fin n → ℚ, x ≠ 0 ∧
      (K : Submodule (𝓞 ℚ) (Fin n → ℚ)) = Submodule.span (𝓞 ℚ) {x} :=
    fun K => exists_gen_of_rank_one hD (hle K K.2) (hS.ne_bot K K.2) (hrk K K.2)
  choose X hX0 hKX using hgen
  have hXK : ∀ K : ↥S, X K ∈ (K : Submodule (𝓞 ℚ) (Fin n → ℚ)) := fun K => by
    rw [hKX K]; exact Submodule.mem_span_singleton_self _
  have hXD : ∀ K, X K ∈ D := fun K => hle K K.2 (hXK K)
  have hXorth : ∀ K K' : ↥S, K ≠ K' → bil (sumSqForm n) (X K) (X K') = 0 := fun K K' hne =>
    hS.orth K K.2 K' K'.2 (fun h => hne (Subtype.ext h)) (X K) (hXK K) (X K') (hXK K')
  have hDspan : D = Submodule.span (𝓞 ℚ) (Set.range X) := by
    apply le_antisymm
    · rw [← hS.sup_eq]
      refine Finset.sup_le fun K hK => ?_
      have e := hKX ⟨K, hK⟩
      simp only at e
      show K ≤ _
      rw [e, Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨⟨K, hK⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨K, rfl⟩
      exact hXD K
  have hqpos : ∀ K, 0 < (sumSqForm n).eval (X K) := by
    intro K
    rw [sumSq_eval']
    obtain ⟨i, hi⟩ : ∃ i, X K i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hX0 K (funext hcon)
    exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))
      (Finset.single_le_sum (f := fun i => X K i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i))
  have hq1 : ∀ K, (sumSqForm n).eval (X K) = 1 := by
    intro K
    obtain ⟨m, hm⟩ := uni_Q_int (sumSqForm n) hu (hXD K)
    have hmpos : (0 : ℚ) < m := hm ▸ hqpos K
    have hcoef : ∀ w ∈ D, ∃ r : ℤ, bil (sumSqForm n) (X K) w = 2 * m * r := by
      intro w hw
      rw [hDspan] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨K', rfl⟩ := hw
        by_cases hKK : K = K'
        · subst hKK
          exact ⟨1, by rw [bil_self_eq, hm]; ring⟩
        · exact ⟨0, by rw [hXorth K K' hKK]; simp⟩
      | zero => exact ⟨0, by simp [bil]⟩
      | add w w' _ _ h h' =>
        obtain ⟨r, hr⟩ := h
        obtain ⟨r', hr'⟩ := h'
        exact ⟨r + r', by rw [bil_add_right', hr, hr']; push_cast; ring⟩
      | smul c w _ h =>
        obtain ⟨r, hr⟩ := h
        obtain ⟨k, hk⟩ := exists_int_smul_eq c w
        exact ⟨k * r, by rw [hk, bil_smul_right', hr]; push_cast; ring⟩
    have hy : (m : ℚ)⁻¹ • X K ∈ D := by
      have : (m : ℚ)⁻¹ • X K ∈ omearaDual (sumSqForm n) D := by
        intro w hw
        obtain ⟨r, hr⟩ := hcoef w hw
        refine ⟨r, ?_⟩
        rw [bil_smul_left', hr]
        field_simp
      rw [show omearaDual (sumSqForm n) D = D from hu] at this
      exact this
    rw [hDspan] at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 ℚ)).mp hy
    choose k hk using fun K' => exists_int_smul_eq (c K') (X K')
    have hc' : ∑ K', (k K' : ℚ) • X K' = (m : ℚ)⁻¹ • X K := by
      rw [← hc]
      exact Finset.sum_congr rfl fun K' _ => (hk K').symm
    have hpair := congrArg (fun v => bil (sumSqForm n) v (X K)) hc'
    rw [bil_sum_left_aux] at hpair
    simp_rw [bil_smul_left'] at hpair
    rw [Finset.sum_eq_single K] at hpair
    · rw [bil_self_eq, hm] at hpair
      have h2 : (k K : ℚ) * m = 1 := by
        have : (k K : ℚ) * (2 * m) = (m : ℚ)⁻¹ * (2 * m) := hpair
        have hm0 : (m : ℚ) ≠ 0 := hmpos.ne'
        field_simp at this
        linarith
      have h3 : k K * m = 1 := by exact_mod_cast h2
      have hm1 : m = 1 := Int.eq_one_of_mul_eq_one_left (by exact_mod_cast hmpos.le) h3
      rw [hm, hm1]; simp
    · intro K' _ hK'
      rw [hXorth K' K hK', mul_zero]
    · intro hK
      exact absurd (Finset.mem_univ K) hK
  have hon : ∀ K K' : ↥S, ∑ i, X K i * X K' i = if K = K' then 1 else 0 := by
    intro K K'
    have h1 := sumSq_bil' (X K) (X K')
    by_cases hKK : K = K'
    · subst hKK
      simp only [↓reduceIte]
      have := bil_self_eq (sumSqForm n) (X K)
      rw [hq1, h1] at this
      linarith
    · simp only [hKK, ↓reduceIte]
      rw [hXorth K K' hKK] at h1
      linarith
  have hli : LinearIndependent ℚ X := linIndep_of_orthonormal X hon
  have hspan : Submodule.span ℚ (Set.range X) = ⊤ := by
    rw [eq_top_iff, ← hD.span_eq_top, Submodule.span_le]
    intro x hx
    have : x ∈ Submodule.span (𝓞 ℚ) (Set.range X) := by rw [← hDspan]; exact hx
    exact Submodule.span_le_restrictScalars (𝓞 ℚ) ℚ (Set.range X) this
  have hcard : Fintype.card ↥S = n := by
    have h1 := finrank_span_eq_card hli
    rw [hspan, finrank_top, Module.finrank_fin_fun] at h1
    exact h1.symm
  let e : ↥S ≃ Fin n := Fintype.equivFinOfCardEq hcard
  set b : Fin n → Fin n → ℚ := fun j => X (e.symm j) with hb
  set M : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => b j i with hM
  have hMM : Mᵀ * M = 1 := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hM, Matrix.of_apply, Matrix.one_apply]
    rw [hb]
    simp only
    rw [hon]
    simp
  have hdet : M.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_transpose, h0] at this
    simp at this
  let γ : GL (Fin n) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
  have hγval : γ.val = M := rfl
  have hγo : γ ∈ orthGroup (sumSqForm n) ℚ := mem_orthGroup_sumSq (by rw [hγval]; exact hMM)
  have hγcol : ∀ j, γ.val *ᵥ Pi.single j (1 : ℚ) = b j := by
    intro j
    ext i
    simp [hγval, hM]
  refine ⟨γ, hγo, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := eq_sum_of_mem_intVec hy
    have e1 : γ.val *ᵥ (∑ i, c i • (Pi.single i (1 : ℚ) : Fin n → ℚ)) = ∑ i, c i • b i := by
      have := map_sum ((Matrix.mulVecLin γ.val).restrictScalars (𝓞 ℚ))
        (fun i => c i • (Pi.single i (1 : ℚ) : Fin n → ℚ)) Finset.univ
      simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, map_smul, hγcol] using this
    show γ.val *ᵥ _ ∈ D
    rw [e1]
    exact Submodule.sum_mem _ fun j _ => D.smul_mem _ (hXD _)
  · intro hx
    rw [hDspan] at hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 ℚ)).mp hx
    refine ⟨fun j => algebraMap (𝓞 ℚ) ℚ (c (e.symm j)), fun j => ⟨_, rfl⟩, ?_⟩
    show γ.val *ᵥ _ = x
    rw [← hc]
    ext i
    simp only [hγval, hM, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      hb]
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    ring

/-- **106.r10: a unimodular lattice on $I_n$ is completely decomposable iff it has the matrix $I_n$** (O'Meara
1973, §106, p. 324). Let $V = \mathbb Q^n$ with $Q = x_0^2 + \dots + x_{n-1}^2$ (`sumSqForm n`, O'Meara's
$V = I_n$) and $D$ a unimodular lattice on $V$ ($D^\# = D$). Then $D$ is completely decomposable (an orthogonal sum
of lattices of dimension $1$, `IsCompletelyDecomposable`) if and only if $D$ has the matrix $I_n$, that is, $D$ has
a base $x_0, \dots, x_{n-1}$ with $B(x_i, x_j) = \delta_{ij}$; this is expressed as `IsIsometric (sumSqForm n) intVec D`
($D = \gamma\mathbb Z^n$ for an isometry $\gamma \in O(V)$, whose columns are the base). The proof of "$\Rightarrow$"
uses that $I_n$ is positive definite: a rank-one unimodular component $\mathbb Zx$ has $Q(x) = 1$.
(Only "$\Rightarrow$" uses that $D$ is a unimodular lattice; "$\Leftarrow$" holds for every $D = \gamma\mathbb Z^n$.) -/
@[kb "omeara1963" "§106, p. 324 (completely decomposable iff the matrix is I_n)"]
theorem omeara106_r10 {D : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hD : D.IsLattice ℚ)
    (hu : IsUnimodularZ (sumSqForm n) D) :
    IsCompletelyDecomposable (sumSqForm n) D ↔ IsIsometric (sumSqForm n) intVec D :=
  ⟨isIsometric_of_isCompletelyDecomposable hD hu, isCompletelyDecomposable_of_isIsometric⟩

end SumSq

/-! ### Volume and index of lattices -/

section Index

open Module

/-- The underlying additive group of the $\mathbb Z$-span of a finite family is its additive closure. -/
theorem toAddSubgroup_span_range {ι : Type*} [Fintype ι] (x : ι → Fin n → ℚ) :
    (Submodule.span (𝓞 ℚ) (Set.range x)).toAddSubgroup = AddSubgroup.closure (Set.range x) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 ℚ)).mp hz
    choose k hk using fun i => exists_int_smul_eq (c i) (x i)
    have e : ∑ i, c i • x i = ∑ i, (k i) • x i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hk i, Int.cast_smul_eq_zsmul]
    show ∑ i, c i • x i ∈ AddSubgroup.closure (Set.range x)
    rw [e]
    exact AddSubgroup.sum_mem _ fun i _ =>
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  · rw [AddSubgroup.closure_le]
    intro z hz
    exact Submodule.subset_span hz

/-- $(1 : \text{Submodule}) \ne \bot$ in $\mathbb Q$ over $\mathcal O_{\mathbb Q}$. -/
theorem one_submodule_ne_bot : (1 : Submodule (𝓞 ℚ) ℚ) ≠ ⊥ := by
  intro h
  have h1 : (1 : ℚ) ∈ (1 : Submodule (𝓞 ℚ) ℚ) := Submodule.one_le.1 le_rfl
  rw [h] at h1
  exact one_ne_zero ((Submodule.mem_bot (𝓞 ℚ)).1 h1)

/-- **The volume of the lattice generated by a $\mathbb Q$-independent family** is $d(x)\mathbb Z$,
$d(x) = \det(B(x_i, x_j))$. -/
theorem volume_famLat {x : Fin n → Fin n → ℚ} (hx : LinearIndependent ℚ x) :
    OMeara.volume Q.toQuadraticForm (Submodule.span (𝓞 ℚ) (Set.range x)) =
      Submodule.span (𝓞 ℚ) {(OMeara.gram Q.toQuadraticForm x).det} := by
  have h1fg : (1 : Submodule (𝓞 ℚ) ℚ).FG := by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  have := OMeara.volume_eq_of_adapted_fintype Q.toQuadraticForm x hx (fun _ => 1)
    (fun _ => ⟨h1fg, one_submodule_ne_bot⟩)
  simpa [Submodule.one_smul, ← Submodule.span_range_eq_iSup] using this

/-- **Every lattice on $V = \mathbb Q^n$ is generated by a $\mathbb Q$-independent family** of $n$ vectors (it is free,
$\mathcal O_{\mathbb Q} = \mathbb Z$ being a principal ideal domain). -/
theorem exists_family_of_lattice {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : M.IsLattice ℚ) :
    ∃ x : Fin n → Fin n → ℚ, LinearIndependent ℚ x ∧ M = Submodule.span (𝓞 ℚ) (Set.range x) := by
  have := pid_ringOfIntegers_rat
  obtain ⟨γ, hγ⟩ := HilbertModular.exists_latOf_of_isPrincipalIdealRing (n := n) (⟨M, hM⟩ : Lat ℚ n)
  refine ⟨fun j => γ.val *ᵥ Pi.single j (1 : ℚ), ?_, ?_⟩
  · have h := (Pi.basisFun ℚ (Fin n)).linearIndependent.map' (Matrix.mulVecLin γ.val)
      (LinearMap.ker_eq_bot.mpr (Nbr.mulVec_injective_gl γ))
    convert h using 1
    funext j
    simp
  · rw [show M = latOf γ from hγ, latOf]
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := eq_sum_of_mem_intVec hy
      have e1 : γ.val *ᵥ (∑ i, c i • (Pi.single i (1 : ℚ) : Fin n → ℚ)) =
          ∑ i, c i • (γ.val *ᵥ Pi.single i (1 : ℚ)) := by
        have := map_sum ((Matrix.mulVecLin γ.val).restrictScalars (𝓞 ℚ))
          (fun i => c i • (Pi.single i (1 : ℚ) : Fin n → ℚ)) Finset.univ
        simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, map_smul] using this
      show γ.val *ᵥ _ ∈ _
      rw [e1]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact mulVec_mem_glImage (single_one_mem_intVec j)

/-- A $\mathbb Q$-independent family of $n$ vectors is a $\mathbb Q$-base of $V = \mathbb Q^n$ when it spans a lattice. -/
theorem span_eq_top_of_lattice {x : Fin n → Fin n → ℚ} {M : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hM : M.IsLattice ℚ) (hx : M = Submodule.span (𝓞 ℚ) (Set.range x)) :
    ⊤ ≤ Submodule.span ℚ (Set.range x) := by
  rw [← hM.span_eq_top, Submodule.span_le]
  intro z hz
  have : z ∈ Submodule.span (𝓞 ℚ) (Set.range x) := by rw [← hx]; exact hz
  exact Submodule.span_le_restrictScalars (𝓞 ℚ) ℚ (Set.range x) this

/-- **Volume and index** (O'Meara 1973, §82E, p. 230, over $\mathbb Z$): for lattices $N \subseteq M$ on $V = \mathbb Q^n$,
$\mathfrak vN = [M : N]^2\,\mathfrak vM$. -/
theorem volume_eq_index_sq_mul {M N : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : M.IsLattice ℚ)
    (hN : N.IsLattice ℚ) (hle : N ≤ M) :
    OMeara.volume Q.toQuadraticForm N =
      Submodule.span (𝓞 ℚ) {((N.toAddSubgroup.relIndex M.toAddSubgroup : ℕ) : ℚ) ^ 2} *
        OMeara.volume Q.toQuadraticForm M := by
  classical
  obtain ⟨x, hx, hMx⟩ := exists_family_of_lattice hM
  obtain ⟨y, hy, hNy⟩ := exists_family_of_lattice hN
  have hmem : ∀ i, y i ∈ Submodule.span (𝓞 ℚ) (Set.range x) := fun i =>
    hMx ▸ hle (hNy ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose T hT using fun i => (Submodule.mem_span_range_iff_exists_fun (𝓞 ℚ)).mp (hmem i)
  set Tm : Matrix (Fin n) (Fin n) (𝓞 ℚ) := Matrix.of T with hTm
  have hy' : y = fun i => ∑ j, Tm i j • x j := funext fun i => (hT i).symm
  -- bases
  set b₂ : Basis (Fin n) ℚ (Fin n → ℚ) := Basis.mk hx (span_eq_top_of_lattice hM hMx) with hb₂
  set b₁ : Basis (Fin n) ℚ (Fin n → ℚ) := Basis.mk hy (span_eq_top_of_lattice hN hNy) with hb₁
  have hdet : b₂.det b₁ = algebraMap (𝓞 ℚ) ℚ Tm.det := by
    rw [Basis.det_apply]
    have : b₂.toMatrix b₁ = (Tm.map (algebraMap (𝓞 ℚ) ℚ))ᵀ := by
      ext i j
      rw [Basis.toMatrix_apply, hb₁, Basis.mk_apply, hy']
      have e : (∑ k, Tm j k • x k) = ∑ k, (algebraMap (𝓞 ℚ) ℚ (Tm j k)) • b₂ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hb₂, Basis.mk_apply, algebraMap_smul]
      show b₂.repr (∑ k, Tm j k • x k) i = _
      rw [e, Basis.repr_sum_self]
      simp
    rw [this, Matrix.det_transpose]
    exact (RingHom.map_det (algebraMap (𝓞 ℚ) ℚ) Tm).symm
  have hidx : ((N.toAddSubgroup.relIndex M.toAddSubgroup : ℕ) : ℚ) = |algebraMap (𝓞 ℚ) ℚ Tm.det| := by
    have := AddSubgroup.relIndex_eq_abs_det N.toAddSubgroup M.toAddSubgroup hle b₁ b₂
      (by rw [hNy, toAddSubgroup_span_range, hb₁]; simp)
      (by rw [hMx, toAddSubgroup_span_range, hb₂]; simp)
    rw [this, hdet]
  rw [hidx, hNy, hMx, volume_famLat Q hy, volume_famLat Q hx, Submodule.span_mul_span,
    Set.singleton_mul_singleton, sq_abs]
  congr 2
  have hg : OMeara.gram Q.toQuadraticForm y =
      Tm.map (algebraMap (𝓞 ℚ) ℚ) * OMeara.gram Q.toQuadraticForm x * (Tm.map (algebraMap (𝓞 ℚ) ℚ))ᵀ := by
    rw [hy']
    exact OMeara.gram_comb Q.toQuadraticForm x Tm
  have hdm : (Tm.map (algebraMap (𝓞 ℚ) ℚ)).det = algebraMap (𝓞 ℚ) ℚ Tm.det :=
    (RingHom.map_det (algebraMap (𝓞 ℚ) ℚ) Tm).symm
  rw [hg, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdm]
  ring

end Index

/-! ### 106:5 -/

section Five

/-- The intersection of two lattices on $V$ is a lattice on $V$. -/
theorem isLattice_inf {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : K.IsLattice ℚ) (hL : L.IsLattice ℚ) :
    (K ⊓ L).IsLattice ℚ := by
  obtain ⟨d₁, hd₁, h₁, h₁'⟩ := exists_global_bounds hK
  obtain ⟨d₂, hd₂, h₂, h₂'⟩ := exists_global_bounds hL
  refine isLattice_of_global_bounds (d := d₁ * d₂) (mul_ne_zero hd₁ hd₂) ?_ ?_
  · intro x hx
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mul_smul]; exact h₁ _ (intVec.smul_mem _ hx)
    · rw [mul_comm, mul_smul]; exact h₂ _ (intVec.smul_mem _ hx)
  · intro x hx
    rw [mul_smul]
    exact intVec.smul_mem _ (h₂' x (Submodule.mem_inf.mp hx).2)

/-- The sum of two lattices on $V$ is a lattice on $V$. -/
theorem isLattice_sup {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : K.IsLattice ℚ) (hL : L.IsLattice ℚ) :
    (K ⊔ L).IsLattice ℚ where
  fg := hK.fg.sup hL.fg
  span_eq_top := by
    rw [eq_top_iff, ← hK.span_eq_top]
    exact Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left)

/-- $(K + L)^\# = K^\# \cap L^\# = K \cap L$ for unimodular $K, L$ (O'Meara 1973, p. 328, proof of 106:5). -/
theorem omearaDual_sup {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : IsUnimodularZ Q K)
    (hL : IsUnimodularZ Q L) : omearaDual Q (K ⊔ L) = K ⊓ L := by
  ext x
  constructor
  · intro hx
    have hxK : x ∈ omearaDual Q K := fun y hy => hx y (Submodule.mem_sup_left hy)
    have hxL : x ∈ omearaDual Q L := fun y hy => hx y (Submodule.mem_sup_right hy)
    rw [show omearaDual Q K = K from hK] at hxK
    rw [show omearaDual Q L = L from hL] at hxL
    exact Submodule.mem_inf.mpr ⟨hxK, hxL⟩
  · intro hx z hz
    obtain ⟨hxK, hxL⟩ := Submodule.mem_inf.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨m1, hm1⟩ := uni_mem' Q hK hxK ha
    obtain ⟨m2, hm2⟩ := uni_mem' Q hL hxL hb
    exact ⟨m1 + m2, by rw [bil_add_right', add_div, hm1, hm2]; push_cast; rfl⟩

/-- The volume of a unimodular lattice on $V$ ($n \ge 1$) is $\mathbb Z$. -/
theorem volume_eq_one_of_unimodular {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) (hn : 0 < n)
    (hu : IsUnimodularZ Q L) : OMeara.volume Q.toQuadraticForm L = 1 := by
  have h := (isUnimodular_of_isUnimodularZ Q hL hn hu).2.2
  rw [h, one_pow]

private theorem nm_two' : HilbertModular.nm (2 : 𝓞 ℚ) = 2 := by
  have h : (2 : 𝓞 ℚ) = ((2 : ℕ) : 𝓞 ℚ) := by norm_num
  rw [h, HilbertModular.nm_natCast, NumberField.RingOfIntegers.rank]
  simp

private theorem inf_index_left {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : Nbr.IsNbrL Q 2 L K) :
    (K ⊓ L).toAddSubgroup.relIndex L.toAddSubgroup = 2 := by
  have h1 := h.index_left
  rw [nm_two'] at h1
  have e : (K ⊓ L).toAddSubgroup = K.toAddSubgroup ⊓ L.toAddSubgroup := rfl
  rw [e, AddSubgroup.inf_relIndex_right, h1]

private theorem inf_index_right {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : Nbr.IsNbrL Q 2 L K) :
    (K ⊓ L).toAddSubgroup.relIndex K.toAddSubgroup = 2 := by
  have h1 := h.index_right
  rw [nm_two'] at h1
  have e : (K ⊓ L).toAddSubgroup = K.toAddSubgroup ⊓ L.toAddSubgroup := rfl
  rw [e, AddSubgroup.inf_relIndex_left, h1]

private theorem two_smul_mem_of_index {N M : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (h : N.toAddSubgroup.relIndex M.toAddSubgroup = 2) {x : Fin n → ℚ} (hx : x ∈ M) :
    algebraMap (𝓞 ℚ) ℚ 2 • x ∈ N := by
  have := AddSubgroup.nsmul_relIndex_mem N.toAddSubgroup (K := M.toAddSubgroup) (g := x) hx
  rw [h] at this
  have e : algebraMap (𝓞 ℚ) ℚ 2 • x = 2 • x := by
    rw [map_ofNat, two_smul, two_nsmul]
  rw [e]
  exact this

/-- If $\mathbb Z c^2 = \mathbb Z\cdot 4$ (as submodules of $\mathbb Q$) for a natural number $c$, then $c = 2$. -/
private theorem nat_eq_two_of_span_sq (c : ℕ)
    (h : Submodule.span (𝓞 ℚ) {((c : ℚ)) ^ 2} = Submodule.span (𝓞 ℚ) {(4 : ℚ)}) : c = 2 := by
  have h1 : ((c : ℚ)) ^ 2 ∈ Submodule.span (𝓞 ℚ) {(4 : ℚ)} := h ▸ Submodule.mem_span_singleton_self _
  have h2 : (4 : ℚ) ∈ Submodule.span (𝓞 ℚ) {((c : ℚ)) ^ 2} := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h2
  rw [Algebra.smul_def, ← Rat.ringOfIntegersEquiv_apply_coe] at ha hb
  set k := Rat.ringOfIntegersEquiv a
  set m := Rat.ringOfIntegersEquiv b
  have e3 : (m : ℚ) * k = 1 := by
    have : (m : ℚ) * ((k : ℚ) * 4) = 4 := by rw [ha]; exact hb
    linarith
  have e4 : m * k = 1 := by exact_mod_cast e3
  have hk : k = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' e4 with ⟨-, hk⟩ | ⟨-, hk⟩
    · exact hk
    · exfalso
      rw [hk] at ha
      push_cast at ha
      nlinarith [sq_nonneg (c : ℚ)]
  rw [hk] at ha
  have e5 : (c : ℚ) ^ 2 = 2 ^ 2 := by rw [← ha]; norm_num
  have e6 : c ^ 2 = 2 ^ 2 := by exact_mod_cast e5
  exact Nat.pow_left_injective (by norm_num) e6

/-- **Proposition 106:5** (O'Meara 1973, §106C, p. 328). Let $K$ and $L$ be unimodular lattices on $V = \mathbb Q^n$
($K, L$ lattices on $V$ with $K^\# = K$, $L^\# = L$; $n \ge 1$) and $\mathfrak v$ the volume (`OMeara.volume`, over
$\mathcal O_{\mathbb Q} = \mathbb Z$, for the form `Q.toQuadraticForm`). The following are equivalent:
(1) $K$ is adjacent to $L$ (`Nbr.IsNbrL Q 2 L K`, the $2$-neighbour relation, which for unimodular lattices is
O'Meara's adjacency, see `Sec106C.lean`); (2) $\mathfrak v(K + L) = \tfrac14\mathbb Z$; (3) $\mathfrak v(K \cap L) =
4\mathbb Z$. It is stated as $(1) \Leftrightarrow (2)$ and $(2) \Leftrightarrow (3)$. The proof follows O'Meara for
$(2) \Leftrightarrow (3)$ (duality: $K \cap L = (K + L)^\#$ and $\mathfrak v L^\# \cdot \mathfrak v L = \mathfrak o$), and
replaces the Invariant Factor Theorem in $(3) \Rightarrow (1)$ by the formula $\mathfrak vN = [M:N]^2\mathfrak vM$ for
lattices $N \subseteq M$ (`volume_eq_index_sq_mul`, from the index as a determinant). This holds for every form $Q$
(O'Meara has $V = I_n$; positive definiteness is not used). -/
@[kb "omeara1963" "§106C, 106:5, p. 328 (K adjacent to L iff v(K+L) = 1/4 Z iff v(K∩L) = 4Z)"]
theorem omeara106_5 {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : K.IsLattice ℚ) (hL : L.IsLattice ℚ)
    (hn : 0 < n) (hKu : IsUnimodularZ Q K) (hLu : IsUnimodularZ Q L) :
    (Nbr.IsNbrL Q 2 L K ↔
        OMeara.volume Q.toQuadraticForm (K ⊔ L) = Submodule.span (𝓞 ℚ) {(1 / 4 : ℚ)}) ∧
      (OMeara.volume Q.toQuadraticForm (K ⊔ L) = Submodule.span (𝓞 ℚ) {(1 / 4 : ℚ)} ↔
        OMeara.volume Q.toQuadraticForm (K ⊓ L) = Submodule.span (𝓞 ℚ) {(4 : ℚ)}) := by
  have hS := isLattice_sup hK hL
  have hI := isLattice_inf hK hL
  have hvK := volume_eq_one_of_unimodular Q hK hn hKu
  have hvL := volume_eq_one_of_unimodular Q hL hn hLu
  have hdual := omearaDual_sup Q hKu hLu
  have hreg : OMeara.IsRegular Q.toQuadraticForm (K ⊔ L) := by
    intro x hx hx0
    refine eq_zero_of_div_mem hS fun m => ?_
    have : (((m : ℚ) + 1)⁻¹) • x ∈ omearaDual Q (K ⊔ L) := by
      intro y hy
      refine ⟨0, ?_⟩
      have h0 := hx0 y hy
      rw [omeara_bil_eq] at h0
      rw [bil_smul_left']
      have : bil Q x y = 0 := by linarith
      rw [this]; simp
    rw [hdual] at this
    exact ((inf_le_left : K ⊓ L ≤ K).trans (le_sup_left : K ≤ K ⊔ L)) this
  have hvSI : OMeara.volume Q.toQuadraticForm (K ⊓ L) * OMeara.volume Q.toQuadraticForm (K ⊔ L) = 1 := by
    have := OMeara.volume_dual_mul Q.toQuadraticForm hS.fg hreg
    rwa [dual_eq_omearaDual Q hS, hdual] at this
  have h14 : Submodule.span (𝓞 ℚ) {(4 : ℚ)} * Submodule.span (𝓞 ℚ) {(1 / 4 : ℚ)} = 1 := by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, Submodule.one_eq_span]
    norm_num
  have key23 : OMeara.volume Q.toQuadraticForm (K ⊔ L) = Submodule.span (𝓞 ℚ) {(1 / 4 : ℚ)} ↔
      OMeara.volume Q.toQuadraticForm (K ⊓ L) = Submodule.span (𝓞 ℚ) {(4 : ℚ)} := by
    constructor
    · intro h
      calc OMeara.volume Q.toQuadraticForm (K ⊓ L)
          = OMeara.volume Q.toQuadraticForm (K ⊓ L) *
              (Submodule.span (𝓞 ℚ) {(4 : ℚ)} * Submodule.span (𝓞 ℚ) {(1 / 4 : ℚ)}) := by
            rw [h14, mul_one]
        _ = (OMeara.volume Q.toQuadraticForm (K ⊓ L) * OMeara.volume Q.toQuadraticForm (K ⊔ L)) *
              Submodule.span (𝓞 ℚ) {(4 : ℚ)} := by rw [h]; ring
        _ = Submodule.span (𝓞 ℚ) {(4 : ℚ)} := by rw [hvSI, one_mul]
    · intro h
      calc OMeara.volume Q.toQuadraticForm (K ⊔ L)
          = OMeara.volume Q.toQuadraticForm (K ⊔ L) *
              (Submodule.span (𝓞 ℚ) {(4 : ℚ)} * Submodule.span (𝓞 ℚ) {(1 / 4 : ℚ)}) := by
            rw [h14, mul_one]
        _ = (OMeara.volume Q.toQuadraticForm (K ⊓ L) * OMeara.volume Q.toQuadraticForm (K ⊔ L)) *
              Submodule.span (𝓞 ℚ) {(1 / 4 : ℚ)} := by rw [h]; ring
        _ = Submodule.span (𝓞 ℚ) {(1 / 4 : ℚ)} := by rw [hvSI, one_mul]
  -- the index formulas
  have hvIL : OMeara.volume Q.toQuadraticForm (K ⊓ L) = Submodule.span (𝓞 ℚ)
      {(((K ⊓ L).toAddSubgroup.relIndex L.toAddSubgroup : ℕ) : ℚ) ^ 2} := by
    rw [volume_eq_index_sq_mul Q hL hI inf_le_right, hvL, mul_one]
  have hvIK : OMeara.volume Q.toQuadraticForm (K ⊓ L) = Submodule.span (𝓞 ℚ)
      {(((K ⊓ L).toAddSubgroup.relIndex K.toAddSubgroup : ℕ) : ℚ) ^ 2} := by
    rw [volume_eq_index_sq_mul Q hK hI inf_le_left, hvK, mul_one]
  have key13 : Nbr.IsNbrL Q 2 L K ↔
      OMeara.volume Q.toQuadraticForm (K ⊓ L) = Submodule.span (𝓞 ℚ) {(4 : ℚ)} := by
    constructor
    · intro h
      rw [hvIL, inf_index_left Q h]
      norm_num
    · intro h
      have hL2 : (K ⊓ L).toAddSubgroup.relIndex L.toAddSubgroup = 2 :=
        nat_eq_two_of_span_sq _ (hvIL.symm.trans h)
      have hK2 : (K ⊓ L).toAddSubgroup.relIndex K.toAddSubgroup = 2 :=
        nat_eq_two_of_span_sq _ (hvIK.symm.trans h)
      have e : (K ⊓ L).toAddSubgroup = K.toAddSubgroup ⊓ L.toAddSubgroup := rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [nm_two', ← AddSubgroup.inf_relIndex_right, ← e, hL2]
      · rw [nm_two', ← AddSubgroup.inf_relIndex_left, ← e, hK2]
      · intro x hx
        exact (inf_le_right : K ⊓ L ≤ L) (two_smul_mem_of_index hK2 hx)
      · intro x hx
        exact (inf_le_left : K ⊓ L ≤ K) (two_smul_mem_of_index hL2 hx)
      · intro x hx
        obtain ⟨m, hm⟩ := uni_Q_int Q hLu hx
        exact ⟨Rat.ringOfIntegersEquiv.symm m, by rw [← Rat.ringOfIntegersEquiv_apply_coe]; simp [hm]⟩
      · intro x hx
        obtain ⟨m, hm⟩ := uni_Q_int Q hKu hx
        exact ⟨Rat.ringOfIntegersEquiv.symm m, by rw [← Rat.ringOfIntegersEquiv_apply_coe]; simp [hm]⟩
  exact ⟨key13.trans key23.symm, key23⟩

end Five

/-! ### 106.r22: a base adapted to two adjacent lattices -/

section Adapted

open Module

/-- The invariant factors of $K$ in $L$ over $\mathbb Z$, with the index type $\mathrm{Fin}\,n$ (O'Meara's 81:11
specialized to $F = \mathbb Q$, $V = \mathbb Q^n$). -/
theorem exists_basis_invFactors_fin {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ)
    (hK : K.IsLattice ℚ) :
    ∃ (x : Basis (Fin n) ℚ (Fin n → ℚ)) (a t : Fin n → Submodule (𝓞 ℚ) ℚ),
      (∀ i, (a i).FG ∧ a i ≠ ⊥) ∧ (∀ i, (t i).FG ∧ t i ≠ ⊥) ∧ Antitone t ∧
      L = ⨆ i, a i • Submodule.span (𝓞 ℚ) {x i} ∧
      K = ⨆ i, (a i * t i) • Submodule.span (𝓞 ℚ) {x i} := by
  obtain ⟨x, a, ha, ht, hanti, hLx, hKx⟩ := OMeara.exists_basis_invFactors (R := 𝓞 ℚ) (F := ℚ) hL hK
  have hm : Module.finrank ℚ (Fin n → ℚ) = n := Module.finrank_fin_fun ℚ
  let e : Fin n ≃ Fin (Module.finrank ℚ (Fin n → ℚ)) := (finCongr hm).symm
  refine ⟨x.reindex e.symm, fun i => a (e i), fun i => OMeara.invFactors hL hK (e i),
    fun i => ha _, fun i => ht _, ?_, ?_, ?_⟩
  · intro i j hij
    exact hanti (show e i ≤ e j from hij)
  · refine hLx.trans ?_
    simp only [Basis.reindex_apply, Equiv.symm_symm]
    exact (Equiv.iSup_comp (g := fun j => a j • Submodule.span (𝓞 ℚ) {x j}) e).symm
  · refine hKx.trans ?_
    simp only [Basis.reindex_apply, Equiv.symm_symm]
    exact (Equiv.iSup_comp (g := fun j => (a j * OMeara.invFactors hL hK j) •
      Submodule.span (𝓞 ℚ) {x j}) e).symm

/-- **Normal form of two lattices on $\mathbb Q^n$** (the Invariant Factor Theorem, O'Meara 1973, 81:11, over
$\mathbb Z$): there is a $\mathbb Q$-base $y$ of $V$ and non-zero rationals $\varphi_i$ with
$L = \sum_i\mathbb Zy_i$, $K = \sum_i\mathbb Z\varphi_iy_i$, and $\varphi_j \in \varphi_i\mathbb Z$ for $i \le j$. -/
theorem exists_adapted_basis_pid {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ)
    (hK : K.IsLattice ℚ) :
    ∃ (y : Basis (Fin n) ℚ (Fin n → ℚ)) (φ : Fin n → ℚ), (∀ i, φ i ≠ 0) ∧
      (∀ i j, i ≤ j → ∃ r : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ r * φ i = φ j) ∧
      L = Submodule.span (𝓞 ℚ) (Set.range y) ∧
      K = Submodule.span (𝓞 ℚ) (Set.range fun i => φ i • y i) := by
  have := pid_ringOfIntegers_rat
  obtain ⟨x, a, t, ha, ht, hanti, hLx, hKx⟩ := exists_basis_invFactors_fin hL hK
  choose α hα using fun i => OMeara.exists_eq_span_of_fg (a i) (ha i).1
  choose φ hφ using fun i => OMeara.exists_eq_span_of_fg (t i) (ht i).1
  have hα0 : ∀ i, α i ≠ 0 := fun i h => (ha i).2 (by rw [hα i, h]; simp)
  have hφ0 : ∀ i, φ i ≠ 0 := fun i h => (ht i).2 (by rw [hφ i, h]; simp)
  let y : Basis (Fin n) ℚ (Fin n → ℚ) := x.isUnitSMul (w := α) (fun i => isUnit_iff_ne_zero.mpr (hα0 i))
  have hy : ∀ i, y i = α i • x i := fun i => by simp only [y, Basis.isUnitSMul_apply]
  refine ⟨y, φ, hφ0, ?_, ?_, ?_⟩
  · intro i j hij
    have hmem : φ j ∈ t i := hanti hij (by rw [hφ j]; exact Submodule.mem_span_singleton_self _)
    rw [hφ i, Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    exact ⟨r, by rw [← hr, Algebra.smul_def]⟩
  · ext v
    rw [hLx, OMeara.mem_iSup_smul_span_iff_exists, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, hc, rfl⟩
      choose r hr using fun i => Submodule.mem_span_singleton.mp ((hα i) ▸ hc i)
      refine ⟨r, Finset.sum_congr rfl fun i _ => ?_⟩
      rw [hy, ← smul_assoc, hr i]
    · rintro ⟨r, rfl⟩
      refine ⟨fun i => r i • α i, fun i => ?_, Finset.sum_congr rfl fun i _ => ?_⟩
      · rw [hα i]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · rw [hy, ← smul_assoc]
  · ext v
    rw [hKx, OMeara.mem_iSup_smul_span_iff_exists, Submodule.mem_span_range_iff_exists_fun]
    have hat : ∀ i, a i * t i = Submodule.span (𝓞 ℚ) {α i * φ i} := fun i => by
      rw [hα i, hφ i, Submodule.span_mul_span, Set.singleton_mul_singleton]
    constructor
    · rintro ⟨c, hc, rfl⟩
      choose r hr using fun i => Submodule.mem_span_singleton.mp ((hat i) ▸ hc i)
      refine ⟨r, Finset.sum_congr rfl fun i _ => ?_⟩
      show r i • φ i • y i = c i • x i
      rw [hy i, smul_smul, ← smul_assoc, ← hr i, mul_comm (φ i)]
    · rintro ⟨r, rfl⟩
      refine ⟨fun i => r i • (α i * φ i), fun i => ?_, Finset.sum_congr rfl fun i _ => ?_⟩
      · rw [hat i]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · show r i • φ i • y i = (r i • (α i * φ i)) • x i
        rw [hy i, smul_smul, ← smul_assoc, mul_comm (φ i)]

/-- Membership in the lattice $\sum_i\mathbb Zu_iy_i$ in terms of the coordinates with respect to the base $y$. -/
theorem mem_span_range_smul_iff (y : Basis (Fin n) ℚ (Fin n → ℚ)) (u : Fin n → ℚ) (v : Fin n → ℚ) :
    v ∈ Submodule.span (𝓞 ℚ) (Set.range fun i => u i • y i) ↔
      ∀ i, ∃ r : 𝓞 ℚ, y.repr v i = algebraMap (𝓞 ℚ) ℚ r * u i := by
  have key : ∀ c : Fin n → 𝓞 ℚ, ∑ j, c j • (u j • y j) =
      ∑ j, (algebraMap (𝓞 ℚ) ℚ (c j) * u j) • y j := fun c => by
    refine Finset.sum_congr rfl fun j _ => ?_
    have : c j • u j = algebraMap (𝓞 ℚ) ℚ (c j) * u j := Algebra.smul_def _ _
    rw [← this, smul_assoc]
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    refine ⟨c i, ?_⟩
    rw [key, Basis.repr_sum_self]
  · intro h
    choose r hr using h
    refine ⟨r, ?_⟩
    rw [key]
    conv_rhs => rw [← y.sum_repr v]
    exact Finset.sum_congr rfl fun j _ => by rw [hr j]

/-- Scaling the vectors of a base by non-zero rationals keeps them independent. -/
theorem linIndep_smul (y : Basis (Fin n) ℚ (Fin n → ℚ)) (u : Fin n → ℚ) (hu : ∀ i, u i ≠ 0) :
    LinearIndependent ℚ (fun i => u i • y i) := by
  have := (y.isUnitSMul (w := u) (fun i => isUnit_iff_ne_zero.mpr (hu i))).linearIndependent
  convert this using 1
  funext i
  simp only [Basis.isUnitSMul_apply]

/-- The matrix of a scaled family: $\det(B(u_ix_i, u_jx_j)) = (\prod u_i)^2\det(B(x_i, x_j))$. -/
theorem gram_smul_det (u : Fin n → ℚ) (x : Fin n → Fin n → ℚ) :
    (OMeara.gram Q.toQuadraticForm fun i => u i • x i).det =
      (∏ i, u i) ^ 2 * (OMeara.gram Q.toQuadraticForm x).det := by
  have : OMeara.gram Q.toQuadraticForm (fun i => u i • x i) =
      Matrix.diagonal u * OMeara.gram Q.toQuadraticForm x * Matrix.diagonal u := by
    ext i j
    simp [OMeara.gram, Matrix.mul_apply, Matrix.diagonal_apply]
    ring
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring

theorem exists_int_iff (p c : ℚ) :
    (∃ r : 𝓞 ℚ, p = algebraMap (𝓞 ℚ) ℚ r * c) ↔ ∃ m : ℤ, p = m * c := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨Rat.ringOfIntegersEquiv r, by rw [Rat.ringOfIntegersEquiv_apply_coe]⟩
  · rintro ⟨m, rfl⟩
    exact ⟨Rat.ringOfIntegersEquiv.symm m, by rw [← Rat.ringOfIntegersEquiv_apply_coe]; simp⟩

/-- Coordinates in $\mathbb Z \cap \varphi\mathbb Z$ for $|\varphi| \in \{\tfrac12, 1, 2\}$. -/
theorem coord_inter (p : ℚ) {φ : ℚ} {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 4) (hφ : |φ| = (t : ℚ) / 2) :
    ((∃ m : ℤ, p = m * 1) ∧ ∃ m : ℤ, p = m * φ) ↔
      ∃ m : ℤ, p = m * (((if t = 4 then 2 else 1 : ℕ)) : ℚ) := by
  have hφ' : φ = (t : ℚ) / 2 ∨ φ = -((t : ℚ) / 2) := by
    rcases abs_eq (by positivity : (0 : ℚ) ≤ (t : ℚ) / 2) |>.mp hφ with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases ht with rfl | rfl | rfl
  · have e : (((if (1 : ℕ) = 4 then 2 else 1 : ℕ)) : ℚ) = 1 := by norm_num
    rw [e]
    constructor
    · rintro ⟨h, -⟩
      exact h
    · intro h
      refine ⟨h, ?_⟩
      obtain ⟨m, hm⟩ := h
      rcases hφ' with rfl | rfl
      · exact ⟨2 * m, by push_cast; rw [hm]; ring⟩
      · exact ⟨-(2 * m), by push_cast; rw [hm]; ring⟩
  · have e : (((if (2 : ℕ) = 4 then 2 else 1 : ℕ)) : ℚ) = 1 := by norm_num
    rw [e]
    constructor
    · rintro ⟨h, -⟩
      exact h
    · intro h
      refine ⟨h, ?_⟩
      obtain ⟨m, hm⟩ := h
      rcases hφ' with rfl | rfl
      · exact ⟨m, by push_cast; rw [hm]; ring⟩
      · exact ⟨-m, by push_cast; rw [hm]; ring⟩
  · have e : (((if (4 : ℕ) = 4 then 2 else 1 : ℕ)) : ℚ) = 2 := by norm_num
    rw [e]
    constructor
    · rintro ⟨-, m', hm'⟩
      rcases hφ' with rfl | rfl
      · exact ⟨m', by push_cast at hm'; rw [hm']; ring⟩
      · exact ⟨-m', by push_cast at hm' ⊢; rw [hm']; ring⟩
    · rintro ⟨m, hm⟩
      refine ⟨⟨2 * m, by push_cast; rw [hm]; ring⟩, ?_⟩
      rcases hφ' with rfl | rfl
      · exact ⟨m, by push_cast; rw [hm]; ring⟩
      · exact ⟨-m, by push_cast; rw [hm]; ring⟩

/-- The profile $(\tfrac12, 1, \dots, 1, 2)$: a chain of divisibilities $t_i \mid t_j$ ($i \le j$) among values
$1, 2, 4$ with exactly one value $4$ and product $2^n$ is $1, 2, \dots, 2, 4$. -/
theorem profile_of_chain (hn : 2 ≤ n) (t : Fin n → ℕ) (ht : ∀ i, t i = 1 ∨ t i = 2 ∨ t i = 4)
    (hdv : ∀ i j, i ≤ j → t i ∣ t j) (hC : (Finset.univ.filter fun i => t i = 4).card = 1)
    (hprod : ∏ i, t i = 2 ^ n) :
    ∀ i : Fin n, t i = if i.val = 0 then 1 else if i.val = n - 1 then 4 else 2 := by
  classical
  have hk : ∀ i, ∃ k : ℕ, t i = 2 ^ k ∧
      k + (if t i = 1 then 1 else 0) = 1 + (if t i = 4 then 1 else 0) := by
    intro i
    rcases ht i with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, by simp [h]⟩
  choose k hk1 hk2 using hk
  have hsum : ∑ i, k i = n := by
    have h1 : ∏ i, t i = 2 ^ (∑ i, k i) := by
      rw [Finset.prod_congr rfl fun i _ => hk1 i]
      exact Finset.prod_pow_eq_pow_sum _ _ _
    exact Nat.pow_right_injective (le_refl 2) (h1.symm.trans hprod)
  have hA : (Finset.univ.filter fun i => t i = 1).card = 1 := by
    have h1 : ∑ i, (k i + (if t i = 1 then 1 else 0)) = ∑ i, (1 + (if t i = 4 then 1 else 0)) :=
      Finset.sum_congr rfl fun i _ => hk2 i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum] at h1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
    rw [← Finset.card_filter, ← Finset.card_filter] at h1
    omega
  obtain ⟨i₁, h1⟩ := Finset.card_eq_one.mp hA
  obtain ⟨i₄, h4⟩ := Finset.card_eq_one.mp hC
  have e1 : ∀ j, t j = 1 ↔ j = i₁ := fun j => by
    have := Finset.ext_iff.mp h1 j
    simpa using this
  have e4 : ∀ j, t j = 4 ↔ j = i₄ := fun j => by
    have := Finset.ext_iff.mp h4 j
    simpa using this
  have hi₁ : i₁.val = 0 := by
    by_contra hne
    have hle : (⟨0, by omega⟩ : Fin n) ≤ i₁ := Fin.le_def.mpr (Nat.zero_le _)
    have hd := hdv _ _ hle
    rw [(e1 i₁).mpr rfl] at hd
    have h0 : t ⟨0, by omega⟩ = 1 := Nat.dvd_one.mp hd
    have : (⟨0, by omega⟩ : Fin n) = i₁ := (e1 _).mp h0
    exact hne (by rw [← this])
  have hi₄ : i₄.val = n - 1 := by
    by_contra hne
    have hle : i₄ ≤ (⟨n - 1, by omega⟩ : Fin n) := Fin.le_def.mpr (by have := i₄.isLt; simp; omega)
    have hd := hdv _ _ hle
    rw [(e4 i₄).mpr rfl] at hd
    have hlast : t ⟨n - 1, by omega⟩ = 4 := by
      rcases ht ⟨n - 1, by omega⟩ with h | h | h <;> rw [h] at hd <;> omega
    have : (⟨n - 1, by omega⟩ : Fin n) = i₄ := (e4 _).mp hlast
    exact hne (by rw [← this])
  intro i
  split_ifs with h0 hl
  · have : i = i₁ := Fin.ext (h0.trans hi₁.symm)
    exact (e1 i).mpr this
  · have : i = i₄ := Fin.ext (hl.trans hi₄.symm)
    exact (e4 i).mpr this
  · rcases ht i with h | h | h
    · exfalso
      exact h0 (by have := (e1 i).mp h; rw [this]; exact hi₁)
    · exact h
    · exfalso
      exact hl (by have := (e4 i).mp h; rw [this]; exact hi₄)

theorem span_mul_of_unit {G : ℚ} (hG : Submodule.span (𝓞 ℚ) {G} = 1) (c : ℚ) :
    Submodule.span (𝓞 ℚ) {c * G} = Submodule.span (𝓞 ℚ) {c} := by
  rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, hG, mul_one]

theorem sq_eq_one_of_span_eq_one (c : ℚ) (h : Submodule.span (𝓞 ℚ) {c ^ 2} = 1) : c ^ 2 = 1 := by
  have h1 : c ^ 2 ∈ (1 : Submodule (𝓞 ℚ) ℚ) := h ▸ Submodule.mem_span_singleton_self _
  have h2 : (1 : ℚ) ∈ Submodule.span (𝓞 ℚ) {c ^ 2} := h ▸ (Submodule.one_le.1 le_rfl)
  obtain ⟨m, hm⟩ := (mem_one_iff_int _).mp h1
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h2
  rw [Algebra.smul_def, ← Rat.ringOfIntegersEquiv_apply_coe] at ha
  set k := Rat.ringOfIntegersEquiv a
  have e : (k : ℚ) * m = 1 := by rw [← hm]; exact ha
  have e' : k * m = 1 := by exact_mod_cast e
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' e' with ⟨-, hm1⟩ | ⟨-, hm1⟩
  · rw [hm, hm1]; simp
  · exfalso
    rw [hm1] at hm
    push_cast at hm
    nlinarith [sq_nonneg c]

/-- **106.r22 (reconstructed): a base adapted to two adjacent lattices** (O'Meara 1973, §106B, p. 326: "there is a
base $x_1, \dots, x_n$ for $V$ in which $L = \mathbb Zx_1 + \dots + \mathbb Zx_n$ and $K = \mathbb Z(\tfrac12x_1) +
\mathbb Zx_2 + \dots + \mathbb Zx_{n-1} + \mathbb Z(2x_n)$"; this part of the scan is partly illegible and the statement
is reconstructed from the definition of adjacency by the invariant factors $\tfrac12\mathbb Z, \mathbb Z, \dots,
\mathbb Z, 2\mathbb Z$). Let $K$ and $L$ be unimodular lattices on $V = \mathbb Q^n$, $n \ge 2$, $K$ adjacent to $L$
(`Nbr.IsNbrL Q 2 L K`). Then there is a $\mathbb Q$-base $x_0, \dots, x_{n-1}$ of $V$ (indices shifted by one) with
$L = \sum_i \mathbb Zx_i$ and $K = \mathbb Z(\tfrac12x_0) + \mathbb Zx_1 + \dots + \mathbb Zx_{n-2} + \mathbb Z(2x_{n-1})$.
Proof: the Invariant Factor Theorem (`exists_adapted_basis_pid`) gives a base with $K = \sum\mathbb Z\varphi_ix_i$,
and $2L \subseteq K$, $2K \subseteq L$, $\mathfrak vK = \mathfrak vL$ and $\mathfrak v(K \cap L) = 4\mathbb Z$
(`omeara106_5`) force $|\varphi_i| \in \{\tfrac12, 1, 2\}$ with the profile $(\tfrac12, 1, \dots, 1, 2)$. -/
@[kb "omeara1963" "§106B, p. 326 (reconstructed: base with L = ΣZxᵢ, K = Z(x₁/2) + Zx₂ + ⋯ + Z(2xₙ))"]
theorem omeara106_r22 {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : K.IsLattice ℚ) (hL : L.IsLattice ℚ)
    (hn : 2 ≤ n) (hKu : IsUnimodularZ Q K) (hLu : IsUnimodularZ Q L) (hadj : Nbr.IsNbrL Q 2 L K) :
    ∃ x : Fin n → Fin n → ℚ, LinearIndependent ℚ x ∧ Submodule.span ℚ (Set.range x) = ⊤ ∧
      L = Submodule.span (𝓞 ℚ) (Set.range x) ∧
      K = Submodule.span (𝓞 ℚ) (Set.range fun i : Fin n =>
        (if i.val = 0 then (1 / 2 : ℚ) else if i.val = n - 1 then 2 else 1) • x i) := by
  have hn0 : 0 < n := by omega
  have hvI : OMeara.volume Q.toQuadraticForm (K ⊓ L) = Submodule.span (𝓞 ℚ) {(4 : ℚ)} :=
    (omeara106_5 Q hK hL hn0 hKu hLu).2.mp ((omeara106_5 Q hK hL hn0 hKu hLu).1.mp hadj)
  have hvL := volume_eq_one_of_unimodular Q hL hn0 hLu
  have hvK := volume_eq_one_of_unimodular Q hK hn0 hKu
  obtain ⟨y, φ, hφ0, hdiv, hLy, hKy⟩ := exists_adapted_basis_pid hL hK
  have h2L : ∀ v ∈ L, (2 : ℚ) • v ∈ K := fun v hv => by
    have := hadj.smul_right v hv
    rwa [map_ofNat] at this
  have h2K : ∀ v ∈ K, (2 : ℚ) • v ∈ L := fun v hv => by
    have := hadj.smul_left v hv
    rwa [map_ofNat] at this
  have hYL : ∀ i, y i ∈ L := fun i => by rw [hLy]; exact Submodule.subset_span ⟨i, rfl⟩
  have hYK : ∀ i, φ i • y i ∈ K := fun i => by rw [hKy]; exact Submodule.subset_span ⟨i, rfl⟩
  have hLy1 : L = Submodule.span (𝓞 ℚ) (Set.range fun i => (fun _ : Fin n => (1 : ℚ)) i • y i) := by
    rw [hLy]; simp
  have hCL : ∀ v, v ∈ L ↔ ∀ i, ∃ r : 𝓞 ℚ, y.repr v i = algebraMap (𝓞 ℚ) ℚ r * 1 := fun v => by
    rw [hLy1]; exact mem_span_range_smul_iff y (fun _ => 1) v
  have hCK : ∀ v, v ∈ K ↔ ∀ i, ∃ r : 𝓞 ℚ, y.repr v i = algebraMap (𝓞 ℚ) ℚ r * φ i := fun v => by
    rw [hKy]; exact mem_span_range_smul_iff y φ v
  -- integer data
  have hint : ∀ i, ∃ z ρ : ℤ, (z : ℚ) = 2 * φ i ∧ (ρ : ℚ) * φ i = 2 := by
    intro i
    obtain ⟨r, hr⟩ := (hCK _).mp (h2L _ (hYL i)) i
    obtain ⟨s, hs⟩ := (hCL _).mp (h2K _ (hYK i)) i
    refine ⟨Rat.ringOfIntegersEquiv s, Rat.ringOfIntegersEquiv r, ?_, ?_⟩
    · rw [Rat.ringOfIntegersEquiv_apply_coe, ← mul_one (algebraMap (𝓞 ℚ) ℚ s), ← hs]
      simp
    · rw [Rat.ringOfIntegersEquiv_apply_coe, ← hr]
      simp
  have htdata : ∃ t : Fin n → ℕ, (∀ i, t i = 1 ∨ t i = 2 ∨ t i = 4) ∧ ∀ i, |φ i| = (t i : ℚ) / 2 := by
    choose z ρ hz hρ using hint
    refine ⟨fun i => (z i).natAbs, fun i => ?_, fun i => ?_⟩
    · have hzρ : z i * ρ i = 4 := by
        have : ((z i : ℤ) : ℚ) * (ρ i : ℚ) = 4 := by rw [hz i]; linear_combination 2 * hρ i
        exact_mod_cast this
      have hdvd : (z i).natAbs ∣ 4 := by
        have : (z i) ∣ 4 := ⟨ρ i, hzρ.symm⟩
        exact_mod_cast Int.natAbs_dvd_natAbs.mpr this
      have hle : (z i).natAbs ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < (z i).natAbs := by
        rw [Int.natAbs_pos]
        intro h0
        exact hφ0 i (by have := hz i; rw [h0] at this; push_cast at this; linarith)
      have : (z i).natAbs = 1 ∨ (z i).natAbs = 2 ∨ (z i).natAbs = 3 ∨ (z i).natAbs = 4 := by omega
      rcases this with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · rw [h] at hdvd; omega
      · exact Or.inr (Or.inr h)
    · have h1 : (((z i).natAbs : ℕ) : ℚ) = |((z i : ℤ) : ℚ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      show |φ i| = (((z i).natAbs : ℕ) : ℚ) / 2
      rw [h1, hz i, abs_mul]
      norm_num
  obtain ⟨t, ht, htφ⟩ := htdata
  have hdv : ∀ i j, i ≤ j → t i ∣ t j := by
    intro i j hij
    obtain ⟨r, hr⟩ := hdiv i j hij
    have h1 : (t j : ℚ) = ((Rat.ringOfIntegersEquiv r).natAbs : ℚ) * t i := by
      have e1 := htφ j
      rw [← hr, abs_mul, htφ i, ← Rat.ringOfIntegersEquiv_apply_coe] at e1
      have e2 : (((Rat.ringOfIntegersEquiv r).natAbs : ℕ) : ℚ) =
          |((Rat.ringOfIntegersEquiv r : ℤ) : ℚ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [e2]
      linarith
    have h2 : t j = (Rat.ringOfIntegersEquiv r).natAbs * t i := by exact_mod_cast h1
    exact Dvd.intro_left _ h2.symm
  -- volumes
  have hGL : Submodule.span (𝓞 ℚ) {(OMeara.gram Q.toQuadraticForm ⇑y).det} = 1 := by
    rw [← volume_famLat Q y.linearIndependent, ← hLy, hvL]
  have hd0 : ∀ i, ((if t i = 4 then 2 else 1 : ℕ) : ℚ) ≠ 0 := fun i => by
    split_ifs <;> norm_num
  have hI : K ⊓ L = Submodule.span (𝓞 ℚ) (Set.range fun i => ((if t i = 4 then 2 else 1 : ℕ) : ℚ) • y i) := by
    ext v
    rw [Submodule.mem_inf, and_comm, hCL, hCK,
      mem_span_range_smul_iff y (fun i => ((if t i = 4 then 2 else 1 : ℕ) : ℚ)) v, ← forall_and]
    refine forall_congr' fun i => ?_
    rw [exists_int_iff, exists_int_iff, exists_int_iff]
    exact coord_inter _ (ht i) (htφ i)
  have hvI' : Submodule.span (𝓞 ℚ) {(∏ i, ((if t i = 4 then 2 else 1 : ℕ) : ℚ)) ^ 2} =
      Submodule.span (𝓞 ℚ) {(4 : ℚ)} := by
    have := hvI
    rw [hI, volume_famLat Q (linIndep_smul y _ hd0), gram_smul_det, span_mul_of_unit hGL] at this
    exact this
  have hprodd : ∏ i, (if t i = 4 then 2 else 1 : ℕ) = 2 := by
    apply nat_eq_two_of_span_sq
    rw [Nat.cast_prod]
    exact hvI'
  have hC : (Finset.univ.filter fun i => t i = 4).card = 1 := by
    have h1 : ∏ i, (if t i = 4 then 2 else 1 : ℕ) = 2 ^ (Finset.univ.filter fun i => t i = 4).card := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [h1] at hprodd
    exact Nat.pow_right_injective (le_refl 2) (by simpa using hprodd)
  have hφsq : (∏ i, φ i) ^ 2 = 1 := by
    have := hvK
    rw [hKy, volume_famLat Q (linIndep_smul y φ hφ0), gram_smul_det, span_mul_of_unit hGL] at this
    exact sq_eq_one_of_span_eq_one _ this
  have hprodt : ∏ i, t i = 2 ^ n := by
    have h1 : |∏ i, φ i| = 1 :=
      (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).mp (by rw [sq_abs]; exact hφsq)
    have h2 : ∏ i, ((t i : ℚ) / 2) = 1 := by
      rw [← h1, Finset.abs_prod]
      exact Finset.prod_congr rfl fun i _ => (htφ i).symm
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    have h3 : (∏ i, (t i : ℚ)) = 2 ^ n := by
      have h2' : (2 : ℚ) ^ n ≠ 0 := by positivity
      field_simp at h2
      linarith
    exact_mod_cast h3
  have hprof := profile_of_chain hn t ht hdv hC hprodt
  have hcφ : ∀ i : Fin n, |φ i| =
      (if i.val = 0 then (1 / 2 : ℚ) else if i.val = n - 1 then 2 else 1) := by
    intro i
    rw [htφ i, hprof i]
    split_ifs <;> norm_num
  refine ⟨y, y.linearIndependent, y.span_eq, hLy, ?_⟩
  rw [hKy]
  ext v
  rw [mem_span_range_smul_iff y φ v,
    mem_span_range_smul_iff y (fun i : Fin n => (if i.val = 0 then (1 / 2 : ℚ) else
      if i.val = n - 1 then 2 else 1)) v]
  refine forall_congr' fun i => ?_
  have hc0 : (0 : ℚ) ≤ (if i.val = 0 then (1 / 2 : ℚ) else if i.val = n - 1 then 2 else 1) := by
    split_ifs <;> norm_num
  rcases (abs_eq hc0).mp (hcφ i) with h | h
  · rw [h]
  · rw [h]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨-r, by rw [hr, map_neg]; ring⟩
    · rintro ⟨r, hr⟩
      exact ⟨-r, by rw [hr, map_neg]; ring⟩

end Adapted

end QuadFormsKB.Lattices
