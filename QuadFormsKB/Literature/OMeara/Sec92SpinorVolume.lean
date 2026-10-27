/-
# O'Meara §92: spinor norms from the volume (Example 92:9)

**Setting** (as in `Sec92Spinor.lean`): $R$ a complete discrete valuation ring with finite residue field, $2$ a unit of
$R$ (non-dyadic), prime element $\pi$, fraction field $F$, a finite-dimensional regular quadratic space $(V, Q)$ over
$F$ of dimension $n$, lattices = `Submodule R V`; $\mathfrak p^k = (\pi^k)$ is `(R ∙ algebraMap R F π) ^ k`.

**Proves** `exists_hasSpinorNorm_of_volume` (**92:9**, p. 250): if $L$ is a lattice on $V$ with $\mathfrak sL \subseteq
\mathfrak o$ and $\mathfrak vL \supsetneq \mathfrak p^{n(n-1)/2}$, then $\theta(O^+(L)) \supseteq \mathfrak u$: every unit
is the spinor norm of a rotation in $O^+(L)$.
-/
import QuadFormsKB.Literature.OMeara.Sec92Spinor
import QuadFormsKB.Literature.OMeara.Sec91Chain

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section LocalNonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- $(R x)^k = R x^k$ for submodules of $F$. -/
theorem span_singleton_pow_eq (x : F) (k : ℕ) :
    (R ∙ x) ^ k = R ∙ (x ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Submodule.one_eq_span]
  | succ k ih => rw [pow_succ, ih, span_mul_span, Set.singleton_mul_singleton, pow_succ]

/-- A proper sub-principal-ideal of $\mathfrak p^j$ lies in $\mathfrak p^{j+1}$. -/
theorem le_pow_succ_of_lt_pow {π : R} (hπ : Irreducible π) {a : Submodule R F} {α : F}
    (ha : a = R ∙ α) (j : ℕ) (h : a < (R ∙ algebraMap R F π) ^ j) :
    a ≤ (R ∙ algebraMap R F π) ^ (j + 1) := by
  rw [span_singleton_pow_eq] at h ⊢
  have hα : α ∈ R ∙ (algebraMap R F π) ^ j := h.le (ha ▸ mem_span_singleton_self α)
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hα
  have hnu : ¬ IsUnit c := by
    intro hu
    apply h.not_ge
    rw [span_singleton_le_iff_mem, ha, mem_span_singleton]
    obtain ⟨w, hw⟩ := hu
    refine ⟨(↑w⁻¹ : R), ?_⟩
    rw [← hc, ← hw, ← mul_smul, Units.inv_mul, one_smul]
  have hcm : c ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal]; exact hnu
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hcm
  obtain ⟨d, rfl⟩ := hcm
  rw [ha, span_singleton_le_iff_mem, mem_span_singleton]
  refine ⟨d, ?_⟩
  rw [← hc, Algebra.smul_def, Algebra.smul_def, map_mul, pow_succ]
  ring

/-- The volume of the zero lattice is contained in $\mathfrak o$. -/
theorem volume_bot_le_one :
    volume Q (⊥ : Submodule R V) ≤ 1 := by
  refine span_le.mpr ?_
  rintro d ⟨x, hx, rfl⟩
  have hx0 : x = 0 := funext fun i => by simpa using hx i
  subst hx0
  have hg : gram Q (0 : Fin (finrank R (⊥ : Submodule R V)) → V) = 0 := by
    ext i j; simp [gram, bil]
  rw [hg]
  generalize finrank R (⊥ : Submodule R V) = k
  rcases k with _ | k
  · simp
  · simp

/-- **Example 92:9** (O'Meara 1963, p. 250): let $L$ be a lattice on a regular $n$-ary quadratic space over a non-dyadic
local field with $\mathfrak sL \subseteq \mathfrak o$ and $\mathfrak vL \supsetneq \mathfrak p^{n(n-1)/2}$. Then
$\theta(O^+(L)) \supseteq \mathfrak u$. *Proof:* a Jordan splitting of $L$ has fewer than $n$ components, since $n$
components of rank $1$ with scales $\mathfrak sL_1 \supsetneq \cdots \supsetneq \mathfrak sL_n$ inside $\mathfrak o$ would
give $\mathfrak vL \subseteq \mathfrak p^{0 + 1 + \cdots + (n-1)}$; so some component has rank $\ge 2$, and 92:5 applies to
it. (O'Meara's "$\supset$" is strict inclusion, as the proof requires.) -/
@[kb "omeara1963" "§92, 92:9, p. 250"]
theorem exists_hasSpinorNorm_of_volume (h2 : IsUnit (2 : R)) [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) {π : R} (hπ : Irreducible π) {L : Submodule R V}
    (hL : L.IsLattice F) (hs : scale Q L ≤ 1)
    (hv : (R ∙ algebraMap R F π) ^ (finrank F V * (finrank F V - 1) / 2) < volume Q L) {ε : R}
    (hε : IsUnit ε) : ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ (algebraMap R F ε) := by
  classical
  have hfg := hL.fg
  have hreg : IsRegular Q L := by
    intro x _ hx
    have hBV : ∀ y : V, bil Q x y = 0 := by
      intro y
      have hy : y ∈ span F (L : Set V) := hL.span_eq_top ▸ mem_top
      refine span_induction (p := fun y _ => bil Q x y = 0) ?_ (by simp [bil]) ?_ ?_ hy
      · intro y hy; exact hx y hy
      · intro a b _ _ ha hb; rw [bil_add_right, ha, hb, add_zero]
      · intro c a _ ha; rw [bil_smul_right, ha, mul_zero]
    exact hV.1 x hBV
  have hrank : finrank R L = finrank F V :=
    Module.finrank_eq_of_rank_eq
      ((Submodule.IsLattice.rank' F L).trans (Module.finrank_eq_rank F V).symm)
  by_cases hbot : L = ⊥
  · exfalso
    have hn : finrank F V = 0 := by rw [← hrank, hbot]; simp
    have h1 : volume Q L ≤ 1 := by rw [hbot]; exact volume_bot_le_one Q
    rw [hn] at hv
    simp only [Nat.zero_mul, Nat.zero_div, pow_zero] at hv
    exact absurd (hv.trans_le h1) (lt_irrefl _)
  obtain ⟨t, Ls, hJ⟩ := exists_isJordanSplitting Q hfg hreg hbot
  have hle : ∀ k, Ls k ≤ L := fun k => hJ.split.iSup_eq ▸ le_iSup Ls k
  have hLsfg : ∀ k, (Ls k).FG := fun k => FG.of_le hfg (hle k)
  by_cases hbig : ∃ i, 2 ≤ finrank R (Ls i)
  · obtain ⟨i, hi⟩ := hbig
    have hs : IsOrthSum Q L (Ls i) (⨆ (j) (_ : j ≠ i), Ls j) := by
      refine ⟨fun x hx y hy => ?_, hJ.split.indep i, ?_⟩
      · rw [bil_comm Q x y]
        exact bil_eq_zero_of_mem_iSup Q (P := fun j => j ≠ i)
          (fun j hj y' hy' => hJ.split.orth j i hj y' hy' x hx) hy
      · rw [← iSup_split_single Ls i]; exact hJ.split.iSup_eq
    obtain ⟨α, hα, hαeq⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (hLsfg i)) (hJ.modular i).1
    have hmod : IsModular Q (R ∙ α) (Ls i) := by rw [← hαeq]; exact hJ.modular i
    exact exists_hasSpinorNorm_of_component Q h2 hs hα (hLsfg i) hmod hi hε
  · exfalso
    push Not at hbig
    have hrk1 : ∀ i, finrank R (Ls i) = 1 := by
      intro i
      by_contra hne
      have h0 : finrank R (Ls i) = 0 := by have := hbig i; omega
      have : Module.Finite R (Ls i) := Module.Finite.iff_fg.mpr (hLsfg i)
      have : Module.IsTorsionFree R V := Module.IsTorsionFree.trans_faithfulSMul R F V
      have hb : Ls i = ⊥ := (Submodule.finrank_eq_zero).mp h0
      exact (hJ.modular i).1 (by rw [← (hJ.modular i).2.1, hb, scale_bot])
    cases t with
    | zero =>
      apply hbot
      rw [← hJ.split.iSup_eq]
      simp
    | succ s =>
    have hchfg : ∀ i, (jordanChain Ls i).FG := fun i => FG.of_le hfg (iSup₂_le fun k _ => hle k)
    have hchrank : ∀ k (i : Fin (s + 1)), i.val = k → finrank R (jordanChain Ls i) = k + 1 := by
      intro k
      induction k with
      | zero =>
        intro i hi
        rw [jordanChain_zero Ls i hi]; exact hrk1 i
      | succ k ih =>
        intro i hi
        have hk : k < s + 1 := by omega
        have h1 := isOrthSum_jordanChain_succ Q hfg hJ ⟨k, hk⟩ i (by simp [hi])
        rw [isOrthSum_finrank Q h1 (hchfg i), ih ⟨k, hk⟩ rfl, hrk1]
    have hn : finrank F V = s + 1 := by
      rw [← hrank, ← jordanChain_last Q hJ.split]
      exact hchrank s (Fin.last s) rfl
    have hscale : ∀ k (i : Fin (s + 1)), i.val = k →
        scale Q (Ls i) ≤ (R ∙ algebraMap R F π) ^ k := by
      intro k
      induction k with
      | zero =>
        intro i hi
        rw [pow_zero]
        exact (scale_mono Q (hle i)).trans hs
      | succ k ih =>
        intro i hi
        have hk : k < s + 1 := by omega
        have hlt : scale Q (Ls i) < scale Q (Ls ⟨k, hk⟩) :=
          hJ.scale_strictAnti (show (⟨k, hk⟩ : Fin (s + 1)) < i by rw [Fin.lt_def]; simp [hi])
        obtain ⟨α, -, hαeq⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (hLsfg i)) (hJ.modular i).1
        exact le_pow_succ_of_lt_pow hπ hαeq k (hlt.trans_le (ih ⟨k, hk⟩ rfl))
    have hvolLs : ∀ i : Fin (s + 1), volume Q (Ls i) ≤ (R ∙ algebraMap R F π) ^ i.val := by
      intro i
      rw [(hJ.modular i).2.2, hrk1, pow_one]
      exact hscale _ i rfl
    have hvol : ∀ k (i : Fin (s + 1)), i.val = k →
        volume Q (jordanChain Ls i) ≤ (R ∙ algebraMap R F π) ^ (k * (k + 1) / 2) := by
      intro k
      induction k with
      | zero =>
        intro i hi
        rw [jordanChain_zero Ls i hi]
        simpa [hi] using hvolLs i
      | succ k ih =>
        intro i hi
        have hk : k < s + 1 := by omega
        have h1 := isOrthSum_jordanChain_succ Q hfg hJ ⟨k, hk⟩ i (by simp [hi])
        rw [volume_eq_mul_of_isOrthSum Q h1 (hchfg _) (hLsfg i)]
        have hexp : (k + 1) * (k + 1 + 1) / 2 = k * (k + 1) / 2 + (k + 1) := by
          have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
          rw [this, Nat.add_mul_div_left _ _ (by norm_num)]
        rw [hexp, pow_add]
        refine mul_le_mul' (ih ⟨k, hk⟩ rfl) ?_
        have := hvolLs i
        rwa [hi] at this
    have hfin := hvol s (Fin.last s) rfl
    rw [jordanChain_last Q hJ.split] at hfin
    rw [hn] at hv
    have e : (s + 1) * (s + 1 - 1) / 2 = s * (s + 1) / 2 := by
      rw [Nat.add_sub_cancel, Nat.mul_comm]
    rw [e] at hv
    exact absurd (hv.trans_le hfin) (lt_irrefl _)

end LocalNonDyadic

end QuadFormsKB.OMeara
