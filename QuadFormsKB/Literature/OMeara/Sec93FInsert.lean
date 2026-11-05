/-
# O'Meara 93:28, sufficiency, step 8: inserting a new Jordan component

**Setting** (as in `Sec93FAdjoin.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$;
$(V, Q)$ and $(W, Q_W)$ quadratic spaces over $F$, lattices `Submodule R V`, `Submodule R W`; the orthogonal sum
$L \perp J$ is the lattice `L.prod J` in $V \times W$ with the form `Q.prod QW`. **Indices are $0$-based**: O'Meara's
$L_1, L_2, \dots$ are `Ls 0, Ls 1, …`, and his inserted component $L_{1\frac12} = J$ is at index `1`.

O'Meara's step 8 (p. 276) adjoins $J \cong \langle\pi A(0,0)\rangle$ to $L$ and $K$: with Jordan splittings
$L = L_1 \perp \cdots \perp L_t$ and $\mathfrak s_1 \supsetneq \mathfrak p = \mathfrak sJ \supsetneq \mathfrak s_2$,
$$L \perp J = L_1 \perp L_{1\frac12} \perp L_2 \perp \cdots \perp L_t, \qquad L_{1\frac12} = J,$$
is a Jordan splitting with one more component.

**Defines**
* `insLs Ls J`: the splitting $L_1 \perp J \perp L_2 \perp \cdots \perp L_t$ of $L \perp J$ (`Fin (m + 3)`-indexed);
* `insA a c`: the fundamental norm generators $a_1, c, a_2, \dots, a_t$ (O'Meara takes $c = \pi^2a_1$).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8, p. 276)
* `isJordanSplitting_insLs`: `insLs Ls J` is a Jordan splitting when $J$ is modular with scale strictly between
  $\mathfrak s_1$ and $\mathfrak s_2$;
* `jordanChain_insLs_*`: the Jordan chains $L'_{(1)} = L_{(1)} \perp 0$, $L'_{(1\frac12)} = L_{(1)} \perp J$,
  $L'_{(i)} = L_{(i)} \perp J$ ($i \ge 2$).
-/
import QuadFormsKB.Literature.OMeara.Sec93FCoreStep8

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Insert

open Sat93 Transfer28 Adjoin28 SuffMain SuffStep NecMerge FIdealAux Suff28

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
variable (Q : QuadraticForm F V) (QW : QuadraticForm F W)

section Split

/-- **The splitting with an inserted component** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8, p. 276):
for `Ls : Fin (m + 2) → Submodule R V` (O'Meara's $L_1, \dots, L_t$, $t = m + 2$) and $J \subseteq W$, the family
$L_1 \perp 0,\ 0 \perp J,\ L_2 \perp 0,\ \dots,\ L_t \perp 0$ of sublattices of $V \times W$ (O'Meara's
$L_1, L_{1\frac12}, L_2, \dots, L_t$). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (the splitting L ⊥ J = L_1 ⊥ L_{1½} ⊥ L_2 ⊥ ⋯)"]
def insLs {m : ℕ} (Ls : Fin (m + 2) → Submodule R V) (J : Submodule R W) : Fin (m + 3) → Submodule R (V × W) :=
  Fin.cons ((Ls 0).prod ⊥) (Fin.cons ((⊥ : Submodule R V).prod J) fun k : Fin (m + 1) => (Ls k.succ).prod ⊥)

/-- **The inserted fundamental norm generators** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8, p. 276):
$a_1, c, a_2, \dots, a_t$ for `a : Fin (m + 2) → F` (O'Meara's $a'_{1\frac12} = c = \pi^2 a_1$). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (a'_{1½} = π²a_1)"]
def insA {m : ℕ} (a : Fin (m + 2) → F) (c : F) : Fin (m + 3) → F :=
  Fin.cons (a 0) (Fin.cons c fun k : Fin (m + 1) => a k.succ)

variable {m : ℕ} (Ls : Fin (m + 2) → Submodule R V) (J : Submodule R W)

@[simp] theorem insLs_zero : insLs Ls J 0 = (Ls 0).prod ⊥ := rfl

@[simp] theorem insLs_one : insLs Ls J 1 = (⊥ : Submodule R V).prod J := rfl

@[simp] theorem insLs_succ_succ (k : Fin (m + 1)) : insLs Ls J k.succ.succ = (Ls k.succ).prod ⊥ := rfl

@[simp] theorem insA_zero (a : Fin (m + 2) → F) (c : F) : insA a c 0 = a 0 := rfl

@[simp] theorem insA_one (a : Fin (m + 2) → F) (c : F) : insA a c 1 = c := rfl

@[simp] theorem insA_succ_succ (a : Fin (m + 2) → F) (c : F) (k : Fin (m + 1)) :
    insA a c k.succ.succ = a k.succ := rfl

/-- The index map $0 \mapsto 0$, $1 \mapsto 0$, $k + 2 \mapsto k + 1$: away from the inserted index `1`,
`insLs Ls J k = (Ls (insIdx k)).prod ⊥`. -/
def insIdx : Fin (m + 3) → Fin (m + 2) := Fin.cons 0 (Fin.cons 0 fun k : Fin (m + 1) => k.succ)

theorem insLs_of_ne_one {k : Fin (m + 3)} (hk : k ≠ 1) : insLs Ls J k = (Ls (insIdx k)).prod ⊥ := by
  induction k using Fin.cases with
  | zero => rfl
  | succ k =>
    induction k using Fin.cases with
    | zero => exact absurd rfl hk
    | succ k => rfl

theorem insIdx_inj {i j : Fin (m + 3)} (hi : i ≠ 1) (hj : j ≠ 1) (h : insIdx i = insIdx j) : i = j := by
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hj
      | succ j => exact absurd h.symm (Fin.succ_ne_zero j)
  | succ i =>
    induction i using Fin.cases with
    | zero => exact absurd rfl hi
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (Fin.succ_ne_zero i)
      | succ j =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hj
        | succ j =>
          have : i.succ = j.succ := h
          rw [Fin.succ_inj.1 this]

/-- The scales of `insLs Ls J`: $\mathfrak s_1,\ \mathfrak sJ,\ \mathfrak s_2, \dots, \mathfrak s_t$. -/
theorem scale_insLs (k : Fin (m + 3)) :
    scale (Q.prod QW) (insLs Ls J k) =
      (Fin.cons (scale Q (Ls 0)) (Fin.cons (scale QW J) fun k : Fin (m + 1) => scale Q (Ls k.succ)) :
        Fin (m + 3) → Submodule R F) k := by
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · simp [scale_prod, scale_bot]
  · simp [scale_prod, scale_bot]
  · simp [scale_prod, scale_bot]

theorem iSup_insLs : ⨆ k, insLs Ls J k = (⨆ k, Ls k).prod J := by
  have hL : (⨆ k, Ls k) = Ls 0 ⊔ ⨆ k : Fin (m + 1), Ls k.succ := by
    rw [← iSup_fin_cons]; exact iSup_congr fun k => by
      induction k using Fin.cases with
      | zero => rfl
      | succ k => rfl
  rw [insLs, iSup_fin_cons, iSup_fin_cons, Adjoin28.iSup_prod, iSup_const, hL,
    show (Ls 0 ⊔ ⨆ k : Fin (m + 1), Ls k.succ).prod J =
      (Ls 0).prod ⊥ ⊔ ((⊥ : Submodule R V).prod J ⊔ (⨆ k : Fin (m + 1), Ls k.succ).prod ⊥) by
    rw [Submodule.prod_sup_prod, Submodule.prod_sup_prod, bot_sup_eq, sup_bot_eq, bot_sup_eq]]

/-- **The inserted splitting is a Jordan splitting** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8,
p. 276): if $L = L_1 \perp \cdots \perp L_t$ is a Jordan splitting and $J$ is $\mathfrak sJ$-modular with
$\mathfrak s_1 \supsetneq \mathfrak sJ \supsetneq \mathfrak s_2$, then $L \perp J = L_1 \perp J \perp L_2 \perp \cdots
\perp L_t$ is a Jordan splitting. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (L ⊥ J = L_1 ⊥ L_{1½} ⊥ L_2 ⊥ ⋯ is Jordan)"]
theorem isJordanSplitting_insLs {L : Submodule R V} (hLfg : L.FG) (hL : IsJordanSplitting Q L Ls) (hJfg : J.FG)
    (hJ : IsModular QW (scale QW J) J) (h0 : scale QW J < scale Q (Ls 0)) (h1 : scale Q (Ls 1) < scale QW J) :
    IsJordanSplitting (Q.prod QW) (L.prod J) (insLs Ls J) := by
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls k)
  have hmodL : ∀ k, IsModular (Q.prod QW) (scale Q (Ls k)) ((Ls k).prod (⊥ : Submodule R W)) := fun k =>
    IsometricLat.isModular Q (Q.prod QW) (adj_isometricLat_prod_bot Q QW (Ls k)) (hLk k) (hL.modular k)
  have hmodJ : IsModular (Q.prod QW) (scale QW J) ((⊥ : Submodule R V).prod J) :=
    IsometricLat.isModular QW (Q.prod QW) (adj_isometricLat_bot_prod Q QW J) hJfg hJ
  have hmod : ∀ k, IsModular (Q.prod QW) (scale (Q.prod QW) (insLs Ls J k)) (insLs Ls J k) := by
    intro k
    by_cases hk : k = 1
    · subst hk; rw [insLs_one, scale_prod, scale_bot, bot_sup_eq]; exact hmodJ
    · rw [insLs_of_ne_one Ls J hk, scale_prod, scale_bot, sup_bot_eq]; exact hmodL _
  have hfg : (L.prod J).FG := by
    rw [prod_eq_sup, ← Submodule.map_inl, ← Submodule.map_inr]; exact (hLfg.map _).sup (hJfg.map _)
  have hor : ∀ i j, i ≠ j → ∀ x ∈ insLs Ls J i, ∀ y ∈ insLs Ls J j, bil (Q.prod QW) x y = 0 := by
    intro i j hij x hx y hy
    by_cases hi : i = 1
    · subst hi
      have hj : j ≠ 1 := Ne.symm hij
      rw [insLs_of_ne_one Ls J hj] at hy
      rw [insLs_one] at hx
      rw [bil_comm]
      exact bil_prod_bot Q QW _ J y hy x hx
    · by_cases hj : j = 1
      · subst hj
        rw [insLs_of_ne_one Ls J hi] at hx
        exact bil_prod_bot Q QW _ J x hx y hy
      · rw [insLs_of_ne_one Ls J hi] at hx
        rw [insLs_of_ne_one Ls J hj] at hy
        obtain ⟨x₁, x₂⟩ := x
        obtain ⟨y₁, y₂⟩ := y
        obtain ⟨hx₁, hx₂⟩ := hx
        obtain ⟨hy₁, hy₂⟩ := hy
        have hne : insIdx i ≠ insIdx j := fun h => hij (insIdx_inj hi hj h)
        obtain rfl : x₂ = 0 := hx₂
        rw [adj_bil_prod, hL.split.orth _ _ hne _ hx₁ _ hy₁]
        simp [bil]
  have hle : ∀ k, insLs Ls J k ≤ L.prod J := fun k => by
    rw [← hL.split.iSup_eq, ← iSup_insLs]; exact le_iSup (insLs Ls J) k
  refine ⟨⟨hor, iSupIndep_of_orth _ hor fun k => (hmod k).isRegular _ (FG.of_le hfg (hle k)), ?_⟩, hmod, ?_⟩
  · rw [iSup_insLs, hL.split.iSup_eq]
  · have hs : (fun k => scale (Q.prod QW) (insLs Ls J k)) =
        (Fin.cons (scale Q (Ls 0)) (Fin.cons (scale QW J) fun k : Fin (m + 1) => scale Q (Ls k.succ)) :
          Fin (m + 3) → Submodule R F) := funext (scale_insLs Q QW Ls J)
    rw [hs, Fin.strictAnti_iff_succ_lt]
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact h0
    · exact h1
    · show scale Q (Ls i.succ.succ) < scale Q (Ls i.succ.castSucc)
      exact hL.scale_strictAnti (by simp [Fin.lt_def])

/-- $L'_{(1)} = L_{(1)} \perp 0$ for the inserted splitting. -/
theorem jordanChain_insLs_zero : jordanChain (insLs Ls J) 0 = (jordanChain Ls 0).prod ⊥ := by
  rw [jordanChain_zero _ 0 rfl, jordanChain_zero _ 0 rfl]; rfl

/-- $L'_{(1\frac12)} = L_{(1)} \perp J$ for the inserted splitting. -/
theorem jordanChain_insLs_one : jordanChain (insLs Ls J) 1 = (jordanChain Ls 0).prod J := by
  rw [jordanChain_zero _ 0 rfl]
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k hk
    · exact fun _ => Submodule.prod_mono le_rfl bot_le
    · exact fun _ => Submodule.prod_mono bot_le le_rfl
    · intro h; exact absurd h (by simp [Fin.le_def])
  · rw [prod_eq_sup]
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le (0 : Fin (m + 3)) (Fin.zero_le _) le_rfl
    · exact le_iSup₂_of_le (1 : Fin (m + 3)) le_rfl le_rfl

/-- $L'_{(i)} = L_{(i)} \perp J$ for $i \ge 2$ (O'Meara's numbering) for the inserted splitting. -/
theorem jordanChain_insLs_succ_succ (k : Fin (m + 1)) :
    jordanChain (insLs Ls J) k.succ.succ = (jordanChain Ls k.succ).prod J := by
  apply le_antisymm
  · refine iSup₂_le fun i hi => ?_
    by_cases h1 : i = 1
    · subst h1; exact Submodule.prod_mono bot_le le_rfl
    · rw [insLs_of_ne_one Ls J h1]
      refine Submodule.prod_mono (le_iSup₂_of_le (insIdx i) ?_ le_rfl) bot_le
      induction i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        induction i using Fin.cases with
        | zero => exact absurd rfl h1
        | succ i => exact Fin.succ_le_succ_iff.1 hi
  · rw [prod_eq_sup]
    refine sup_le ?_ ?_
    · rw [jordanChain, ← Submodule.map_inl, Submodule.map_iSup]
      refine iSup_le fun i => ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun hi => ?_
      rw [Submodule.map_inl]
      induction i using Fin.cases with
      | zero => exact le_iSup₂_of_le (0 : Fin (m + 3)) (Fin.zero_le _) le_rfl
      | succ i => exact le_iSup₂_of_le i.succ.succ (Fin.succ_le_succ_iff.2 hi) le_rfl
    · exact le_iSup₂_of_le (Fin.succ 0 : Fin (m + 3)) (Fin.succ_le_succ_iff.2 (Fin.zero_le _)) le_rfl

end Split


section Fund

variable {m : ℕ} {Ls : Fin (m + 2) → Submodule R V} {J : Submodule R W}

theorem scale_insLs_of_ne_one {k : Fin (m + 3)} (hk : k ≠ 1) :
    scale (Q.prod QW) (insLs Ls J k) = scale Q (Ls (insIdx k)) := by
  rw [insLs_of_ne_one Ls J hk, scale_prod, scale_bot, sup_bot_eq]

theorem scale_insLs_one : scale (Q.prod QW) (insLs Ls J 1) = scale QW J := by
  rw [insLs_one, scale_prod, scale_bot, bot_sup_eq]

/-- $\mathfrak g(L'^{\mathfrak s}) = \mathfrak g(L^{\mathfrak s}) + \mathfrak g(J^{\mathfrak s})$ for the
fundamental sublattices of $L \perp J$. -/
theorem fundNormGroup_insLs (L : Submodule R V) (k : Fin (m + 3)) :
    fundNormGroup (Q.prod QW) (L.prod J) (insLs Ls J) k =
      normGroup Q (subA Q (scale (Q.prod QW) (insLs Ls J k)) L) ⊔
        normGroup QW (subA QW (scale (Q.prod QW) (insLs Ls J k)) J) := by
  simp only [fundNormGroup, fundSub]
  rw [subA_prod, normGroup_prod]

/-- `2c` lies in the norm group of $L^{\mathfrak s_i}$ for every $c \in \mathfrak s_i$. -/
theorem two_mul_mem_fundNormGroup {L : Submodule R V} (hLfg : L.FG) {t : ℕ} {Ks : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ks) (i : Fin t) {c : F} (hc : c ∈ scale Q (Ks i)) :
    2 * c ∈ normGroup Q (subA Q (scale Q (Ks i)) L) := by
  refine ⟨0, zero_mem _, c, ?_, by simp⟩
  have := scale_fundSub Q hLfg hL i
  simp only [fundSub] at this
  rw [this]; exact hc

/-- **The fundamental norm groups of the old indices are unchanged** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, step 8, p. 276: "$\mathfrak g'_i = \mathfrak g_i$"), when $\mathfrak gJ \subseteq 2\mathfrak p$ and
$\mathfrak g(J^{\mathfrak s}) \subseteq 2\mathfrak s$ for $\mathfrak s \subseteq \mathfrak p$, $\mathfrak s_1 =
\mathfrak o$, $\mathfrak s_2 \subseteq \mathfrak p$, $\mathfrak sJ = \pi\mathfrak o$. -/
theorem fundNormGroup_insLs_of_ne_one {π : R} {L : Submodule R V} (hLfg : L.FG) (hL : IsJordanSplitting Q L Ls)
    (hJs : scale QW J = R ∙ algebraMap R F π) (hsc0 : scale Q (Ls 0) = 1)
    (hsc1 : scale Q (Ls 1) ≤ R ∙ algebraMap R F π)
    (hgJ : ∀ z ∈ normGroup QW J, ∃ r : R, z = 2 * algebraMap R F π * algebraMap R F r)
    (hgJs : ∀ s : Submodule R F, s ≤ R ∙ algebraMap R F π →
      ∀ z ∈ normGroup QW (subA QW s J), ∃ c ∈ s, z = 2 * c)
    {k : Fin (m + 3)} (hk : k ≠ 1) :
    fundNormGroup (Q.prod QW) (L.prod J) (insLs Ls J) k = fundNormGroup Q L Ls (insIdx k) := by
  rw [fundNormGroup_insLs, scale_insLs_of_ne_one Q QW hk]
  refine sup_eq_left.mpr fun z hz => ?_
  induction k using Fin.cases with
  | zero =>
    have hJ1 : subA QW (scale Q (Ls (insIdx 0))) J = J := by
      refine subA_eq_self QW ?_
      show scale QW J ≤ scale Q (Ls 0)
      rw [hJs, hsc0, Submodule.one_eq_span, span_singleton_le_iff_mem]
      exact Submodule.mem_span_singleton.2 ⟨π, by simp [Algebra.smul_def]⟩
    rw [hJ1] at hz
    obtain ⟨r, rfl⟩ := hgJ z hz
    rw [mul_assoc]
    refine two_mul_mem_fundNormGroup Q hLfg hL _ ?_
    show _ ∈ scale Q (Ls 0)
    rw [hsc0, ← map_mul]
    exact Submodule.mem_one.2 ⟨π * r, rfl⟩
  | succ k =>
    induction k using Fin.cases with
    | zero => exact absurd rfl hk
    | succ k =>
      have hle : scale Q (Ls (insIdx k.succ.succ)) ≤ R ∙ algebraMap R F π :=
        (hL.scale_strictAnti.antitone (show (1 : Fin (m + 2)) ≤ k.succ from
          Fin.succ_le_succ_iff.2 (Fin.zero_le _))).trans hsc1
      obtain ⟨c, hc, rfl⟩ := hgJs _ hle z hz
      exact two_mul_mem_fundNormGroup Q hLfg hL _ hc

/-- **The norm group of $L^{\mathfrak p}$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8, p. 276; the
computation behind "$\pi^2\mathfrak g_1 \subseteq \mathfrak g'_{1\frac12}$, $\mathfrak g_2 \subseteq
\mathfrak g'_{1\frac12}$"): for a Jordan splitting with $\mathfrak s_1 = \mathfrak o$ and $\mathfrak s_2 \subseteq
\mathfrak p$, $L^{\mathfrak p} = \pi L_1 \perp L_2 \perp \cdots \perp L_t$, hence
$\mathfrak g(L^{\mathfrak p}) = \pi^2\mathfrak g_1 + \mathfrak g_2$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (g(L^p) = π²g_1 + g_2)"]
theorem normGroup_subA_pi [FiniteDimensional F V] {π : R} (hπ : Irreducible π) {L : Submodule R V} (hLfg : L.FG)
    (hL : IsJordanSplitting Q L Ls) (hsc0 : scale Q (Ls 0) = 1) (hsc1 : scale Q (Ls 1) ≤ R ∙ algebraMap R F π) :
    normGroup Q (subA Q (R ∙ algebraMap R F π) L) =
      (fundNormGroup Q L Ls 0).map (AddMonoidHom.mulLeft (algebraMap R F π ^ 2)) ⊔ fundNormGroup Q L Ls 1 := by
  set ϖ := algebraMap R F π with hϖ
  have hϖ0 : ϖ ≠ 0 := by
    rw [hϖ]; exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero
  have hpo : (R ∙ ϖ) ≤ (1 : Submodule R F) := by
    rw [span_singleton_le_iff_mem]; exact Submodule.mem_one.2 ⟨π, rfl⟩
  apply le_antisymm
  · -- `L^𝔭 = π L_1 ⊥ (L_2 ⊥ ⋯ ⊥ L_t)`
    have hoL := isOrthSum_zero_tail Q hLfg hL
    have hL0fg : (Ls 0).FG := FG.of_le hLfg (hL.split.iSup_eq ▸ le_iSup Ls 0)
    rw [show subA Q (R ∙ ϖ) L = subA Q (R ∙ ϖ) (Ls 0) ⊔ subA Q (R ∙ ϖ) (tailLat Ls) by
      conv_lhs => rw [← hoL.sup_eq]
      exact subA_sup_of_orth Q hoL.orth _]
    have hor : ∀ x ∈ subA Q (R ∙ ϖ) (Ls 0), ∀ y ∈ subA Q (R ∙ ϖ) (tailLat Ls), bil Q x y = 0 :=
      fun x hx y hy => hoL.orth x hx.1 y hy.1
    rw [normGroup_sup_of_orth Q hor]
    refine sup_le_sup ?_ ?_
    · have h0 : subA Q (R ∙ ϖ) (Ls 0) = (R ∙ ϖ) • Ls 0 := by
        have hm := hL.modular 0
        rw [hsc0] at hm
        rw [subA_of_isModular_of_ge Q (fg_span_singleton ϖ) (by simpa using hϖ0) hm hL0fg hpo]
        congr 1
        have h11 : (1 : Submodule R F) * (1 / 1) = 1 :=
          mul_one_div_cancel_of_fg (by rw [Submodule.one_eq_span]; exact fg_span_singleton 1) one_ne_zero
        rw [one_mul] at h11
        rw [h11, mul_one]
      rw [h0, normGroup_smul_lattice]
      refine AddSubgroup.map_mono ?_
      exact normGroup_mono Q (le_fundSub Q hLfg hL 0)
    · have htail : tailLat Ls ≤ fundSub Q L Ls 1 := iSup_le fun k =>
        (le_fundSub Q hLfg hL k.succ).trans
          (subA_mono Q (hL.scale_strictAnti.antitone (Fin.succ_le_succ_iff.2 (Fin.zero_le _))) L)
      exact normGroup_mono Q fun x hx => htail hx.1
  · refine sup_le ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      have hle : (R ∙ ϖ) • fundSub Q L Ls 0 ≤ subA Q (R ∙ ϖ) L := by
        intro x hx
        obtain ⟨x', hx', rfl⟩ := mem_span_singleton_smul_iff.mp hx
        refine ⟨by rw [hϖ, algebraMap_smul]; exact L.smul_mem π hx'.1, fun y hy => ?_⟩
        have h1 := hx'.2 y hy
        rw [hsc0] at h1
        obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
        rw [show bil Q (ϖ • x') y = ϖ * bil Q x' y by simp [bil], ← hr]
        exact Submodule.mem_span_singleton.2 ⟨r, by simp [Algebra.smul_def, mul_comm]⟩
      have := normGroup_mono Q hle
      rw [normGroup_smul_lattice] at this
      exact this ⟨y, hy, rfl⟩
    · exact normGroup_mono Q (subA_mono Q hsc1 L)

end Fund

section Invariants

variable [FiniteDimensional F V] {m : ℕ} {Ls Ks : Fin (m + 2) → Submodule R V} {J : Submodule R W}

theorem insA_of_ne_one (a : Fin (m + 2) → F) (c : F) {k : Fin (m + 3)} (hk : k ≠ 1) :
    insA a c k = a (insIdx k) := by
  induction k using Fin.cases with
  | zero => rfl
  | succ k =>
    induction k using Fin.cases with
    | zero => exact absurd rfl hk
    | succ k => rfl

include Q QW in
theorem finrank_prod_bot (A : Submodule R V) : finrank R (A.prod (⊥ : Submodule R W)) = finrank R A := by
  obtain ⟨f, -⟩ := adj_isometricLat_prod_bot Q QW A
  exact f.finrank_eq.symm

/-- A norm generator depends only on the norm group. -/
theorem isNormGenerator_of_normGroup_eq {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V']
    [IsScalarTower R F V'] {Q' : QuadraticForm F V'} {M : Submodule R V} {M' : Submodule R V'} {c : F}
    (h : IsNormGenerator Q M c) (hg : normGroup Q' M' = normGroup Q M) : IsNormGenerator Q' M' c :=
  ⟨hg ▸ h.1, by rw [normIdeal_eq_span_normGroup, hg, ← normIdeal_eq_span_normGroup]; exact h.2⟩

theorem fundSub_insLs_one_subA {π : R} (L : Submodule R V) (hJs : scale QW J = R ∙ algebraMap R F π) :
    fundNormGroup (Q.prod QW) (L.prod J) (insLs Ls J) 1 =
      normGroup Q (subA Q (R ∙ algebraMap R F π) L) ⊔ normGroup QW J := by
  rw [fundNormGroup_insLs, scale_insLs_one, hJs, subA_eq_self QW hJs.le]

/-- **The fundamental norm group at the inserted index**: $\mathfrak g'_{1\frac12} = \pi^2\mathfrak g_1 +
\mathfrak g_2 + \mathfrak gJ$. -/
theorem fundNormGroup_insLs_one {π : R} (hπ : Irreducible π) {L : Submodule R V} (hLfg : L.FG)
    (hL : IsJordanSplitting Q L Ls) (hJs : scale QW J = R ∙ algebraMap R F π) (hsc0 : scale Q (Ls 0) = 1)
    (hsc1 : scale Q (Ls 1) ≤ R ∙ algebraMap R F π) :
    fundNormGroup (Q.prod QW) (L.prod J) (insLs Ls J) 1 =
      ((fundNormGroup Q L Ls 0).map (AddMonoidHom.mulLeft (algebraMap R F π ^ 2)) ⊔ fundNormGroup Q L Ls 1) ⊔
        normGroup QW J := by
  rw [fundSub_insLs_one_subA Q QW L hJs, normGroup_subA_pi Q hπ hLfg hL hsc0 hsc1]

/-- **The fundamental norm generators of $L \perp J$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8,
p. 276: "$\mathfrak n(L')^{\mathfrak p} = \pi^2 a_1\mathfrak o$ and we can take $a'_{1\frac12} = \pi^2 a_1$ as a
fundamental norm generator"): $a_1, \pi^2a_1, a_2, \dots, a_t$, when $a_1\mathfrak o \supsetneq 2\mathfrak o$,
$a_2\mathfrak o \subseteq \pi^2a_1\mathfrak o$ and $\mathfrak gJ \subseteq 2\pi\mathfrak o$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (a'_{1½} = π²a_1 is a norm generator)"]
theorem isFundNormGenerators_insLs {π : R} (hπ : Irreducible π) {L : Submodule R V} (hLfg : L.FG)
    (hL : IsJordanSplitting Q L Ls) (hJs : scale QW J = R ∙ algebraMap R F π) (hsc0 : scale Q (Ls 0) = 1)
    (hsc1 : scale Q (Ls 1) ≤ R ∙ algebraMap R F π)
    (hgJ : ∀ z ∈ normGroup QW J, ∃ r : R, z = 2 * algebraMap R F π * algebraMap R F r)
    (hgJs : ∀ s : Submodule R F, s ≤ R ∙ algebraMap R F π →
      ∀ z ∈ normGroup QW (subA QW s J), ∃ c ∈ s, z = 2 * c)
    {a : Fin (m + 2) → F} (ha : IsFundNormGenerators Q L Ls a) (h8a : dord hπ (a 0) < dord hπ (2 : F))
    (h8b : dord hπ (a 0) + 2 ≤ dord hπ (a 1)) :
    IsFundNormGenerators (Q.prod QW) (L.prod J) (insLs Ls J) (insA a (algebraMap R F π ^ 2 * a 0)) := by
  intro k
  by_cases hk : k = 1
  · subst hk
    set ϖ := algebraMap R F π with hϖ
    have hϖ0 : ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero
    have ha0 : a 0 ≠ 0 := fundNormGenerator_ne_zero Q hLfg hL ha 0
    have hy0 : ϖ ^ 2 * a 0 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hϖ0) ha0
    have hdy : dord hπ (ϖ ^ 2 * a 0) = dord hπ (a 0) + 2 := by
      rw [dord_mul hπ (pow_ne_zero 2 hϖ0) ha0, pow_two, dord_mul hπ hϖ0 hϖ0, hϖ, dord_pi hπ]; ring
    rw [insA_one]
    have hg := fundNormGroup_insLs_one Q QW hπ hLfg hL hJs hsc0 hsc1
    simp only [fundNormGroup] at hg
    refine ⟨?_, ?_⟩
    · rw [hg]
      exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_left ⟨a 0, (ha 0).1, rfl⟩)
    · rw [normIdeal_eq_span_normGroup, hg]
      apply le_antisymm
      · rw [span_singleton_le_iff_mem]
        exact subset_span (AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_left ⟨a 0, (ha 0).1, rfl⟩))
      · rw [span_le]
        have hG : ((fundNormGroup Q L Ls 0).map (AddMonoidHom.mulLeft (ϖ ^ 2)) ⊔ fundNormGroup Q L Ls 1) ⊔
            normGroup QW J ≤ (R ∙ (ϖ ^ 2 * a 0)).toAddSubgroup := by
          refine sup_le (sup_le ?_ ?_) ?_
          · rintro _ ⟨y, hy, rfl⟩
            have hy' : y ∈ R ∙ a 0 := by
              rw [(ha 0).2]; exact normGroup_subset_normIdeal Q _ hy
            obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy'
            exact Submodule.mem_span_singleton.2 ⟨r, by simp [Algebra.smul_def]; ring⟩
          · intro y hy
            have hy' : y ∈ R ∙ a 1 := by
              rw [(ha 1).2]; exact normGroup_subset_normIdeal Q _ hy
            have ha1 : a 1 ∈ R ∙ (ϖ ^ 2 * a 0) := CoreFactor.mem_span_of_dord Q hπ hy0 fun _ => by
              rw [hdy]; exact h8b
            exact (span_singleton_le_iff_mem _ _).2 ha1 hy'
          · intro y hy
            obtain ⟨r, rfl⟩ := hgJ y hy
            have h2 : (2 : F) ≠ 0 := two_ne_zero
            have h2ϖ : 2 * ϖ ∈ R ∙ (ϖ ^ 2 * a 0) := CoreFactor.mem_span_of_dord Q hπ hy0 fun _ => by
              rw [hdy, dord_mul hπ h2 hϖ0, hϖ, dord_pi hπ]; omega
            obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.1 h2ϖ
            exact Submodule.mem_span_singleton.2 ⟨r * r', by
              rw [← hr']; simp [Algebra.smul_def]; ring⟩
        intro z hz
        exact hG hz
  · rw [insA_of_ne_one a _ hk]
    refine isNormGenerator_of_normGroup_eq Q (ha (insIdx k)) ?_
    have := fundNormGroup_insLs_of_ne_one Q QW hLfg hL hJs hsc0 hsc1 hgJ hgJs hk
    simpa only [fundNormGroup] using this

/-- **$L \perp J$ and $K \perp J$ have the same fundamental invariants** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, step 8, p. 276: "It is easily seen that $L'$ and $K'$ have the same fundamental invariants"). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (L', K' have the same fundamental invariants)"]
theorem sameFund_insLs {π : R} (hπ : Irreducible π) {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG)
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks) (hJs : scale QW J = R ∙ algebraMap R F π)
    (hsc0 : scale Q (Ls 0) = 1) (hsc1 : scale Q (Ls 1) ≤ R ∙ algebraMap R F π)
    (hgJ : ∀ z ∈ normGroup QW J, ∃ r : R, z = 2 * algebraMap R F π * algebraMap R F r)
    (hgJs : ∀ s : Submodule R F, s ≤ R ∙ algebraMap R F π →
      ∀ z ∈ normGroup QW (subA QW s J), ∃ c ∈ s, z = 2 * c)
    {a : Fin (m + 2) → F} (hS : SameFundamentalInvariants Q Q L K Ls Ks a)
    (h8a : dord hπ (a 0) < dord hπ (2 : F)) (h8b : dord hπ (a 0) + 2 ≤ dord hπ (a 1)) :
    SameFundamentalInvariants (Q.prod QW) (Q.prod QW) (L.prod J) (K.prod J) (insLs Ls J) (insLs Ks J)
      (insA a (algebraMap R F π ^ 2 * a 0)) := by
  obtain ⟨⟨h0, hT⟩, haL, haK⟩ := hS
  have hc : ∀ i : Fin (m + 2), Fin.cast h0 i = i := fun i => Fin.ext rfl
  have hrk : ∀ i, finrank R (Ls i) = finrank R (Ks i) := fun i => by have := (hT i).1; rwa [hc] at this
  have hs : ∀ i, scale Q (Ls i) = scale Q (Ks i) := fun i => by have := (hT i).2.1; rwa [hc] at this
  have hg : ∀ i, fundNormGroup Q L Ls i = fundNormGroup Q K Ks i := fun i => by
    have := (hT i).2.2; rwa [hc] at this
  have hsc0K : scale Q (Ks 0) = 1 := (hs 0) ▸ hsc0
  have hsc1K : scale Q (Ks 1) ≤ R ∙ algebraMap R F π := (hs 1) ▸ hsc1
  refine ⟨⟨rfl, fun i => ⟨?_, ?_, ?_⟩⟩, isFundNormGenerators_insLs Q QW hπ hLfg hL hJs hsc0 hsc1 hgJ hgJs haL h8a h8b,
    isFundNormGenerators_insLs Q QW hπ hKfg hK hJs hsc0K hsc1K hgJ hgJs haK h8a h8b⟩
  · show finrank R (insLs Ls J i) = finrank R (insLs Ks J i)
    by_cases hi : i = 1
    · subst hi; rfl
    · rw [insLs_of_ne_one Ls J hi, insLs_of_ne_one Ks J hi, finrank_prod_bot Q QW, finrank_prod_bot Q QW, hrk]
  · show scale (Q.prod QW) (insLs Ls J i) = scale (Q.prod QW) (insLs Ks J i)
    by_cases hi : i = 1
    · subst hi; rw [scale_insLs_one, scale_insLs_one]
    · rw [scale_insLs_of_ne_one Q QW hi, scale_insLs_of_ne_one Q QW hi, hs]
  · show fundNormGroup (Q.prod QW) (L.prod J) (insLs Ls J) i =
      fundNormGroup (Q.prod QW) (K.prod J) (insLs Ks J) i
    by_cases hi : i = 1
    · subst hi
      rw [fundNormGroup_insLs_one Q QW hπ hLfg hL hJs hsc0 hsc1,
        fundNormGroup_insLs_one Q QW hπ hKfg hK hJs hsc0K hsc1K, hg 0, hg 1]
    · rw [fundNormGroup_insLs_of_ne_one Q QW hLfg hL hJs hsc0 hsc1 hgJ hgJs hi,
        fundNormGroup_insLs_of_ne_one Q QW hKfg hK hJs hsc0K hsc1K hgJ hgJs hi, hg]

end Invariants

section FIdeals

open FundAux

/-- $\mathfrak f$ grows with the second norm group and the ideal of square roots. -/
theorem fIdealOf_mono {s : Submodule R F} {g g' g'' : AddSubgroup F} {n n' n'' : Submodule R F} (hg : g' ≤ g'')
    (hc : span R {z : F | (R ∙ z) * (R ∙ z) = n * n'} ≤ span R {z : F | (R ∙ z) * (R ∙ z) = n * n''}) :
    fIdealOf R s g g' n n' ≤ fIdealOf R s g g'' n n'' := by
  intro z hz
  rw [fIdealOf, Submodule.mem_div_iff_forall_mul_mem] at hz ⊢
  intro y hy
  refine SetLike.le_def.1 (sup_le_sup ?_ ?_) (hz y hy)
  · exact iSup_mono fun α => iSup_mono fun _ => iSup_le fun β => iSup_le fun hβ =>
      le_iSup_of_le β (le_iSup_of_le (hg hβ) le_rfl)
  · exact smul_mono_aux 2 (mul_le_mul' hc le_rfl)

/-- **$\mathfrak f_1 \subseteq \mathfrak f'_{1\frac12}$** at the level of `fIdealOf` (O'Meara 1963, §93F, proof of
93:28, sufficiency, step 8, p. 276): for $\mathfrak s = \mathfrak o$ against $\mathfrak s' = \varpi\mathfrak o$, when
$\varpi^2\mathfrak g \subseteq \mathfrak g'$ and $\varpi$ times the square roots for $(\mathfrak n, \mathfrak n_1)$ are
square roots for $(\mathfrak n', \mathfrak n_1)$. Every term of $\mathfrak f$ is multiplied by $\varpi^2$:
$\varpi^2\mathfrak d(\alpha\beta) = \mathfrak d(\varpi^2\alpha\beta)$. -/
theorem fIdealOf_le_pi {ϖ : F} (hϖ : ϖ ≠ 0) {g0 g1 g' : AddSubgroup F} {n0 n1 n' : Submodule R F}
    (hg : g0.map (AddMonoidHom.mulLeft (ϖ ^ 2)) ≤ g')
    (hc : (R ∙ ϖ) * span R {z : F | (R ∙ z) * (R ∙ z) = n0 * n1} ≤
      span R {z : F | (R ∙ z) * (R ∙ z) = n' * n1}) :
    fIdealOf R 1 g0 g1 n0 n1 ≤ fIdealOf R (R ∙ ϖ) g' g1 n' n1 := by
  intro z hz
  rw [fIdealOf, Submodule.mem_div_iff_forall_mul_mem] at hz ⊢
  have hz1 := hz 1 (by rw [mul_one]; exact Submodule.one_le.1 le_rfl)
  rw [mul_one] at hz1
  simp only [mul_one] at hz1
  intro y hy
  rw [span_mul_span'] at hy
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have key : (R ∙ (ϖ ^ 2)) *
      ((⨆ (α : F) (_ : α ∈ g0) (β : F) (_ : β ∈ g1), quadDefect R (α * β)) ⊔
        (2 : F) • span R {z : F | (R ∙ z) * (R ∙ z) = n0 * n1}) ≤
      (⨆ (α : F) (_ : α ∈ g') (β : F) (_ : β ∈ g1), quadDefect R (α * β)) ⊔
        (2 : F) • (span R {z : F | (R ∙ z) * (R ∙ z) = n' * n1} * (R ∙ ϖ)) := by
    rw [Submodule.mul_sup]
    refine sup_le_sup ?_ ?_
    · simp only [Submodule.mul_iSup]
      refine iSup_le fun α => iSup_le fun hα => iSup_le fun β => iSup_le fun hβ => ?_
      rw [← quadDefect_sq_mul, show ϖ ^ 2 * (α * β) = (AddMonoidHom.mulLeft (ϖ ^ 2) α) * β by
        simp only [AddMonoidHom.coe_mulLeft]; ring]
      exact le_iSup_of_le _ (le_iSup_of_le (hg ⟨α, hα, rfl⟩) (le_iSup_of_le β (le_iSup_of_le hβ le_rfl)))
    · rw [smul_eq_span_mul, smul_eq_span_mul, pow_two, ← span_mul_span']
      calc (R ∙ ϖ) * (R ∙ ϖ) * ((R ∙ (2 : F)) * span R {z : F | (R ∙ z) * (R ∙ z) = n0 * n1})
          = (R ∙ (2 : F)) * (((R ∙ ϖ) * span R {z : F | (R ∙ z) * (R ∙ z) = n0 * n1}) * (R ∙ ϖ)) := by
            ring
        _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' hc le_rfl)
  have hm := key (Submodule.mul_mem_mul (mem_span_singleton_self _) hz1)
  rw [show z * (r • (ϖ * ϖ)) = r • (ϖ ^ 2 * z) by simp [Algebra.smul_def]; ring]
  exact Submodule.smul_mem _ r hm

end FIdeals

section Cond

open FundAux

variable [FiniteDimensional F V] {m : ℕ} {Ls Ks : Fin (m + 2) → Submodule R V} {J : Submodule R W}

theorem fg_prod {L : Submodule R V} (hLfg : L.FG) (hJfg : J.FG) : (L.prod J).FG := by
  rw [prod_eq_sup, ← Submodule.map_inl, ← Submodule.map_inr]; exact (hLfg.map _).sup (hJfg.map _)

/-- The norm ideals $\mathfrak nL^{\mathfrak s_i}$ are the ideals $a_i\mathfrak o$. -/
theorem fundNormIdeal_eq {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
    {Q' : QuadraticForm F V'} {M : Submodule R V'} {t : ℕ} {Ms : Fin t → Submodule R V'} {b : Fin t → F}
    (hb : IsFundNormGenerators Q' M Ms b) (k : Fin t) : fundNormIdeal Q' M Ms k = R ∙ b k :=
  (hb k).2.symm

/-- **$\mathfrak f'_i = \mathfrak f_i$ away from the inserted index** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, step 8, p. 276: "hence from the definition $\mathfrak f'_i = \mathfrak f_i$ ($i = 2, \dots, t$)"). -/
theorem fIdeal_insLs_of_ne_one {π : R} {L : Submodule R V} (hLfg : L.FG) (hL : IsJordanSplitting Q L Ls)
    (hJs : scale QW J = R ∙ algebraMap R F π) (hsc0 : scale Q (Ls 0) = 1)
    (hsc1 : scale Q (Ls 1) ≤ R ∙ algebraMap R F π)
    (hgJ : ∀ z ∈ normGroup QW J, ∃ r : R, z = 2 * algebraMap R F π * algebraMap R F r)
    (hgJs : ∀ s : Submodule R F, s ≤ R ∙ algebraMap R F π →
      ∀ z ∈ normGroup QW (subA QW s J), ∃ c ∈ s, z = 2 * c)
    {i j : Fin (m + 3)} (hi : i ≠ 1) (hj : j ≠ 1) :
    fIdeal (Q.prod QW) (L.prod J) (insLs Ls J) i j = fIdeal Q L Ls (insIdx i) (insIdx j) := by
  unfold fIdeal
  rw [fIdeal_fundNormIdeal_eq_span, fIdeal_fundNormIdeal_eq_span, fIdeal_fundNormIdeal_eq_span,
    fIdeal_fundNormIdeal_eq_span, scale_insLs_of_ne_one Q QW hi,
    fundNormGroup_insLs_of_ne_one Q QW hLfg hL hJs hsc0 hsc1 hgJ hgJs hi,
    fundNormGroup_insLs_of_ne_one Q QW hLfg hL hJs hsc0 hsc1 hgJ hgJs hj]

/-- **$\mathfrak w'_i = \mathfrak w_i$ away from the inserted index** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, step 8, p. 276: "$\mathfrak w'_i = \mathfrak w_i$"). -/
theorem fundWeight_insLs_of_ne_one {π : R} {L : Submodule R V} (hLfg : L.FG) (hL : IsJordanSplitting Q L Ls)
    (hJfg : J.FG) (hJ : IsModular QW (scale QW J) J) (hJs : scale QW J = R ∙ algebraMap R F π)
    (hsc0 : scale Q (Ls 0) = 1) (hsc1 : scale Q (Ls 1) < R ∙ algebraMap R F π)
    (hp0 : R ∙ algebraMap R F π < scale Q (Ls 0))
    (hgJ : ∀ z ∈ normGroup QW J, ∃ r : R, z = 2 * algebraMap R F π * algebraMap R F r)
    (hgJs : ∀ s : Submodule R F, s ≤ R ∙ algebraMap R F π →
      ∀ z ∈ normGroup QW (subA QW s J), ∃ c ∈ s, z = 2 * c)
    {i : Fin (m + 3)} (hi : i ≠ 1) :
    fundWeight (Q.prod QW) (L.prod J) (insLs Ls J) i = fundWeight Q L Ls (insIdx i) := by
  have hJ' := isJordanSplitting_insLs Q QW Ls J hLfg hL hJfg hJ (hJs ▸ hp0) (hJs ▸ hsc1)
  refine weight_congr _ _ ?_ ?_
  · have := fundNormGroup_insLs_of_ne_one Q QW hLfg hL hJs hsc0 hsc1.le hgJ hgJs hi
    simpa only [fundNormGroup] using this
  · rw [scale_fundSub _ (fg_prod hLfg hJfg) hJ' i, scale_fundSub Q hLfg hL, scale_insLs_of_ne_one Q QW hi]

/-- **The data of the inserted lattice** $J$ (O'Meara's $J \cong \langle\pi A(0,0)\rangle$, `InsertJ.latJ`):
finitely generated, $\pi\mathfrak o$-modular, $\mathfrak gJ \subseteq 2\pi\mathfrak o$ and
$\mathfrak g(J^{\mathfrak s}) \subseteq 2\mathfrak s$ for $\mathfrak s \subseteq \mathfrak p$. -/
structure InsHyp (π : R) (J : Submodule R W) : Prop where
  fg : J.FG
  scale_eq : scale QW J = R ∙ algebraMap R F π
  modular : IsModular QW (scale QW J) J
  normGroup_le : ∀ z ∈ normGroup QW J, ∃ r : R, z = 2 * algebraMap R F π * algebraMap R F r
  normGroup_subA_le : ∀ s : Submodule R F, s ≤ R ∙ algebraMap R F π →
    ∀ z ∈ normGroup QW (subA QW s J), ∃ c ∈ s, z = 2 * c

/-- **The configuration of O'Meara's step 8** for a Jordan splitting with fundamental norm generators $a_i$
(0-based): $\mathfrak s_1 = \mathfrak o$, $\mathfrak s_2 \subseteq \mathfrak p^2$, $u_1 < \operatorname{ord} 2$,
$u_2 \ge u_1 + 2$. -/
structure Step8Conf (π : R) (hπ : Irreducible π) (Ls : Fin (m + 2) → Submodule R V) (a : Fin (m + 2) → F) :
    Prop where
  sc0 : scale Q (Ls 0) = 1
  sc1 : scale Q (Ls 1) ≤ R ∙ (algebraMap R F π ^ 2)
  ord0 : dord hπ (a 0) < dord hπ (2 : F)
  ord1 : dord hπ (a 0) + 2 ≤ dord hπ (a 1)

section Step8Facts

variable {π : R} {hπ : Irreducible π} {a : Fin (m + 2) → F}

theorem Step8Conf.sc1_lt (h : Step8Conf Q π hπ Ls a) : scale Q (Ls 1) < R ∙ algebraMap R F π := by
  refine lt_of_le_of_lt h.sc1 ?_
  have hϖ0 : algebraMap R F π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero
  refine lt_of_le_of_ne ?_ fun he => ?_
  · rw [span_singleton_le_iff_mem]
    exact Submodule.mem_span_singleton.2 ⟨π, by simp [Algebra.smul_def, pow_two]⟩
  · have hm : algebraMap R F π ∈ R ∙ (algebraMap R F π ^ 2) := he ▸ mem_span_singleton_self _
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hm
    rw [Algebra.smul_def, pow_two, ← mul_assoc] at hr
    have h1 : algebraMap R F r * algebraMap R F π = 1 :=
      mul_right_cancel₀ hϖ0 (by rw [hr, one_mul])
    rw [← map_mul, ← map_one (algebraMap R F)] at h1
    have hh : r * π = 1 := IsFractionRing.injective R F h1
    exact hπ.not_isUnit ⟨⟨π, r, by rw [mul_comm]; exact hh, hh⟩, rfl⟩

theorem pi_lt_one (hπ : Irreducible π) : R ∙ algebraMap R F π < (1 : Submodule R F) := by
  refine lt_of_le_of_ne ?_ fun he => ?_
  · rw [span_singleton_le_iff_mem]; exact Submodule.mem_one.2 ⟨π, rfl⟩
  · have hm : (1 : F) ∈ R ∙ algebraMap R F π := he ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hm
    rw [Algebra.smul_def, ← map_mul, ← map_one (algebraMap R F)] at hr
    have hh : r * π = 1 := IsFractionRing.injective R F hr
    exact hπ.not_isUnit ⟨⟨π, r, by rw [mul_comm]; exact hh, hh⟩, rfl⟩

variable {L K : Submodule R V} {J : Submodule R W}

theorem Step8Conf.jordan (h8 : Step8Conf Q π hπ Ls a) (hJ : InsHyp QW π J) (hLfg : L.FG)
    (hL : IsJordanSplitting Q L Ls) : IsJordanSplitting (Q.prod QW) (L.prod J) (insLs Ls J) :=
  isJordanSplitting_insLs Q QW Ls J hLfg hL hJ.fg hJ.modular (by rw [hJ.scale_eq, h8.sc0]; exact pi_lt_one hπ)
    (by rw [hJ.scale_eq]; exact h8.sc1_lt Q)

theorem Step8Conf.fundGens (h8 : Step8Conf Q π hπ Ls a) (hJ : InsHyp QW π J) (hLfg : L.FG)
    (hL : IsJordanSplitting Q L Ls) (ha : IsFundNormGenerators Q L Ls a) :
    IsFundNormGenerators (Q.prod QW) (L.prod J) (insLs Ls J) (insA a (algebraMap R F π ^ 2 * a 0)) :=
  isFundNormGenerators_insLs Q QW hπ hLfg hL hJ.scale_eq h8.sc0 (h8.sc1_lt Q).le hJ.normGroup_le
    hJ.normGroup_subA_le ha h8.ord0 h8.ord1

/-- **$\mathfrak f_1 \subseteq \mathfrak f'_1$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8, p. 276:
"hence from the definition $\mathfrak f_1 \subseteq \mathfrak f'_1$"). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (f_1 ⊆ f'_1)"]
theorem fIdeal_le_insLs_zero (h8 : Step8Conf Q π hπ Ls a) (hJ : InsHyp QW π J) (hLfg : L.FG)
    (hL : IsJordanSplitting Q L Ls) (ha : IsFundNormGenerators Q L Ls a) :
    fIdeal Q L Ls 0 1 ≤ fIdeal (Q.prod QW) (L.prod J) (insLs Ls J) 0 1 := by
  have ha' := h8.fundGens Q QW hJ hLfg hL ha
  have ha0 : a 0 ≠ 0 := fundNormGenerator_ne_zero Q hLfg hL ha 0
  have ha1 : a 1 ≠ 0 := fundNormGenerator_ne_zero Q hLfg hL ha 1
  set ϖ := algebraMap R F π with hϖ
  have hϖ0 : ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero
  have h01 : (0 : Fin (m + 3)) ≠ 1 := Fin.zero_ne_one
  unfold fIdeal
  rw [fundNormIdeal_eq ha 0, fundNormIdeal_eq ha 1, fundNormIdeal_eq ha' 0, fundNormIdeal_eq ha' 1, insA_zero,
    insA_one, scale_insLs_of_ne_one Q QW h01,
    fundNormGroup_insLs_of_ne_one Q QW hLfg hL hJ.scale_eq h8.sc0 (h8.sc1_lt Q).le hJ.normGroup_le
      hJ.normGroup_subA_le h01,
    fundNormGroup_insLs_one Q QW hπ hLfg hL hJ.scale_eq h8.sc0 (h8.sc1_lt Q).le]
  refine fIdealOf_mono (le_sup_of_le_left le_sup_right) ?_
  have hT : ϖ * a 0 ∈ span R {z : F | (R ∙ z) * (R ∙ z) = (R ∙ a 0) * (R ∙ (ϖ ^ 2 * a 0))} :=
    subset_span (show _ = _ by rw [span_mul_span', span_mul_span']; congr 1; ring)
  refine span_le.2 fun z hz => ?_
  obtain ⟨hz0, hdz⟩ := (mem_sqRoots_iff hπ ha0 ha1 z).1 hz
  have hzm : z ∈ R ∙ (ϖ * a 0) := CoreFactor.mem_span_of_dord Q hπ (mul_ne_zero hϖ0 ha0) fun _ => by
    rw [dord_mul hπ hϖ0 ha0, hϖ, dord_pi hπ]; have := h8.ord1; omega
  exact (span_singleton_le_iff_mem _ _).2 hT hzm

/-- **$\mathfrak f_1 \subseteq \mathfrak f'_{1\frac12}$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8,
p. 276: "hence from the definition $\mathfrak f_1 \subseteq \mathfrak f'_{1\frac12}$"). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (f_1 ⊆ f'_{1½})"]
theorem fIdeal_le_insLs_one (h8 : Step8Conf Q π hπ Ls a) (hJ : InsHyp QW π J) (hLfg : L.FG)
    (hL : IsJordanSplitting Q L Ls) (ha : IsFundNormGenerators Q L Ls a) :
    fIdeal Q L Ls 0 1 ≤ fIdeal (Q.prod QW) (L.prod J) (insLs Ls J) 1 (Fin.succ (Fin.succ 0)) := by
  have ha' := h8.fundGens Q QW hJ hLfg hL ha
  set ϖ := algebraMap R F π with hϖ
  have hϖ0 : ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero
  have h21 : (Fin.succ (Fin.succ 0) : Fin (m + 3)) ≠ 1 := by
    intro h; have := congrArg Fin.val h; simp at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  unfold fIdeal
  rw [fundNormIdeal_eq ha 0, fundNormIdeal_eq ha 1, fundNormIdeal_eq ha' 1, fundNormIdeal_eq ha' _,
    insA_one, insA_succ_succ, scale_insLs_one, hJ.scale_eq, h8.sc0,
    fundNormGroup_insLs_of_ne_one Q QW hLfg hL hJ.scale_eq h8.sc0 (h8.sc1_lt Q).le hJ.normGroup_le
      hJ.normGroup_subA_le h21,
    fundNormGroup_insLs_one Q QW hπ hLfg hL hJ.scale_eq h8.sc0 (h8.sc1_lt Q).le]
  refine fIdealOf_le_pi hϖ0 (le_sup_of_le_left le_sup_left) ?_
  rw [show (R ∙ ϖ) = span R {ϖ} from rfl, Submodule.span_mul_span]
  refine span_mono ?_
  rintro _ ⟨x, hx, z, hz, rfl⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  show _ = _
  have hz' : (R ∙ z) * (R ∙ z) = (R ∙ a 0) * (R ∙ a 1) := hz
  rw [span_mul_span', span_mul_span'] at hz' ⊢
  calc R ∙ (ϖ * z * (ϖ * z)) = (R ∙ (ϖ ^ 2)) * (R ∙ (z * z)) := by rw [span_mul_span']; congr 1; ring
    _ = (R ∙ (ϖ ^ 2)) * (R ∙ (a 0 * a 1)) := by rw [hz']
    _ = R ∙ (ϖ ^ 2 * a 0 * a 1) := by rw [span_mul_span']; congr 1; ring

theorem Step8Conf.of_sameFund (h8 : Step8Conf Q π hπ Ls a) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) :
    Step8Conf Q π hπ Ks a := by
  obtain ⟨⟨h0, hT⟩, -, -⟩ := hS
  have hs : ∀ i, scale Q (Ls i) = scale Q (Ks i) := fun i => by
    have := (hT i).2.1; rwa [show Fin.cast h0 i = i from Fin.ext rfl] at this
  exact ⟨hs 0 ▸ h8.sc0, hs 1 ▸ h8.sc1, h8.ord0, h8.ord1⟩

/-- **$\pi^2\mathfrak w_1 \subseteq \mathfrak w'_{1\frac12}$** (O'Meara 1963, §93F, proof of 93:28, sufficiency,
step 8, p. 276, "by Example 93:25"). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (π²w_1 ⊆ w'_{1½}, by 93:25)"]
theorem fundWeight_le_insLs_one (h8 : Step8Conf Q π hπ Ls a) (hJ : InsHyp QW π J) (hLfg : L.FG)
    (hL : IsJordanSplitting Q L Ls) :
    algebraMap R F π ^ 2 • fundWeight Q L Ls 0 ≤ fundWeight (Q.prod QW) (L.prod J) (insLs Ls J) 1 := by
  have hJ' := h8.jordan Q QW hJ hLfg hL
  have h01 : (0 : Fin (m + 3)) ≠ 1 := Fin.zero_ne_one
  have hw := fundWeight_insLs_of_ne_one Q QW hLfg hL hJ.fg hJ.modular hJ.scale_eq h8.sc0 (h8.sc1_lt Q)
    (by rw [h8.sc0]; exact pi_lt_one hπ) hJ.normGroup_le hJ.normGroup_subA_le h01
  rw [← show fundWeight (Q.prod QW) (L.prod J) (insLs Ls J) 0 = fundWeight Q L Ls 0 from hw]
  refine fundWeight_sq_smul_le (Q.prod QW) (fg_prod hLfg hJ.fg) hJ' (i := 0) (j := 1) (c := π) ?_
  rw [scale_insLs_one, scale_insLs_of_ne_one Q QW h01, hJ.scale_eq]
  exact (by rw [show insIdx (0 : Fin (m + 3)) = 0 from rfl, h8.sc0, mul_one])

/-- $2\pi \in \mathfrak w'_{1\frac12}$, since $\mathfrak w \supseteq 2\mathfrak s$ and $\mathfrak s'_{1\frac12} =
\mathfrak p$. -/
theorem two_pi_mem_fundWeight_insLs (h8 : Step8Conf Q π hπ Ls a) (hJ : InsHyp QW π J) (hLfg : L.FG)
    (hL : IsJordanSplitting Q L Ls) :
    2 * algebraMap R F π ∈ fundWeight (Q.prod QW) (L.prod J) (insLs Ls J) 1 := by
  have hJ' := h8.jordan Q QW hJ hLfg hL
  have hsc := scale_fundSub (Q.prod QW) (fg_prod hLfg hJ.fg) hJ' 1
  rw [scale_insLs_one, hJ.scale_eq] at hsc
  refine (weight_bounds (Q.prod QW) _).2.2.1 ?_
  rw [hsc]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (mem_span_singleton_self _)

/-- **$\mathfrak f'_1 = a_1\mathfrak w'_{1\frac12}$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8,
p. 276, by Example 93:27 since $u'_{1\frac12} = u_1 + 2$). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (f'_1 = a_1 w'_{1½}, by 93:27)"]
theorem fIdeal_insLs_zero_eq [HenselianLocalRing R] [Finite (ResidueField R)] (h2p : ¬ IsUnit (2 : R)) (h8 : Step8Conf Q π hπ Ls a) (hJ : InsHyp QW π J)
    (hLfg : L.FG) (hL : IsJordanSplitting Q L Ls) (ha : IsFundNormGenerators Q L Ls a)
    (hreg : IsRegular (Q.prod QW) (L.prod J)) :
    fIdeal (Q.prod QW) (L.prod J) (insLs Ls J) 0 1 = a 0 • fundWeight (Q.prod QW) (L.prod J) (insLs Ls J) 1 := by
  have hJ' := h8.jordan Q QW hJ hLfg hL
  have ha' := h8.fundGens Q QW hJ hLfg hL ha
  have h01 : (0 : Fin (m + 3)) ≠ 1 := Fin.zero_ne_one
  have ha0 : a 0 ≠ 0 := fundNormGenerator_ne_zero Q hLfg hL ha 0
  have hϖ0 : algebraMap R F π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero
  have hs0 : scale (Q.prod QW) (insLs Ls J 0) = R ∙ (1 : F) := by
    rw [scale_insLs_of_ne_one Q QW h01, ← Submodule.one_eq_span]; exact h8.sc0
  have hs1 : scale (Q.prod QW) (insLs Ls J 1) = R ∙ algebraMap R F π := by
    rw [scale_insLs_one]; exact hJ.scale_eq
  have h := mul_fIdeal_of_dord_add_two (Q.prod QW) hπ h2p (fg_prod hLfg hJ.fg) hreg hJ' ha' 0 1 rfl hs0 hs1
    (by
      rw [insA_one, insA_zero, dord_mul hπ (pow_ne_zero 2 hϖ0) ha0, pow_two, dord_mul hπ hϖ0 hϖ0, dord_pi hπ]
      ring)
    (by rw [dord_pi hπ, CoreFactor.dord_one Q hπ]; rfl)
  rw [hs0, ← Submodule.one_eq_span, one_mul, one_mul, insA_zero] at h
  exact h

/-- **Condition (ii) is vacuous at $i = 1$ for $L'$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8,
p. 276: "We see that (ii) is vacuous for $i = 1$ since then $\mathfrak w'_{1\frac12}\mathfrak f'_1 = a_1
\mathfrak w'^2_{1\frac12} \supseteq 4a_1\mathfrak p^2 = 4a'_{1\frac12}\mathfrak o$"). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 ((ii) is vacuous for i = 1)"]
theorem not_lt_insLs_zero [HenselianLocalRing R] [Finite (ResidueField R)] (h2p : ¬ IsUnit (2 : R)) (h8 : Step8Conf Q π hπ Ls a) (hJ : InsHyp QW π J)
    (hLfg : L.FG) (hL : IsJordanSplitting Q L Ls) (ha : IsFundNormGenerators Q L Ls a)
    (hreg : IsRegular (Q.prod QW) (L.prod J)) :
    ¬ fIdeal (Q.prod QW) (L.prod J) (insLs Ls J) 0 1 <
      (4 * insA a (algebraMap R F π ^ 2 * a 0) 1) • (1 / fundWeight (Q.prod QW) (L.prod J) (insLs Ls J) 1) := by
  intro hlt
  refine hlt.not_ge ?_
  rw [fIdeal_insLs_zero_eq Q QW h2p h8 hJ hLfg hL ha hreg, insA_one]
  set w := fundWeight (Q.prod QW) (L.prod J) (insLs Ls J) 1
  have h2ϖ := two_pi_mem_fundWeight_insLs Q QW h8 hJ hLfg hL
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  have hy1 := (Submodule.mem_div_iff_forall_mul_mem.1 hy) _ h2ϖ
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 hy1
  have : (4 * (algebraMap R F π ^ 2 * a 0)) • y = a 0 * (r • (2 * algebraMap R F π)) := by
    rw [smul_eq_mul, Algebra.smul_def, hr]; ring
  rw [this]
  exact mul_mem_smul_pointwise _ _ _ (w.smul_mem r h2ϖ)

/-- The bound $4\pi^2a_1\mathfrak w'^{-1}_{1\frac12} \subseteq 4a_1\mathfrak w_1^{-1}$, from $\pi^2\mathfrak w_1
\subseteq \mathfrak w'_{1\frac12}$ (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 8, p. 276: the check of
(iii) for $i = 1\frac12$, "left to the reader"). -/
theorem smul_div_le_insLs_one (h8 : Step8Conf Q π hπ Ls a) (hJ : InsHyp QW π J) (hLfg : L.FG)
    (hL : IsJordanSplitting Q L Ls) :
    (4 * (algebraMap R F π ^ 2 * a 0)) • (1 / fundWeight (Q.prod QW) (L.prod J) (insLs Ls J) 1) ≤
      (4 * a 0) • (1 / fundWeight Q L Ls 0) := by
  have hw := fundWeight_le_insLs_one Q QW h8 hJ hLfg hL
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨algebraMap R F π ^ 2 * y, ?_, ?_⟩
  · refine Submodule.mem_div_iff_forall_mul_mem.2 fun w hw0 => ?_
    have := (Submodule.mem_div_iff_forall_mul_mem.1 hy) _
      (hw (Submodule.smul_mem_pointwise_smul w (algebraMap R F π ^ 2) _ hw0))
    rw [smul_eq_mul] at this
    rw [show algebraMap R F π ^ 2 * y * w = y * (algebraMap R F π ^ 2 * w) by ring]
    exact this
  · simp only [smul_eq_mul]; ring

/-- $FM \to FN \perp \langle c\rangle$ gives $FM \to FN \perp \langle \beta^2 c\rangle$ for $\beta \ne 0$
($\langle c\rangle \cong \langle\beta^2c\rangle$). -/
theorem spanRepresents_sq_mul {M N : Submodule R V} {c β : F} (hβ : β ≠ 0) (h : SpanRepresents Q M N c) :
    SpanRepresents Q M N (β ^ 2 * c) := by
  obtain ⟨f, hf, hQ⟩ := h
  refine ⟨(LinearMap.fst F _ _ ∘ₗ f).prod (β⁻¹ • (LinearMap.snd F _ _ ∘ₗ f)), fun x y hxy => hf ?_, fun x => ?_⟩
  · have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    simp only [LinearMap.prod_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply,
      LinearMap.smul_apply, LinearMap.snd_apply, smul_eq_mul] at h1 h2
    exact Prod.ext h1 (mul_left_cancel₀ (inv_ne_zero hβ) h2)
  · have e1 : ((LinearMap.fst F _ _ ∘ₗ f).prod (β⁻¹ • (LinearMap.snd F _ _ ∘ₗ f)) x).1 = (f x).1 := rfl
    have e2 : ((LinearMap.fst F _ _ ∘ₗ f).prod (β⁻¹ • (LinearMap.snd F _ _ ∘ₗ f)) x).2 = β⁻¹ * (f x).2 := rfl
    rw [e1, e2, ← hQ x]
    field_simp

/-- $dM/dN \cong 1 \bmod \mathfrak a$ is weaker for a larger ideal. -/
theorem discQuot_mono {M N : Submodule R V} {X Y : Submodule R F} (hXY : X ≤ Y)
    (h : DiscQuotSqEquivMod Q M N X) : DiscQuotSqEquivMod Q M N Y := by
  obtain ⟨b, b', ⟨hu, ε, hε, hmem⟩⟩ := h
  exact ⟨b, b', hu, ε, hε, hXY hmem⟩

theorem isRegular_bot_W : IsRegular QW (⊥ : Submodule R W) := fun x hx _ => (mem_bot R).1 hx

/-- **Conditions (i)–(iii) for $L' = L \perp J$ and $K' = K \perp J$** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, step 8, p. 276: "It is now obvious that $L'$ and $K'$ satisfy (i) for all $i$. Also that they satisfy
(ii) and (iii) for $i = 2, \dots, t$. Also that they satisfy (ii) for $i = 1\frac12$. We see that (ii) is vacuous for
$i = 1$ \dots We leave the verification of (iii) for $i = 1$ and $i = 1\frac12$ to the reader."). Here: (i) at
$1$, $1\frac12$ from (i) at $1$ and $\mathfrak f_1 \subseteq \mathfrak f'_1, \mathfrak f'_{1\frac12}$; (ii) at $1$
is vacuous; (iii) at $1$ from (iii) at $1$ ($\mathfrak w'_1 = \mathfrak w_1$); (ii) at $1\frac12$ from (ii) at $1$
($a'_2 = a_2$, $\mathfrak w'_2 = \mathfrak w_2$); (iii) at $1\frac12$ from (iii) at $1$, since
$4\pi^2a_1\mathfrak w'^{-1}_{1\frac12} \subseteq 4a_1\mathfrak w_1^{-1}$ and $\langle a_1\rangle \cong
\langle\pi^2a_1\rangle$; the indices $i \ge 2$ are unchanged. In every case the representation or discriminant
statement for $L_{(i)}, K_{(i)}$ passes to $L_{(i)} \perp J, K_{(i)} \perp J$ (`discQuot_prod_iff`,
`RepTransfer.spanRepresents_prod_iff`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 8, p. 276 (L', K' satisfy (i)–(iii))"]
theorem cond93_insLs [HenselianLocalRing R] [Finite (ResidueField R)] [FiniteDimensional F W]
    (h2p : ¬ IsUnit (2 : R)) (h8 : Step8Conf Q π hπ Ls a) (hJ : InsHyp QW π J) (hLfg : L.FG) (hKfg : K.FG)
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks) (hreg : IsRegular (Q.prod QW) (L.prod J))
    (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a) :
    Cond93 (Q.prod QW) (L.prod J) (insLs Ls J) (insLs Ks J) (insA a (algebraMap R F π ^ 2 * a 0)) := by
  have ha := hS.2.1
  have hJreg : IsRegular QW J := hJ.modular.isRegular QW hJ.fg
  have hϖ0 : algebraMap R F π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero
  have hane : ∀ k, a k ≠ 0 := fundNormGenerator_ne_zero Q hLfg hL ha
  have hchL : ∀ i, (jordanChain Ls i).FG := fun i => FG.of_le hLfg (iSup₂_le fun j _ =>
    hL.split.iSup_eq ▸ le_iSup Ls j)
  have hchK : ∀ i, (jordanChain Ks i).FG := fun i => FG.of_le hKfg (iSup₂_le fun j _ =>
    hK.split.iSup_eq ▸ le_iSup Ks j)
  have hregK : ∀ i, IsRegular Q (jordanChain Ks i) := isRegular_jordanChain Q hKfg hK
  have h01 : (0 : Fin (m + 3)) ≠ 1 := Fin.zero_ne_one
  have hw0 : ∀ i : Fin (m + 3), i ≠ 1 →
      fundWeight (Q.prod QW) (L.prod J) (insLs Ls J) i = fundWeight Q L Ls (insIdx i) := fun i hi =>
    fundWeight_insLs_of_ne_one Q QW hLfg hL hJ.fg hJ.modular hJ.scale_eq h8.sc0 (h8.sc1_lt Q)
      (by rw [h8.sc0]; exact pi_lt_one hπ) hJ.normGroup_le hJ.normGroup_subA_le hi
  have hfL : ∀ i j : Fin (m + 3), i ≠ 1 → j ≠ 1 →
      fIdeal (Q.prod QW) (L.prod J) (insLs Ls J) i j = fIdeal Q L Ls (insIdx i) (insIdx j) := fun i j hi hj =>
    fIdeal_insLs_of_ne_one Q QW hLfg hL hJ.scale_eq h8.sc0 (h8.sc1_lt Q).le hJ.normGroup_le
      hJ.normGroup_subA_le hi hj
  -- passing a representation or a discriminant statement to the products
  have hdisc : ∀ (H : Submodule R W), H.FG → IsRegular QW H → ∀ (i : Fin (m + 2)) (X : Submodule R F),
      DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) X →
      DiscQuotSqEquivMod (Q.prod QW) ((jordanChain Ls i).prod H) ((jordanChain Ks i).prod H) X :=
    fun H hH hHr i X h => (discQuot_prod_iff Q QW (hchL i) (hchK i) hH (hregK i) hHr).2 h
  have hrep : ∀ (H : Submodule R W), IsRegular QW H → ∀ (i : Fin (m + 2)) (c : F), c ≠ 0 →
      SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) c →
      SpanRepresents (Q.prod QW) ((jordanChain Ls i).prod H) ((jordanChain Ks i).prod H) c :=
    fun H hHr i c hc h => (RepTransfer.spanRepresents_prod_iff Q QW (hregK i) hHr hc).2 h
  have hfg0 : (⊥ : Submodule R W).FG := fg_bot
  obtain ⟨hC1, hC2, hC3⟩ := hC 0 1 rfl
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    obtain rfl : j = 1 := Fin.ext (by simpa using hij)
    rw [jordanChain_insLs_zero, jordanChain_insLs_zero]
    refine ⟨hdisc ⊥ hfg0 (isRegular_bot_W QW) 0 _
      (discQuot_mono Q (fIdeal_le_insLs_zero Q QW h8 hJ hLfg hL ha) hC1), fun hlt => ?_, fun hlt => ?_⟩
    · exact absurd hlt (not_lt_insLs_zero Q QW h2p h8 hJ hLfg hL ha hreg)
    · rw [insA_zero, hw0 _ h01] at hlt
      exact hrep ⊥ (isRegular_bot_W QW) 0 _ (hane 0)
        (hC3 (lt_of_le_of_lt (fIdeal_le_insLs_zero Q QW h8 hJ hLfg hL ha) hlt))
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      obtain rfl : j = Fin.succ (Fin.succ 0) := Fin.ext (by rw [hij]; simp only [Fin.val_succ, Fin.val_zero])
      show DiscQuotSqEquivMod _ (jordanChain (insLs Ls J) 1) (jordanChain (insLs Ks J) 1) _ ∧
        (_ → SpanRepresents _ (jordanChain (insLs Ls J) 1) (jordanChain (insLs Ks J) 1) _) ∧
        (_ → SpanRepresents _ (jordanChain (insLs Ls J) 1) (jordanChain (insLs Ks J) 1) _)
      rw [jordanChain_insLs_one, jordanChain_insLs_one]
      have hf1 := fIdeal_le_insLs_one Q QW h8 hJ hLfg hL ha
      refine ⟨hdisc J hJ.fg hJreg 0 _ (discQuot_mono Q hf1 hC1), fun hlt => ?_, fun hlt => ?_⟩
      · have h21 : (Fin.succ (Fin.succ 0) : Fin (m + 3)) ≠ 1 := by
          intro h; have := congrArg Fin.val h; simp at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
        rw [insA_succ_succ, hw0 _ h21] at hlt
        exact hrep J hJreg 0 _ (hane 1) (hC2 (lt_of_le_of_lt hf1 hlt))
      · rw [show insA a (algebraMap R F π ^ 2 * a 0) (Fin.succ 0) = algebraMap R F π ^ 2 * a 0 from rfl] at hlt
        have h := hC3 (lt_of_le_of_lt hf1 (lt_of_lt_of_le hlt (smul_div_le_insLs_one Q QW h8 hJ hLfg hL)))
        exact hrep J hJreg 0 _ (mul_ne_zero (pow_ne_zero 2 hϖ0) (hane 0)) (spanRepresents_sq_mul Q hϖ0 h)
    | succ k =>
      have hj2 : 2 ≤ (j : ℕ) := by simp at hij; omega
      obtain ⟨jo, rfl⟩ : ∃ jo : Fin (m + 1), j = jo.succ.succ :=
        ⟨⟨j - 2, by omega⟩, Fin.ext (by simp; omega)⟩
      have hjo : (jo.succ : ℕ) = (k.succ : ℕ) + 1 := by simp at hij ⊢; omega
      obtain ⟨hD, hR2, hR3⟩ := hC k.succ jo.succ hjo
      have hk1 : (k.succ.succ : Fin (m + 3)) ≠ 1 := fun h => by
        have := congrArg Fin.val h; simp at this
      have hj1 : (jo.succ.succ : Fin (m + 3)) ≠ 1 := fun h => by
        have := congrArg Fin.val h; simp at this
      rw [jordanChain_insLs_succ_succ, jordanChain_insLs_succ_succ, hfL _ _ hk1 hj1, insA_succ_succ, insA_succ_succ,
        hw0 _ hk1, hw0 _ hj1]
      exact ⟨hdisc J hJ.fg hJreg _ _ hD, fun hlt => hrep J hJreg _ _ (hane _) (hR2 hlt),
        fun hlt => hrep J hJreg _ _ (hane _) (hR3 hlt)⟩

end Step8Facts

end Cond

end QuadFormsKB.OMeara.Insert
