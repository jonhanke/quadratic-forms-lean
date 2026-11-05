/-
# O'Meara 93:28, proof of the necessity, step 1: the special case, condition (i)

**Setting** (as in `Sec93E.lean`): $R$ a Henselian discrete valuation ring with finite residue field and fraction
field $F$, $2 \ne 0$ in $R$; $(V, Q)$ a quadratic space over $F$; lattices `Submodule R V`. Indices are $0$-based:
O'Meara's $L_1$, $L_2$, $\mathfrak f_1$ are `Ls i₀`, `Ls i₁`, `fIdeal Q L Ls i₀ i₁` with `i₀ = 0`, `i₁ = 1`.

**Proves** (O'Meara 1963, §93F, proof of 93:28, necessity, step 1, pp. 268–269)
* `others_bil_mem`, `mem_subA_of_others`: for a Jordan splitting $L = K_1 \perp K_{(2)}^*$, $K^*_{(2)} \subseteq
  L^{\mathfrak s_2}$;
* `nec_base_disc`: if $L = L_1 \perp \cdots \perp L_t = K_1 \perp \cdots \perp K_t$ are two Jordan splittings of the same
  lattice, $L_1$ unimodular with a base of matrix $A(a', 0) \perp A(a'', 0)$, then
  $dL_1/dK_1 \cong 1 \bmod \mathfrak f_1$ (condition (i) of 93:28 for $i = 1$ in the special case).

The proof is O'Meara's: write the base vectors $x_k = y_k + Y_k$ with $y_k \in K_1$, $Y_k \in K^*_{(2)}$; then
$B(x_k, x_l) \equiv B(y_k, y_l) \bmod \mathfrak s_2$ and $Q(x_k) \equiv Q(y_k) \bmod \mathfrak g_2$, the $y_k$ form a base
of $K_1$, orthogonalize $y_3, y_4$ against $y_1, y_2$, and compute the two binary discriminants with
`sqEquivMod_sq_add_mul`.
-/
import QuadFormsKB.Literature.OMeara.Sec93FArith
import QuadFormsKB.Literature.OMeara.Sec93SatProof

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecBase

open Sat93 Arith28 D18

section Others

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- $B(K^*_{(2)}, K^*_{(2)}) \subseteq \mathfrak s_2$: the components after the first have scales inside
$\mathfrak sK_2$. -/
theorem others_bil_mem {L : Submodule R V} {t : ℕ} {Ks : Fin t → Submodule R V} (hK : IsJordanSplitting Q L Ks)
    (i₀ i₁ : Fin t) (h₀ : i₀.val = 0) (h₁ : i₁.val = 1) :
    ∀ u ∈ others Ks i₀, ∀ v ∈ others Ks i₀, bil Q u v ∈ scale Q (Ks i₁) := by
  have hle : ∀ j : Fin t, j ≠ i₀ → scale Q (Ks j) ≤ scale Q (Ks i₁) := fun j hj =>
    hK.scale_strictAnti.antitone (Fin.le_def.2 (by have := Fin.val_ne_of_ne hj; omega))
  have inner : ∀ j : Fin t, j ≠ i₀ → ∀ u ∈ Ks j, ∀ v ∈ others Ks i₀, bil Q u v ∈ scale Q (Ks i₁) := by
    intro j hj u hu v hv
    refine Submodule.iSup_induction (fun k : {k : Fin t // k ≠ i₀} => Ks k)
      (motive := fun v => bil Q u v ∈ scale Q (Ks i₁)) hv ?_ (by simp [bil]) ?_
    · intro k w hw
      by_cases hjk : j = k.1
      · rw [← hjk] at hw; exact hle j hj (bil_mem_scale Q hu hw)
      · rw [hK.split.orth j k.1 hjk u hu w hw]; exact zero_mem _
    · intro v w hv hw; rw [bil_add_right]; exact add_mem hv hw
  intro u hu v hv
  refine Submodule.iSup_induction (fun k : {k : Fin t // k ≠ i₀} => Ks k)
    (motive := fun u => bil Q u v ∈ scale Q (Ks i₁)) hu ?_ (by simp [bil]) ?_
  · intro k w hw; exact inner k.1 k.2 w hw v hv
  · intro u w hu hw; rw [bil_add_left]; exact add_mem hu hw

/-- $K^*_{(2)} \subseteq L^{\mathfrak s_2}$. -/
theorem mem_subA_of_others {L : Submodule R V} {t : ℕ} {Ks : Fin t → Submodule R V}
    (hK : IsJordanSplitting Q L Ks) (i₀ i₁ : Fin t) (h₀ : i₀.val = 0) (h₁ : i₁.val = 1) {Y : V}
    (hY : Y ∈ others Ks i₀) : Y ∈ subA Q (scale Q (Ks i₁)) L := by
  have hoL : others Ks i₀ ≤ L := (sup_others Q hK.split i₀) ▸ le_sup_right
  refine ⟨hoL hY, fun l hl => ?_⟩
  rw [← sup_others Q hK.split i₀] at hl
  obtain ⟨k, hk, o, ho, rfl⟩ := mem_sup.mp hl
  rw [bil_add_right, bil_comm, orth_others Q hK.split i₀ hk Y hY, zero_add]
  exact others_bil_mem Q hK i₀ i₁ h₀ h₁ Y hY o ho

end Others

section Base

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- A fractional ideal strictly inside $\mathfrak o$ lies in $\mathfrak p$. -/
theorem exists_max_of_lt_one {s : Submodule R F} (hfg : s.FG) (h0 : s ≠ ⊥) (hlt : s < 1) {z : F} (hz : z ∈ s) :
    ∃ r ∈ maximalIdeal R, algebraMap R F r = z := by
  obtain ⟨σ, -, rfl⟩ := exists_eq_span_singleton (R := R) hfg h0
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hlt.le (mem_span_singleton_self σ))
  have hrm : r ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hlt.ne
    rw [← hr, Submodule.one_eq_span]
    apply le_antisymm
    · rw [span_singleton_le_iff_mem]; exact mem_span_singleton.2 ⟨r, by rw [Algebra.smul_def, mul_one]⟩
    · rw [span_singleton_le_iff_mem]
      obtain ⟨r', hr'⟩ := hu.exists_left_inv
      exact mem_span_singleton.2 ⟨r', by rw [Algebra.smul_def, ← map_mul, hr', map_one]⟩
  obtain ⟨c, rfl⟩ := mem_span_singleton.mp hz
  exact ⟨c * r, Ideal.mul_mem_left _ _ hrm, by rw [← hr, map_mul, Algebra.smul_def]⟩

/-- An element of $\mathfrak p \setminus 0$ has order $\ge 1$. -/
theorem one_le_dord_of_max {π : R} (hπ : Irreducible π) {r : R} (hr : r ∈ maximalIdeal R)
    (h0 : algebraMap R F r ≠ 0) : 1 ≤ dord hπ (algebraMap R F r) := by
  have hmax : maximalIdeal R = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  rw [hmax, Ideal.mem_span_singleton] at hr
  obtain ⟨r', rfl⟩ := hr
  have hr'0 : algebraMap R F r' ≠ 0 := by rintro h; rw [map_mul, h, mul_zero] at h0; exact h0 rfl
  rw [map_mul, dord_mul hπ (alg_pi_ne_zero hπ) hr'0, dord_pi]
  have := dord_alg_nonneg (F := F) hπ (r := r') (by rintro rfl; simp at hr'0)
  omega

/-- The determinant of a $4 \times 4$ matrix with two diagonal $2 \times 2$ blocks. -/
theorem det_two_blocks (A B C A' B' C' : F) :
    (Matrix.of ![![A, B, 0, 0], ![B, C, 0, 0], ![0, 0, A', B'], ![0, 0, B', C']]).det =
      (A * C - B ^ 2) * (A' * C' - B' ^ 2) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- The discriminant does not depend on the indexing of a base. -/
theorem det_gram_reindex {M : Submodule R V} {n m : ℕ} (e : Basis (Fin n) R M) (h : n = m) :
    (gram Q fun i => (e.reindex (finCongr h) i : V)).det = (gram Q fun i => (e i : V)).det := by
  subst h
  congr 2
  ext i
  simp

/-- **Orthogonalizing against a binary sublattice** (O'Meara 1963, p. 269, "solve the pair of equations"): if
$y_1, y_2$ have matrix with entries in $\mathfrak o$ and unit determinant $D$, and $B(y, y_1), B(y, y_2)$ lie in an
$R$-submodule $\mathfrak s \subseteq \mathfrak o$, then $y' = y + \xi y_1 + \eta y_2$ with $\xi, \eta \in \mathfrak s$
is orthogonal to $y_1$ and $y_2$. -/
theorem exists_orth_pair {y₀ y₁ y : V} {A Bv C : R} (hA : Q y₀ = algebraMap R F A)
    (hB : bil Q y₀ y₁ = algebraMap R F Bv) (hC : Q y₁ = algebraMap R F C) (hu : IsUnit (A * C - Bv ^ 2))
    {s : Submodule R F} (hp : bil Q y y₀ ∈ s) (hq : bil Q y y₁ ∈ s)
    (hsR : ∀ z ∈ s, ∃ r : R, algebraMap R F r = z) :
    ∃ r₀ r₁ : R, algebraMap R F r₀ ∈ s ∧ algebraMap R F r₁ ∈ s ∧
      bil Q (y + r₀ • y₀ + r₁ • y₁) y₀ = 0 ∧ bil Q (y + r₀ • y₀ + r₁ • y₁) y₁ = 0 := by
  obtain ⟨w, hw⟩ := hu.exists_left_inv
  set D := A * C - Bv ^ 2 with hD
  have hwF : algebraMap R F w * algebraMap R F D = 1 := by rw [← map_mul, hw, map_one]
  have hDF : algebraMap R F D ≠ 0 := fun h => by rw [h, mul_zero] at hwF; exact zero_ne_one hwF
  set p := bil Q y y₀
  set q := bil Q y y₁
  have hξ : algebraMap R F w * (algebraMap R F Bv * q - algebraMap R F C * p) ∈ s := by
    have : algebraMap R F w * (algebraMap R F Bv * q - algebraMap R F C * p) = (w * Bv) • q - (w * C) • p := by
      simp only [Algebra.smul_def, map_mul]; ring
    rw [this]; exact sub_mem (smul_mem _ _ hq) (smul_mem _ _ hp)
  have hη : algebraMap R F w * (algebraMap R F Bv * p - algebraMap R F A * q) ∈ s := by
    have : algebraMap R F w * (algebraMap R F Bv * p - algebraMap R F A * q) = (w * Bv) • p - (w * A) • q := by
      simp only [Algebra.smul_def, map_mul]; ring
    rw [this]; exact sub_mem (smul_mem _ _ hp) (smul_mem _ _ hq)
  obtain ⟨r₀, hr₀⟩ := hsR _ hξ
  obtain ⟨r₁, hr₁⟩ := hsR _ hη
  have hBA : bil Q y₀ y₀ = algebraMap R F A := by rw [bil_self, hA]
  have hBC : bil Q y₁ y₁ = algebraMap R F C := by rw [bil_self, hC]
  have hB' : bil Q y₁ y₀ = algebraMap R F Bv := by rw [bil_comm, hB]
  have hDdef : algebraMap R F D = algebraMap R F A * algebraMap R F C - algebraMap R F Bv ^ 2 := by
    rw [hD, map_sub, map_mul, map_pow]
  refine ⟨r₀, r₁, hr₀ ▸ hξ, hr₁ ▸ hη, ?_, ?_⟩
  · rw [bil_add_left, bil_add_left, bil_rsmul_left, bil_rsmul_left, hr₀, hr₁, hBA, hB']
    linear_combination (-p) * hwF + (p) * (algebraMap R F w) * hDdef
  · rw [bil_add_left, bil_add_left, bil_rsmul_left, bil_rsmul_left, hr₀, hr₁, hBC, hB]
    linear_combination (-q) * hwF + (q) * (algebraMap R F w) * hDdef

/-- **93:28, necessity, step 1, condition (i)** (O'Meara 1963, §93F, pp. 268–269). Let
$L = L_1 \perp \cdots \perp L_t = K_1 \perp \cdots \perp K_t$ be two Jordan splittings of the same lattice ($t \ge 2$),
with fundamental norm generators $a_i$, and suppose $L_1$ is unimodular with a base of matrix
$A(a', 0) \perp A(a'', 0)$ (this is how O'Meara uses the hypothesis "$FL_1$ is $4$-dimensional hyperbolic").
Then $dL_1/dK_1 \cong 1 \bmod \mathfrak f_1$. (O'Meara treats $u_1 = u_2$ separately; the computation below covers
both cases.) -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity, step 1, pp. 268–269 (condition (i))"]
theorem nec_base_disc (h2 : (2 : R) ≠ 0) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q L Ks)
    (i₀ i₁ : Fin t) (h₀ : i₀.val = 0) (h₁ : i₁.val = 1) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a)
    (hU : scale Q (Ls i₀) = 1) {a' a'' : F} (hblk : HasBlk Q (Ls i₀) a' 0 a'' 0) :
    DiscQuotSqEquivMod Q (jordanChain Ls i₀) (jordanChain Ks i₀) (fIdeal Q L Ls i₀ i₁) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [jordanChain_zero Ls i₀ h₀, jordanChain_zero Ks i₀ h₀]
  have hreg := isRegular_of_isJordanSplitting Q hfg hL
  -- the Jordan types agree
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK
  have hc : ∀ i, Fin.cast hT i = i := fun i => Fin.ext (by simp)
  have hsc : ∀ i, scale Q (Ls i) = scale Q (Ks i) := fun i => by have := (hJT i).1; rwa [hc] at this
  have hrkLK : ∀ i, finrank R (Ls i) = finrank R (Ks i) := fun i => by have := (hJT i).2.1; rwa [hc] at this
  have hK0 : scale Q (Ks i₀) = 1 := (hsc i₀) ▸ hU
  have hKi₁ : Ks i₁ ≤ L := hK.split.iSup_eq ▸ le_iSup Ks i₁
  set s₂ := scale Q (Ks i₁) with hs₂def
  have hs₂lt : s₂ < 1 := hK0 ▸ hK.scale_strictAnti (Fin.lt_def.2 (by omega))
  have hs₂R : ∀ z ∈ s₂, ∃ r ∈ maximalIdeal R, algebraMap R F r = z := fun z hz =>
    exists_max_of_lt_one (scale_fg Q (FG.of_le hfg hKi₁)) (hK.modular i₁).1 hs₂lt hz
  have hs₂R' : ∀ z ∈ s₂, ∃ r : R, algebraMap R F r = z := fun z hz => by
    obtain ⟨r, -, hr⟩ := hs₂R z hz; exact ⟨r, hr⟩
  set g₁ := fundNormGroup Q L Ls i₀ with hg₁def
  set g₂ := fundNormGroup Q L Ls i₁ with hg₂def
  have hg₂ : g₂ = normGroup Q (subA Q s₂ L) := by rw [hg₂def, hs₂def, ← hsc i₁]; rfl
  have hg₂₁ : g₂ ≤ g₁ := fundNormGroup_antitone Q hL (Fin.le_def.2 (by omega))
  -- the base `x` of `L₁`
  obtain ⟨e, he⟩ := hblk
  set x : Fin 4 → V := fun k => (e k : V) with hxdef
  have hrk4 : finrank R (Ls i₀) = 4 := by rw [finrank_eq_card_basis e, Fintype.card_fin]
  have hGx : ∀ k l, bil Q (x k) (x l) = blk2 a' 0 a'' 0 k l := fun k l => by
    have := congrFun (congrFun he k) l; simpa [gram] using this
  have hx00 : Q (x 0) = a' := by rw [← bil_self, hGx]; simp [blk2]
  have hx11 : Q (x 1) = 0 := by rw [← bil_self, hGx]; simp [blk2]
  have hx22 : Q (x 2) = a'' := by rw [← bil_self, hGx]; simp [blk2]
  have hx33 : Q (x 3) = 0 := by rw [← bil_self, hGx]; simp [blk2]
  have hx01 : bil Q (x 0) (x 1) = 1 := by rw [hGx]; simp [blk2]
  have hx23 : bil Q (x 2) (x 3) = 1 := by rw [hGx]; simp [blk2]
  have hx20 : bil Q (x 2) (x 0) = 0 := by rw [hGx]; simp [blk2]
  have hx21 : bil Q (x 2) (x 1) = 0 := by rw [hGx]; simp [blk2]
  have hx30 : bil Q (x 3) (x 0) = 0 := by rw [hGx]; simp [blk2]
  have hx31 : bil Q (x 3) (x 1) = 0 := by rw [hGx]; simp [blk2]
  -- `x_k = y_k + Y_k`
  have hLi : Ls i₀ ≤ L := hL.split.iSup_eq ▸ le_iSup Ls i₀
  have hdec : ∀ k, ∃ y ∈ Ks i₀, ∃ Y ∈ others Ks i₀, y + Y = x k := fun k =>
    mem_sup.mp ((sup_others Q hK.split i₀).symm ▸ hLi (e k).2)
  choose y hy Y hY hxy using hdec
  have hYsub : ∀ k, Y k ∈ subA Q s₂ L := fun k => mem_subA_of_others Q hK i₀ i₁ h₀ h₁ (hY k)
  have hyY : ∀ k l, bil Q (y k) (Y l) = 0 := fun k l => orth_others Q hK.split i₀ (hy k) (Y l) (hY l)
  have hB : ∀ k l, bil Q (x k) (x l) = bil Q (y k) (y l) + bil Q (Y k) (Y l) := by
    intro k l
    rw [← hxy k, ← hxy l, bil_add_left, bil_add_right, bil_add_right, hyY k l, bil_comm Q (Y k) (y l), hyY l k]
    ring
  have hQ : ∀ k, Q (x k) = Q (y k) + Q (Y k) := by
    intro k; rw [← hxy k, Q_add, hyY k k]; ring
  have hYY : ∀ k l, bil Q (Y k) (Y l) ∈ s₂ := fun k l => (hYsub k).2 _ (hYsub l).1
  have hQY : ∀ k, Q (Y k) ∈ g₂ := fun k => hg₂ ▸ Q_mem_normGroup Q (hYsub k)
  have hyR : ∀ {u v : V}, u ∈ Ks i₀ → v ∈ Ks i₀ → ∃ r : R, algebraMap R F r = bil Q u v := fun hu hv =>
    Submodule.mem_one.mp (hK0 ▸ bil_mem_scale Q hu hv)
  -- `B(y, l) ∈ 𝔬` for `y ∈ K₁`, `l ∈ L`
  have hyL : ∀ {u : V}, u ∈ Ks i₀ → ∀ l ∈ L, ∃ r : R, algebraMap R F r = bil Q u l := by
    intro u hu l hl
    rw [← sup_others Q hK.split i₀] at hl
    obtain ⟨k, hk, o, ho, rfl⟩ := mem_sup.mp hl
    rw [bil_add_right, orth_others Q hK.split i₀ hu o ho, add_zero]
    exact hyR hu hk
  -- `𝔤₁`, `𝔤₂` and the ideal `𝔣₁`
  have hfs₀ : Ls i₀ ≤ fundSub Q L Ls i₀ := le_fundSub Q hfg hL i₀
  have hxg : ∀ k, Q (x k) ∈ g₁ := fun k => Q_mem_normGroup Q (hfs₀ (e k).2)
  have hn : ∀ i, fundNormIdeal Q L Ls i = R ∙ a i := fun i => (ha i).2.symm
  have hf : fIdeal Q L Ls i₀ i₁ = fIdealOf R (R ∙ (1 : F)) g₁ g₂ (R ∙ a i₀) (R ∙ a i₁) := by
    rw [fIdeal, hU, hn, hn, Submodule.one_eq_span]
  have ha0 : ∀ i, a i ≠ 0 := fun i =>
    (ha i).ne_zero Q (isRegular_fundSub Q hfg hreg hL i) (fundSub_ne_bot Q hfg hL i)
  have hgA : ∀ i, ∀ z ∈ fundNormGroup Q L Ls i, z ∈ R ∙ a i := fun i z hz =>
    (ha i).2 ▸ normGroup_subset_normIdeal Q _ hz
  have haS : ∀ i, a i ∈ scale Q (Ls i) := fun i => by
    rw [← scale_fundSub Q hfg hL i]
    exact normIdeal_le_scale Q _ ((ha i).2 ▸ mem_span_singleton_self (a i))
  have hu₀ : 0 ≤ dord hπ (a i₀) := by
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hU ▸ haS i₀)
    rw [← hr]; exact dord_alg_nonneg hπ (by rintro rfl; exact ha0 i₀ (by rw [← hr, map_zero]))
  have hu₁ : 1 ≤ dord hπ (a i₁) := by
    obtain ⟨r, hrm, hr⟩ := hs₂R _ (hsc i₁ ▸ haS i₁)
    rw [← hr]; exact one_le_dord_of_max hπ hrm (hr ▸ ha0 i₁)
  have key : ∀ {c : R}, c ∈ maximalIdeal R → ∀ α ∈ g₁, ∀ β ∈ g₂,
      SqEquivMod (fIdeal Q L Ls i₀ i₁) ((1 - algebraMap R F c) ^ 2 + α * β) 1 := by
    intro c hcm α hα β hβ
    rw [hf]
    exact sqEquivMod_sq_add_mul hπ h2 (ha0 i₀) (ha0 i₁) (ha i₀).1 (ha i₁).1 (hgA i₀) (hgA i₁) hu₀ hu₁
      (fun z hz r => mul_sq_mem_normGroup Q hz ⟨r, rfl⟩) hcm hα hβ
  -- the first binary block `y₀, y₁`
  obtain ⟨c₁, hc₁m, hc₁⟩ := hs₂R _ (hYY 0 1)
  have hy01 : bil Q (y 0) (y 1) = 1 - algebraMap R F c₁ := by
    have := hB 0 1; rw [hx01] at this; rw [hc₁]; linear_combination -this
  have hy00 : Q (y 0) = a' - Q (Y 0) := by have := hQ 0; rw [hx00] at this; linear_combination -this
  have hy11 : Q (y 1) = -Q (Y 1) := by have := hQ 1; rw [hx11] at this; linear_combination -this
  have h12 : SqEquivMod (fIdeal Q L Ls i₀ i₁) (bil Q (y 0) (y 1) ^ 2 - Q (y 0) * Q (y 1)) 1 := by
    have := key hc₁m (a' - Q (Y 0)) (sub_mem (hx00 ▸ hxg 0) (hg₂₁ (hQY 0))) (Q (Y 1)) (hQY 1)
    convert this using 1; rw [hy01, hy00, hy11]; ring
  obtain ⟨⟨u₁₂, hu₁₂, hu₁₂'⟩, -⟩ := h12
  rw [mul_one] at hu₁₂'
  obtain ⟨A, hA⟩ := hyR (hy 0) (hy 0)
  obtain ⟨Bv, hBv⟩ := hyR (hy 0) (hy 1)
  obtain ⟨C, hC⟩ := hyR (hy 1) (hy 1)
  rw [bil_self] at hA hC
  have hunit : IsUnit (A * C - Bv ^ 2) := by
    have : A * C - Bv ^ 2 = -u₁₂ := IsFractionRing.injective R F (by
      rw [map_sub, map_mul, map_pow, map_neg, hA, hC, hBv, ← hu₁₂']; ring)
    rw [this]; exact hu₁₂.neg
  -- orthogonalize `y₂`, `y₃` against `y₀`, `y₁`
  have hps : ∀ k l, bil Q (x k) (x l) = 0 → bil Q (y k) (y l) ∈ s₂ := by
    intro k l h
    have := hB k l; rw [h] at this
    have : bil Q (y k) (y l) = -bil Q (Y k) (Y l) := by linear_combination -this
    rw [this]; exact neg_mem (hYY k l)
  obtain ⟨r₀, r₁, hr₀, hr₁, hv₂₀, hv₂₁⟩ := exists_orth_pair Q hA.symm hBv.symm hC.symm hunit
    (hps 2 0 hx20) (hps 2 1 hx21) hs₂R'
  obtain ⟨r₂, r₃, hr₂, hr₃, hv₃₀, hv₃₁⟩ := exists_orth_pair Q hA.symm hBv.symm hC.symm hunit
    (hps 3 0 hx30) (hps 3 1 hx31) hs₂R'
  set w₂ := r₀ • y 0 + r₁ • y 1 with hw₂
  set w₃ := r₂ • y 0 + r₃ • y 1 with hw₃
  set v₂ := y 2 + r₀ • y 0 + r₁ • y 1 with hv₂
  set v₃ := y 3 + r₂ • y 0 + r₃ • y 1 with hv₃
  have hv₂w : v₂ = y 2 + w₂ := by rw [hv₂, hw₂, add_assoc]
  have hv₃w : v₃ = y 3 + w₃ := by rw [hv₃, hw₃, add_assoc]
  have hwK : ∀ {r r' : R}, r • y 0 + r' • y 1 ∈ Ks i₀ := fun {r r'} =>
    add_mem (smul_mem _ r (hy 0)) (smul_mem _ r' (hy 1))
  have hwsub : ∀ {r r' : R}, algebraMap R F r ∈ s₂ → algebraMap R F r' ∈ s₂ →
      r • y 0 + r' • y 1 ∈ subA Q s₂ L := by
    intro r r' hr hr'
    refine ⟨(hK.split.iSup_eq ▸ le_iSup Ks i₀) hwK, fun l hl => ?_⟩
    obtain ⟨b₀, hb₀⟩ := hyL (hy 0) l hl
    obtain ⟨b₁, hb₁⟩ := hyL (hy 1) l hl
    rw [bil_add_left, bil_rsmul_left, bil_rsmul_left, ← hb₀, ← hb₁, mul_comm (algebraMap R F r),
      mul_comm (algebraMap R F r'), ← Algebra.smul_def, ← Algebra.smul_def]
    exact add_mem (smul_mem _ _ hr) (smul_mem _ _ hr')
  have hQv : ∀ {k : Fin 4} {r r' : R}, bil Q (y k + r • y 0 + r' • y 1) (y 0) = 0 →
      bil Q (y k + r • y 0 + r' • y 1) (y 1) = 0 →
      Q (y k + r • y 0 + r' • y 1) = Q (y k) - Q (r • y 0 + r' • y 1) := by
    intro k r r' h0 h1
    have hvw : bil Q (y k + r • y 0 + r' • y 1) (r • y 0 + r' • y 1) = 0 := by
      rw [bil_add_right, bil_rsmul_right, bil_rsmul_right, h0, h1]; ring
    have e1 : y k + r • y 0 + r' • y 1 = y k + (r • y 0 + r' • y 1) := by rw [add_assoc]
    rw [e1] at hvw ⊢
    rw [bil_add_left, bil_self] at hvw
    rw [Q_add]; linear_combination 2 * hvw
  have hQv₂ : Q v₂ = a'' - (Q (Y 2) + Q w₂) := by
    rw [hQv hv₂₀ hv₂₁]; have := hQ 2; rw [hx22] at this; linear_combination -this
  have hQv₃ : Q v₃ = -(Q (Y 3) + Q w₃) := by
    rw [hQv hv₃₀ hv₃₁]; have := hQ 3; rw [hx33] at this; linear_combination -this
  have hQw₂ : Q w₂ ∈ g₂ := hg₂ ▸ Q_mem_normGroup Q (hwsub hr₀ hr₁)
  have hQw₃ : Q w₃ ∈ g₂ := hg₂ ▸ Q_mem_normGroup Q (hwsub hr₂ hr₃)
  -- `B(v₂, v₃) = 1 - c₂` with `c₂ ∈ 𝔰₂`
  have hv₂w₃ : bil Q v₂ w₃ = 0 := by
    rw [hw₃, bil_add_right, bil_rsmul_right, bil_rsmul_right, hv₂₀, hv₂₁]; ring
  have hB₂₃ : bil Q v₂ v₃ = 1 - (bil Q (Y 2) (Y 3) - algebraMap R F r₀ * bil Q (y 0) (y 3) -
      algebraMap R F r₁ * bil Q (y 1) (y 3)) := by
    rw [hv₃w, bil_add_right, hv₂w₃, add_zero, hv₂, bil_add_left, bil_add_left, bil_rsmul_left, bil_rsmul_left]
    have := hB 2 3; rw [hx23] at this; linear_combination -this
  have hc₂s : bil Q (Y 2) (Y 3) - algebraMap R F r₀ * bil Q (y 0) (y 3) -
      algebraMap R F r₁ * bil Q (y 1) (y 3) ∈ s₂ := by
    obtain ⟨b₀, hb₀⟩ := hyR (hy 0) (hy 3)
    obtain ⟨b₁, hb₁⟩ := hyR (hy 1) (hy 3)
    rw [← hb₀, ← hb₁, mul_comm (algebraMap R F r₀), mul_comm (algebraMap R F r₁), ← Algebra.smul_def,
      ← Algebra.smul_def]
    exact sub_mem (sub_mem (hYY 2 3) (smul_mem _ _ hr₀)) (smul_mem _ _ hr₁)
  obtain ⟨c₂, hc₂m, hc₂⟩ := hs₂R _ hc₂s
  have h34 : SqEquivMod (fIdeal Q L Ls i₀ i₁) (bil Q v₂ v₃ ^ 2 - Q v₂ * Q v₃) 1 := by
    have := key hc₂m (a'' - (Q (Y 2) + Q w₂)) (sub_mem (hx22 ▸ hxg 2) (hg₂₁ (add_mem (hQY 2) hQw₂)))
      (Q (Y 3) + Q w₃) (add_mem (hQY 3) hQw₃)
    convert this using 1; rw [hB₂₃, hQv₂, hQv₃, hc₂]; ring
  have h12' : SqEquivMod (fIdeal Q L Ls i₀ i₁) (bil Q (y 0) (y 1) ^ 2 - Q (y 0) * Q (y 1)) 1 := by
    have := key hc₁m (a' - Q (Y 0)) (sub_mem (hx00 ▸ hxg 0) (hg₂₁ (hQY 0))) (Q (Y 1)) (hQY 1)
    convert this using 1; rw [hy01, hy00, hy11]; ring
  -- the base `y₀, y₁, v₂, v₃` of `K₁`
  have hv₂K : v₂ ∈ Ks i₀ := add_mem (add_mem (hy 2) (smul_mem _ _ (hy 0))) (smul_mem _ _ (hy 1))
  have hv₃K : v₃ ∈ Ks i₀ := add_mem (add_mem (hy 3) (smul_mem _ _ (hy 0))) (smul_mem _ _ (hy 1))
  set z : Fin 4 → V := ![y 0, y 1, v₂, v₃] with hz
  have hzK : ∀ k, z k ∈ Ks i₀ := by
    intro k; fin_cases k
    · exact hy 0
    · exact hy 1
    · exact hv₂K
    · exact hv₃K
  have hv₂y0 : bil Q (y 0) v₂ = 0 := by rw [bil_comm]; exact hv₂₀
  have hv₂y1 : bil Q (y 1) v₂ = 0 := by rw [bil_comm]; exact hv₂₁
  have hv₃y0 : bil Q (y 0) v₃ = 0 := by rw [bil_comm]; exact hv₃₀
  have hv₃y1 : bil Q (y 1) v₃ = 0 := by rw [bil_comm]; exact hv₃₁
  obtain ⟨D₂, hD₂⟩ := hyR hv₂K hv₂K
  obtain ⟨E₂, hE₂⟩ := hyR hv₂K hv₃K
  obtain ⟨F₂, hF₂⟩ := hyR hv₃K hv₃K
  rw [bil_self] at hD₂ hF₂
  set G : Matrix (Fin 4) (Fin 4) R := Matrix.of ![![A, Bv, 0, 0], ![Bv, C, 0, 0], ![0, 0, D₂, E₂], ![0, 0, E₂, F₂]]
    with hGdef
  have hgram : gram Q z = G.map (algebraMap R F) := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [gram, hz, hGdef, ← hA, ← hBv, ← hC, ← hD₂, ← hE₂, ← hF₂, bil_self, hv₂y0, hv₂y1, hv₃y0, hv₃y1,
        hv₂₀, hv₂₁, hv₃₀, hv₃₁, bil_comm Q (y 1) (y 0), bil_comm Q v₃ v₂]
  have hdetG : algebraMap R F G.det = (Q (y 0) * Q (y 1) - bil Q (y 0) (y 1) ^ 2) * (Q v₂ * Q v₃ - bil Q v₂ v₃ ^ 2) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hgram]
    have : gram Q z = Matrix.of ![![Q (y 0), bil Q (y 0) (y 1), 0, 0], ![bil Q (y 0) (y 1), Q (y 1), 0, 0],
        ![0, 0, Q v₂, bil Q v₂ v₃], ![0, 0, bil Q v₂ v₃, Q v₃]] := by
      rw [hgram]; ext k l
      fin_cases k <;> fin_cases l <;> simp [hGdef, hA, hBv, hC, hD₂, hE₂, hF₂]
    rw [this, det_two_blocks]
  obtain ⟨⟨u₃₄, hu₃₄, hu₃₄'⟩, -⟩ := h34
  rw [mul_one] at hu₃₄'
  have hGunit : IsUnit G.det := by
    have : G.det = u₁₂ * u₃₄ := IsFractionRing.injective R F (by
      rw [hdetG, map_mul, ← hu₁₂', ← hu₃₄']; ring)
    rw [this]; exact hu₁₂.mul hu₃₄
  have hKU : IsUnimodular Q (Ks i₀) := by have := hK.modular i₀; rw [hK0] at this; exact this
  have hrkK : finrank R (Ks i₀) = 4 := by rw [← hrkLK i₀, hrk4]
  obtain ⟨e', he'⟩ := exists_basis_of_gram_unit Q (FG.of_le hfg (hK.split.iSup_eq ▸ le_iSup Ks i₀)) hKU hrkK hzK
    hGunit hgram
  refine ⟨e.reindex (finCongr hrk4.symm), e'.reindex (finCongr hrkK.symm), ?_⟩
  rw [det_gram_reindex, det_gram_reindex, he, det_blk2]
  have hge' : (gram Q fun i => (e' i : V)) = gram Q z := by congr 1; funext i; exact he' i
  rw [hge', hgram, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdetG]
  have hprod := sqEquivMod_inv_one (sqEquivMod_mul_one h12' (show SqEquivMod (fIdeal Q L Ls i₀ i₁)
    (bil Q v₂ v₃ ^ 2 - Q v₂ * Q v₃) 1 from ⟨⟨u₃₄, hu₃₄, by rw [mul_one]; exact hu₃₄'⟩, by
      obtain ⟨-, h⟩ := key hc₂m (a'' - (Q (Y 2) + Q w₂)) (sub_mem (hx22 ▸ hxg 2) (hg₂₁ (add_mem (hQY 2) hQw₂)))
        (Q (Y 3) + Q w₃) (add_mem (hQY 3) hQw₃)
      convert h using 2; rw [hB₂₃, hQv₂, hQv₃, hc₂]; ring⟩))
  convert hprod using 1
  field_simp
  ring

end Base

end QuadFormsKB.OMeara.NecBase
