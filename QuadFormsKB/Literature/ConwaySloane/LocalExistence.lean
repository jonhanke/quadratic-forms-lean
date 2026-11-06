/-
# Conway–Sloane, Ch. 15, §7.7, Theorem 11 (local part): realizing prescribed $p$-adic symbols

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.7, Thm. 11, p. 383
(`conwaysloane1999`). The local half of Theorem 11: a putative $p$-adic symbol whose Jordan constituents all satisfy the
existence conditions (31) (odd $p$) or (32)–(35) ($p = 2$) is the symbol of an integral form over $\mathbb Z_p$.

**Formalization.** Constituent by constituent. For $p = 2$ a factor $q_t^{\varepsilon n}$ satisfying (32)–(35) is
realized by an explicit list of Cassels blocks (`DyBlock`) of exponent $k$ ($q = 2^k$): type II, $n = 2m$, by
$m - 1$ blocks $2^k\cdot 2xy$ and one further block $2^k\cdot 2xy$ ($\varepsilon = +$) or $2^k(2x^2 + 2xy + 2y^2)$
($\varepsilon = -$); type I by $n$ blocks $2^ku_ix^2$, $u_i \in \{1,3,5,7\}$, with $\sum u_i \equiv t \pmod 8$ and
$\prod\left(\frac{u_i}{2}\right) = \varepsilon$ (for $n \ge 3$: $n - 3$ units $1$ and a triple). For odd $p$ the factor
$q^{\varepsilon n}$ is realized by $n - 1$ entries $p^k$ and one entry $p^k$ or $p^kr$, $r$ a fixed non-residue unit.

**Defines** `UnitSpec`, `unitsOf`, `twoBlocks` (the blocks of one constituent), `twoRealization` (the blocks of a whole
symbol).

**Proves**
* `symOf_twoBlocks`: if $f$ satisfies (32)–(35), the blocks of `twoBlocks k f` have the 2-adic symbol $f$ at scale
  $2^k$ and are trivial elsewhere (`blockSymbol_twoBlocks`);
* `blockSymbol_twoRealization`, `exists_form_of_twoSymbol`: every 2-adic symbol supported below $N$ with
  all constituents satisfying (32)–(35) is the 2-adic symbol of a form over $\mathbb Z_2$;
* `exists_diag_of_oddSymbol`, `exists_form_of_oddSymbol`: the same for odd $p$ with (31).
-/
import QuadFormsKB.Literature.ConwaySloane.TwoAdicForm
import QuadFormsKB.Literature.ConwaySloane.OddClassification

namespace QuadFormsKB.ConwaySloane

open Cassels Finset

/-! ### Units realizing a 2-adic type I constituent -/

theorem Sign.prodList_append (l₁ l₂ : List Sign) :
    Sign.prodList (l₁ ++ l₂) = (Sign.prodList l₁).mul (Sign.prodList l₂) := by
  induction l₁ with
  | nil => cases h : Sign.prodList l₂ <;> simp [Sign.prodList, Sign.mul, h]
  | cons s l ih =>
    simp only [List.cons_append, Sign.prodList, ih]
    cases s <;> cases Sign.prodList l <;> cases Sign.prodList l₂ <;> rfl

theorem Sign.mul_plus (x : Sign) : x.mul .plus = x := by cases x <;> rfl

theorem Sign.prodList_replicate_plus (m : ℕ) : Sign.prodList (List.replicate m .plus) = .plus := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, Sign.prodList, ih, Sign.mul]

/-- One unit realizing $q_t^{\varepsilon 1}$ (33). -/
theorem units_one : ∀ (s : Sign) (t : ZMod 8),
    ((s = .plus → t = 1 ∨ t = 7) ∧ (s = .minus → t = 3 ∨ t = 5)) →
    ∃ u ∈ ([1, 3, 5, 7] : List ℤ), (u : ZMod 8) = t ∧ jacobiTwo u = s := by
  intro s; cases s <;> decide

/-- Two units realizing $q_t^{\varepsilon 2}$ of type I (34). -/
theorem units_two : ∀ (s : Sign) (t : ZMod 8),
    ((s = .plus → t = 0 ∨ t = 2 ∨ t = 6) ∧ (s = .minus → t = 4 ∨ t = 2 ∨ t = 6)) →
    ∃ u ∈ ([1, 3, 5, 7] : List ℤ), ∃ v ∈ ([1, 3, 5, 7] : List ℤ),
      (u : ZMod 8) + (v : ZMod 8) = t ∧ (jacobiTwo u).mul (jacobiTwo v) = s := by
  intro s; cases s <;> decide

/-- Three units with any prescribed sign and any prescribed odd sum. -/
theorem units_three : ∀ r < 8, ∀ (s : Sign) (t : ZMod 8), t.val % 2 = (r + 1) % 2 →
    ∃ a ∈ ([1, 3, 5, 7] : List ℤ), ∃ b ∈ ([1, 3, 5, 7] : List ℤ), ∃ c ∈ ([1, 3, 5, 7] : List ℤ),
      (a : ZMod 8) + b + c = t - (r : ZMod 8) ∧ (jacobiTwo a).mul ((jacobiTwo b).mul (jacobiTwo c)) = s := by
  intro r hr s; cases s <;> revert r <;> decide

/-- The specification of the units of a type I constituent: $n$ units in $\{1,3,5,7\}$ with sum $t$ in $\mathbb Z/8$ and
product of the signs $\left(\frac{u_i}{2}\right)$ equal to $\varepsilon$. -/
def UnitSpec (f : TwoFactor) (L : List ℤ) : Prop :=
  L.length = f.dim ∧ (∀ u ∈ L, u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) ∧
    (L.map (Int.cast : ℤ → ZMod 8)).sum = f.oddity ∧ Sign.prodList (L.map jacobiTwo) = f.sign

/-- A constituent satisfying (32)–(35) of type I has a list of units realizing it. -/
theorem exists_units {f : TwoFactor} (h : f.Exists) (hI : f.type = .I) : ∃ L, UnitSpec f L := by
  obtain ⟨n, s, ty, o⟩ := f
  simp only at hI; subst hI
  obtain ⟨d0, d1, d2, hpar, -⟩ := h
  simp only at d0 d1 d2 hpar
  rcases n with _ | _ | _ | m
  · exact absurd (d0 rfl).1 (by decide)
  · obtain ⟨u, hu, h1, h2⟩ := units_one s o (d1 rfl)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    refine ⟨[u], rfl, ?_, ?_, ?_⟩
    · simpa using hu
    · simpa using h1
    · simpa [Sign.prodList, Sign.mul_plus] using h2
  · obtain ⟨u, hu, v, hv, h1, h2⟩ := units_two s o (d2 rfl trivial)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    refine ⟨[u, v], rfl, ?_, ?_, ?_⟩
    · simpa using ⟨hu, hv⟩
    · simpa using h1
    · simpa [Sign.prodList, Sign.mul_plus] using h2
  · obtain ⟨a, ha, b, hb, c, hc, h1, h2⟩ := units_three (m % 8) (Nat.mod_lt _ (by norm_num)) s o (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
    have hm : (((m % 8 : ℕ)) : ZMod 8) = (m : ZMod 8) := ZMod.natCast_mod m 8
    rw [hm] at h1
    refine ⟨[a, b, c] ++ List.replicate m 1, ?_, ?_, ?_, ?_⟩
    · simp
    · intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_replicate] at hx
      rcases hx with (rfl | rfl | rfl) | ⟨-, rfl⟩
      · exact ha
      · exact hb
      · exact hc
      · simp
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.map_replicate, List.sum_replicate]
      simp only [Int.cast_one, nsmul_eq_mul, mul_one]
      linear_combination h1
    · rw [List.map_append, Sign.prodList_append]
      have hj : jacobiTwo 1 = .plus := by decide
      simp only [List.map_cons, List.map_nil, Sign.prodList, List.map_replicate, hj,
        Sign.prodList_replicate_plus]
      simp only [Sign.mul_plus]
      exact h2

open Classical in
/-- A chosen list of units realizing the type I constituent $f$ (empty if there is none). -/
noncomputable def unitsOf (f : TwoFactor) : List ℤ := if h : ∃ L, UnitSpec f L then h.choose else []

theorem unitsOf_spec {f : TwoFactor} (h : f.Exists) (hI : f.type = .I) : UnitSpec f (unitsOf f) := by
  classical
  have h' := exists_units h hI
  unfold unitsOf
  rw [dite_eq_left_of_eq_true (eq_true h')]
  exact h'.choose_spec

/-! ### The blocks of one constituent -/

/-- The binary block of scale $2^k$ closing a type II constituent: $2^k\cdot 2xy$ for $\varepsilon = +$,
$2^k(2x^2 + 2xy + 2y^2)$ for $\varepsilon = -$. -/
def binBlock (k : ℕ) : Sign → DyBlock
  | .plus => DyBlock.hyp (k : ℤ)
  | .minus => DyBlock.ell (k : ℤ)

/-- **The blocks realizing a 2-adic constituent** $f$ at scale $2^k$ (Conway–Sloane, §7.7, p. 383, proof of Thm. 11):
nothing if $n = 0$; for type II, $n = 2m$: one block $2^k\cdot 2xy$ ($\varepsilon = +$) or
$2^k(2x^2 + 2xy + 2y^2)$ ($\varepsilon = -$) and $m - 1$ blocks $2^k\cdot 2xy$; for type I the blocks $2^ku_ix^2$ for
the units `unitsOf f`. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, Thm. 11, p. 383 (local part)"]
noncomputable def twoBlocks (k : ℕ) (f : TwoFactor) : List DyBlock :=
  if f.dim = 0 then [] else
  match f.type with
  | .II => binBlock k f.sign ::
      List.replicate (f.dim / 2 - 1) (DyBlock.hyp (k : ℤ))
  | .I => (unitsOf f).map (DyBlock.sq (k : ℤ))

/-- The factor of the constituent made of the list of blocks `B`: the symbol of `B` at its own scale. -/
def symOf (B : List DyBlock) : TwoFactor :=
  { dim := (B.map DyBlock.dim).sum
    sign := Sign.prodList (B.map blockSign)
    type := if B.any fun b => decide (IsSqBlock b) then .I else .II
    oddity := (B.map blockOddity).sum }

theorem blockSymbol_apply (D : List DyBlock) (k : ℕ) :
    blockSymbol D k = symOf (D.filter fun b => blockExp b = k) := rfl

theorem twoBlocks_exp (k : ℕ) (f : TwoFactor) : ∀ b ∈ twoBlocks k f, blockExp b = k := by
  intro b hb
  unfold twoBlocks at hb
  split_ifs at hb with h0
  · simp at hb
  · cases ht : f.type <;> rw [ht] at hb <;> simp only at hb
    · simp only [List.mem_map] at hb
      obtain ⟨u, -, rfl⟩ := hb
      rfl
    · simp only [List.mem_cons, List.mem_replicate] at hb
      rcases hb with rfl | ⟨-, rfl⟩
      · cases f.sign <;> rfl
      · rfl

theorem twoBlocks_valid {f : TwoFactor} (h : f.Exists) (k : ℕ) : ∀ b ∈ twoBlocks k f, b.Valid := by
  intro b hb
  unfold twoBlocks at hb
  split_ifs at hb with h0
  · simp at hb
  · cases ht : f.type <;> rw [ht] at hb <;> simp only at hb
    · simp only [List.mem_map] at hb
      obtain ⟨u, hu, rfl⟩ := hb
      exact (unitsOf_spec h ht).2.1 u hu
    · simp only [List.mem_cons, List.mem_replicate] at hb
      rcases hb with rfl | ⟨-, rfl⟩
      · cases f.sign <;> trivial
      · trivial

theorem symOf_map_sq (k : ℤ) (L : List ℤ) :
    symOf (L.map (DyBlock.sq k)) =
      ⟨L.length, Sign.prodList (L.map jacobiTwo), if L = [] then .II else .I,
        (L.map (Int.cast : ℤ → ZMod 8)).sum⟩ := by
  unfold symOf
  have h1 : ((L.map (DyBlock.sq k)).map DyBlock.dim).sum = L.length := by
    induction L with
    | nil => rfl
    | cons a l ih => simp_all [DyBlock.dim, add_comm]
  have h2 : Sign.prodList ((L.map (DyBlock.sq k)).map blockSign) = Sign.prodList (L.map jacobiTwo) := by
    simp [List.map_map, Function.comp_def, blockSign]
  have h3 : ((L.map (DyBlock.sq k)).map blockOddity).sum = (L.map (Int.cast : ℤ → ZMod 8)).sum := by
    simp [List.map_map, Function.comp_def, blockOddity]
  have h4 : ((L.map (DyBlock.sq k)).any fun b => decide (IsSqBlock b)) = !L.isEmpty := by
    cases L <;> simp [IsSqBlock]
  rw [h1, h2, h3, h4]
  cases L <;> simp

/-- **One constituent** (Conway–Sloane, §7.7, p. 383): if $f$ satisfies (32)–(35), the blocks `twoBlocks k f` have
symbol $f$ (at their own scale). -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, Thm. 11, p. 383 (local part)"]
theorem symOf_twoBlocks {f : TwoFactor} (h : f.Exists) (k : ℕ) : symOf (twoBlocks k f) = f := by
  obtain ⟨n, s, ty, o⟩ := f
  have hspec := fun hI => @unitsOf_spec ⟨n, s, ty, o⟩ h hI
  obtain ⟨d0, d1, d2, hpar, hII⟩ := h
  simp only at d0 d1 d2 hpar hII hspec
  by_cases h0 : n = 0
  · subst h0
    obtain ⟨rfl, rfl⟩ := d0 rfl
    have : o = 0 := hII rfl
    subst this
    simp [twoBlocks, symOf, Sign.prodList]
  · cases ty
    · have hL := hspec rfl
      unfold twoBlocks
      simp only [h0, ↓reduceIte]
      rw [symOf_map_sq]
      obtain ⟨hl, -, ho, hs⟩ := hL
      have hne : unitsOf ⟨n, s, .I, o⟩ ≠ [] := by
        intro he; rw [he] at hl; simp at hl; omega
      simp only [hne, ↓reduceIte, TwoFactor.mk.injEq]
      exact ⟨hl, hs, trivial, ho⟩
    · have ho : o = 0 := hII rfl
      subst ho
      have hev : n % 2 = 0 := by simpa using hpar.symm
      unfold twoBlocks
      simp only [h0, ↓reduceIte]
      unfold symOf
      cases s
      · simp [binBlock, blockSign, blockOddity, IsSqBlock, DyBlock.dim, List.map_replicate, Sign.prodList,
          Sign.prodList_replicate_plus, Sign.mul, List.sum_replicate]
        omega
      · simp [binBlock, blockSign, blockOddity, IsSqBlock, DyBlock.dim, List.map_replicate, Sign.prodList,
          Sign.prodList_replicate_plus, Sign.mul, Sign.flip, List.sum_replicate]
        omega

/-! ### A whole 2-adic symbol -/

/-- **The blocks realizing a 2-adic symbol** $\sigma$ supported below $N$: the concatenation of `twoBlocks k (σ k)` over
$k < N$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, Thm. 11, p. 383 (local part)"]
noncomputable def twoRealization (σ : TwoSymbol) : ℕ → List DyBlock
  | 0 => []
  | N + 1 => twoRealization σ N ++ twoBlocks N (σ N)

theorem filter_twoRealization (σ : TwoSymbol) (N k : ℕ) :
    (twoRealization σ N).filter (fun b => blockExp b = k) = if k < N then twoBlocks k (σ k) else [] := by
  induction N with
  | zero => simp [twoRealization]
  | succ N ih =>
    simp only [twoRealization, List.filter_append, ih]
    by_cases hk : k = N
    · subst hk
      have : (twoBlocks k (σ k)).filter (fun b => blockExp b = k) = twoBlocks k (σ k) := by
        rw [List.filter_eq_self]
        intro b hb; simpa using twoBlocks_exp k _ b hb
      simp [this]
    · have : (twoBlocks N (σ N)).filter (fun b => blockExp b = k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb; have := twoBlocks_exp N _ b hb
        simp [this]; omega
      rw [this]
      by_cases hlt : k < N
      · simp [hlt, show k < N + 1 by omega]
      · simp [hlt, show ¬ k < N + 1 by omega]

/-- **Constituents of a realization**: at scale $2^k$ the symbol of `twoBlocks`-realization is $f$ if $k$ is the
scale, and trivial elsewhere. -/
theorem blockSymbol_twoBlocks {f : TwoFactor} (h : f.Exists) (k j : ℕ) :
    blockSymbol (twoBlocks k f) j = if j = k then f else TwoFactor.trivial := by
  rw [blockSymbol_apply]
  by_cases hj : j = k
  · subst hj
    rw [List.filter_eq_self.2 (fun b hb => by simpa using twoBlocks_exp j f b hb)]
    simp [symOf_twoBlocks h]
  · rw [List.filter_eq_nil_iff.2 (fun b hb => by have := twoBlocks_exp k f b hb; simp [this]; omega)]
    simp [hj]
    rfl

/-- The blocks of the realization of a 2-adic symbol (supported below $N$, every constituent satisfying (32)–(35))
have exactly that symbol. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, Thm. 11, p. 383 (local part)"]
theorem blockSymbol_twoRealization {σ : TwoSymbol} {N : ℕ} (hσ : σ.SupportedBelow N)
    (hex : ∀ k, (σ k).Exists) : blockSymbol (twoRealization σ N) = σ := by
  funext k
  rw [blockSymbol_apply, filter_twoRealization]
  split_ifs with hk
  · exact symOf_twoBlocks (hex k) k
  · rw [hσ k (by omega)]; rfl

theorem twoRealization_valid {σ : TwoSymbol} (hex : ∀ k, (σ k).Exists) (N : ℕ) :
    ∀ b ∈ twoRealization σ N, b.Valid := by
  induction N with
  | zero => simp [twoRealization]
  | succ N ih =>
    intro b hb
    simp only [twoRealization, List.mem_append] at hb
    rcases hb with hb | hb
    · exact ih b hb
    · exact twoBlocks_valid (hex N) N b hb

theorem twoRealization_exp (σ : TwoSymbol) (N : ℕ) : ∀ b ∈ twoRealization σ N, 0 ≤ blockExp b := by
  induction N with
  | zero => simp [twoRealization]
  | succ N ih =>
    intro b hb
    simp only [twoRealization, List.mem_append] at hb
    rcases hb with hb | hb
    · exact ih b hb
    · rw [twoBlocks_exp N _ b hb]; exact Int.natCast_nonneg _

theorem dyDim_eq_sum (D : List DyBlock) : dyDim D = (D.map DyBlock.dim).sum := by
  induction D with
  | nil => rfl
  | cons b D ih => simp [dyDim, ih]

theorem dyDim_twoRealization {σ : TwoSymbol} (hex : ∀ k, (σ k).Exists) (N : ℕ) :
    dyDim (twoRealization σ N) = ∑ k ∈ range N, (σ k).dim := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [dyDim_eq_sum] at ih ⊢
    simp only [twoRealization, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    congr 1
    exact congrArg TwoFactor.dim (symOf_twoBlocks (hex N) N)

/-- **Theorem 11, local part at $p = 2$** (Conway–Sloane, §7.7, p. 383): a 2-adic symbol $\sigma$ supported below $N$
whose constituents all satisfy (32)–(35) is the 2-adic symbol of an integral form over $\mathbb Z_2$ in
$\sum_{k < N} n_{2^k}$ variables (namely the orthogonal sum of the blocks `twoRealization σ N`). -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, Thm. 11, p. 383 (local part)"]
theorem exists_form_of_twoSymbol {σ : TwoSymbol} {N : ℕ} (hσ : σ.SupportedBelow N)
    (hex : ∀ k, (σ k).Exists) :
    ∃ F : Matrix (Fin (∑ k ∈ range N, (σ k).dim)) (Fin (∑ k ∈ range N, (σ k).dim)) ℚ_[2],
      IsTwoSymbolOf F σ := by
  have hd := dyDim_twoRealization hex N
  exact ⟨(dyMat (twoRealization σ N)).submatrix (Fin.cast hd.symm) (Fin.cast hd.symm),
    twoRealization σ N, twoRealization_valid hex N, twoRealization_exp σ N, hd, ZpEquiv.refl _,
    (blockSymbol_twoRealization hσ hex).symm⟩

/-! ### Odd primes -/

section Odd

/-- The index set of the diagonal entries realizing a symbol: pairs $(k, j)$, $k < N$, $j < n_{p^k}$. -/
abbrev OddIdx (σ : OddSymbol) (N : ℕ) : Type := Σ k : Fin N, Fin (σ k).dim

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Theorem 11, local part at an odd prime** (Conway–Sloane, §7.7, p. 383): a $p$-adic symbol $\sigma$ supported
below $N$ whose constituents satisfy (31) is the symbol of a diagonal form $\operatorname{diag}(p^{z_i}u_i)$ with
$\sum_{k<N}n_{p^k}$ entries, $z_i < N$ and unit entries $u_i \in \{1, r\}$, $r$ a fixed quadratic non-residue unit. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, Thm. 11, p. 383 (local part)"]
theorem exists_diag_of_oddSymbol_of (r : ℚ_[p]) (hr1 : ‖r‖ = 1) (hr : ¬ IsSquare r) {σ : OddSymbol} {N : ℕ}
    (hσ : σ.SupportedBelow N) (hex : ∀ k, (σ k).Exists) :
    ∃ (n : ℕ) (z : Fin n → ℕ) (u : Fin n → ℚ_[p]),
      n = ∑ k ∈ range N, (σ k).dim ∧ (∀ i, z i < N) ∧ (∀ i, u i = 1 ∨ u i = r) ∧
      oddSymbolOfDiag p z u = σ := by
  classical
  let w : OddIdx σ N → ℚ_[p] := fun x => if x.2.val = 0 ∧ (σ x.1).sign = .minus then r else 1
  let e : Fin (Fintype.card (OddIdx σ N)) ≃ OddIdx σ N := (Fintype.equivFin (OddIdx σ N)).symm
  refine ⟨Fintype.card (OddIdx σ N), fun i => (e i).1.val, fun i => w (e i), ?_, ?_, ?_, ?_⟩
  · simp only [OddIdx, Fintype.card_sigma, Fintype.card_fin]
    exact Fin.sum_univ_eq_sum_range (fun k => (σ k).dim) N
  · intro i; exact (e i).1.isLt
  · intro i; simp only [w]; split_ifs <;> simp
  · funext k
    unfold oddSymbolOfDiag
    have hcard : Fintype.card {i : Fin (Fintype.card (OddIdx σ N)) // (e i).1.val = k} =
        (univ.filter fun x : OddIdx σ N => x.1.val = k).card := by
      rw [← Fintype.card_subtype]
      exact Fintype.card_congr (e.subtypeEquiv fun _ => Iff.rfl)
    have hprod : ∏ i : {i : Fin (Fintype.card (OddIdx σ N)) // (e i).1.val = k}, w (e i) =
        ∏ x ∈ (univ.filter fun x : OddIdx σ N => x.1.val = k), w x := by
      have h1 : ∏ x ∈ (univ.filter fun x : OddIdx σ N => x.1.val = k), w x =
          ∏ x : {x : OddIdx σ N // x.1.val = k}, w x.1 :=
        Finset.prod_subtype _ (fun x => by simp) (fun x => w x)
      rw [h1]
      exact Fintype.prod_equiv (e.subtypeEquiv (q := fun x : OddIdx σ N => x.1.val = k) fun _ => Iff.rfl) (fun i => w (e i.1)) (fun x => w x.1)
        (fun _ => rfl)
    rw [hprod]
    by_cases hk : k < N
    · have hS : (univ.filter fun x : OddIdx σ N => x.1.val = k) =
          ({⟨k, hk⟩} : Finset (Fin N)).sigma (fun a => (univ : Finset (Fin (σ a).dim))) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma, Finset.mem_singleton, and_true,
          Fin.ext_iff]
      have hw : ∏ b : Fin (σ k).dim, w ⟨⟨k, hk⟩, b⟩ = if (σ k).sign = .minus then r else 1 := by
        cases hs : (σ k).sign
        · simp [w, hs]
        · have hd : 0 < (σ k).dim := by
            by_contra h0
            have := hex k (by omega)
            rw [hs] at this
            cases this
          rw [Finset.prod_eq_single (⟨0, hd⟩ : Fin (σ k).dim)]
          · simp [w, hs]
          · intro b _ hb; simp [w, hs]; intro h; exact (hb (Fin.ext h)).elim
          · simp
      rw [hcard, hS, Finset.card_sigma, Finset.prod_sigma]
      simp only [Finset.prod_singleton, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin]
      rw [hw]
      suffices h : (if IsSquare (if (σ k).sign = .minus then r else 1) then Sign.plus else Sign.minus) =
          (σ k).sign by simp only [h]
      cases hs : (σ k).sign
      · simp
      · simp [hr]
    · have hS : (univ.filter fun x : OddIdx σ N => x.1.val = k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x _
        have := x.1.isLt
        omega
      rw [hcard, hS, hσ k (by omega)]
      simp [OddFactor.trivial]

/-- **Theorem 11, local part at an odd prime** (as `exists_diag_of_oddSymbol_of`, for some non-residue unit $r$). -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, Thm. 11, p. 383 (local part)"]
theorem exists_diag_of_oddSymbol (hp2 : p ≠ 2) {σ : OddSymbol} {N : ℕ} (hσ : σ.SupportedBelow N)
    (hex : ∀ k, (σ k).Exists) :
    ∃ (r : ℚ_[p]) (n : ℕ) (z : Fin n → ℕ) (u : Fin n → ℚ_[p]), ‖r‖ = 1 ∧ ¬ IsSquare r ∧
      n = ∑ k ∈ range N, (σ k).dim ∧ (∀ i, z i < N) ∧ (∀ i, u i = 1 ∨ u i = r) ∧
      oddSymbolOfDiag p z u = σ := by
  obtain ⟨r, hr1, hr⟩ := exists_nonsq_unit hp2
  obtain ⟨n, z, u, h⟩ := exists_diag_of_oddSymbol_of r hr1 hr hσ hex
  exact ⟨r, n, z, u, hr1, hr, h⟩

/-- **Theorem 11, local part at an odd prime, as a form** (Conway–Sloane, §7.7, p. 383): a $p$-adic symbol supported
below $N$ whose constituents satisfy (31) is the $p$-adic symbol of an integral form over $\mathbb Z_p$ in
$\sum_{k<N}n_{p^k}$ variables (a diagonal form $\operatorname{diag}(p^{z_i}u_i)$). -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, Thm. 11, p. 383 (local part)"]
theorem exists_form_of_oddSymbol (hp2 : p ≠ 2) {σ : OddSymbol} {N : ℕ} (hσ : σ.SupportedBelow N)
    (hex : ∀ k, (σ k).Exists) :
    ∃ F : Matrix (Fin (∑ k ∈ range N, (σ k).dim)) (Fin (∑ k ∈ range N, (σ k).dim)) ℚ_[p],
      IsOddSymbolOf p F σ := by
  obtain ⟨r, n, z, u, hr1, -, hn, -, hu, hs⟩ := exists_diag_of_oddSymbol hp2 hσ hex
  subst hn
  refine ⟨Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * u i, z, u, ?_, ZpEquiv.refl _, hs.symm⟩
  intro i
  rcases hu i with h | h <;> simp [h, hr1]

end Odd

/-! ### Necessity: the realizable constituents are exactly those satisfying (32)–(35) -/

theorem zmod8_val_add_mod_two : ∀ a b : ZMod 8, (a + b).val % 2 = (a.val + b.val) % 2 := by decide

theorem dyBlock_one_le_dim (b : DyBlock) : 1 ≤ b.dim := by cases b <;> simp [DyBlock.dim]

theorem oddity_parity (B : List DyBlock) (hB : ∀ b ∈ B, b.Valid) :
    (B.map blockOddity).sum.val % 2 = (B.map DyBlock.dim).sum % 2 := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    have ih := ih (fun x hx => hB x (List.mem_cons_of_mem _ hx))
    have hb := hB b List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    rw [zmod8_val_add_mod_two]
    cases b with
    | sq e u =>
      have h1 : (blockOddity (DyBlock.sq e u)).val % 2 = 1 := by
        show ((u : ℤ) : ZMod 8).val % 2 = 1
        simp only [DyBlock.Valid] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> decide
      simp only [DyBlock.dim]
      omega
    | hyp e => simp only [blockOddity, DyBlock.dim]; simp at ih ⊢; omega
    | ell e => simp only [blockOddity, DyBlock.dim]; simp at ih ⊢; omega

theorem oddity_of_typeII (B : List DyBlock) (h : (B.any fun b => decide (IsSqBlock b)) = false) :
    (B.map blockOddity).sum = 0 := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    have hb : blockOddity b = 0 := by cases b <;> simp_all [blockOddity, IsSqBlock]
    simp [List.map_cons, List.sum_cons, hb, ih h.2]

/-- **Necessity** (Conway–Sloane, §7.7, (32)–(35), p. 383): every constituent of a block decomposition with valid blocks
satisfies the existence conditions. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (32)–(35), p. 383"]
theorem symOf_exists (B : List DyBlock) (hB : ∀ b ∈ B, b.Valid) : (symOf B).Exists := by
  by_cases hd : (symOf B).dim ≤ 2
  · rcases B with _ | ⟨b, _ | ⟨c, _ | ⟨d, B⟩⟩⟩
    · decide
    · rcases b with ⟨e, u⟩ | e | e
      · have h : symOf [DyBlock.sq e u] =
            ⟨1 + 0, (jacobiTwo u).mul .plus, .I, (u : ZMod 8) + 0⟩ := rfl
        rw [h]
        have hu := hB _ List.mem_cons_self
        simp only [DyBlock.Valid] at hu
        rcases hu with rfl | rfl | rfl | rfl <;> decide
      · have h : symOf [DyBlock.hyp e] = ⟨2 + 0, Sign.plus.mul .plus, .II, 0 + 0⟩ := rfl
        rw [h]; decide
      · have h : symOf [DyBlock.ell e] = ⟨2 + 0, Sign.minus.mul .plus, .II, 0 + 0⟩ := rfl
        rw [h]; decide
    · rcases b with ⟨e, u⟩ | e | e <;> rcases c with ⟨e', v⟩ | e' | e'
      · have h : symOf [DyBlock.sq e u, DyBlock.sq e' v] =
            ⟨1 + (1 + 0), (jacobiTwo u).mul ((jacobiTwo v).mul .plus), .I, (u : ZMod 8) + ((v : ZMod 8) + 0)⟩ :=
          rfl
        rw [h]
        have hu := hB _ List.mem_cons_self
        have hv := hB (DyBlock.sq e' v) (by simp)
        simp only [DyBlock.Valid] at hu hv
        rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> decide
      all_goals (exfalso; simp [symOf, DyBlock.dim] at hd)
    · exfalso
      have := dyBlock_one_le_dim b
      have := dyBlock_one_le_dim c
      have := dyBlock_one_le_dim d
      simp only [symOf, List.map_cons, List.sum_cons] at hd
      omega
  · refine ⟨fun h => by omega, fun h => by omega, fun h => by omega, oddity_parity B hB, ?_⟩
    intro ht
    have : (B.any fun b => decide (IsSqBlock b)) = false := by
      by_contra hc
      have hc' : (B.any fun b => decide (IsSqBlock b)) = true := by simpa using hc
      simp [symOf, hc'] at ht
    exact oddity_of_typeII B this

/-- **Every constituent of a block decomposition exists** (Conway–Sloane, §7.7, (32)–(35), p. 383): with
`twoRealization` this shows (32)–(35) are exactly the conditions for a 2-adic constituent to occur. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (32)–(35), p. 383"]
theorem blockSymbol_exists (D : List DyBlock) (hD : ∀ b ∈ D, b.Valid) (k : ℕ) :
    (blockSymbol D k).Exists :=
  symOf_exists _ (fun b hb => hD b (List.mem_filter.1 hb).1)

end QuadFormsKB.ConwaySloane
