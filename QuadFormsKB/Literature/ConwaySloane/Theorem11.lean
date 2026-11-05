/-
# Conway–Sloane, Ch. 15, §7.7, Theorem 11: existence of a global form with prescribed local symbols

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.7, Thm. 11, p. 383
(`conwaysloane1999`). Theorem 11: a putative system of local symbols (dimension $n$, determinant $d$, the
$(-1)$-adic symbol $+^r-^s$, a $p$-adic symbol for every prime $p$) satisfying the conditions (29)–(35) of §7.7 is the
system of symbols of an integral quadratic form. The book gives no proof ("No proofs will be offered", p. 378).

**Route.** The local half is `LocalExistence.lean`: every symbol whose
constituents satisfy (31)–(35) is the symbol of a $\mathbb Z_p$-form. For the global half:
1. at every place $v$ the local realization is $\mathbb Q_v$-equivalent to an explicit *integer diagonal* form
   $\alpha_v$ ($\operatorname{diag}(p^{z_i}w_i)$ at odd $p$; at $2$ each Cassels block
   $2^eux^2$, $2^e\cdot 2xy$, $2^e(2x^2+2xy+2y^2)$ is replaced by $\langle 2^eu\rangle$, $\langle 2^e, -2^e\rangle$,
   $\langle 2^{e+1}, 3\cdot 2^{e+1}\rangle$; at $\infty$, $\langle 1^r, (-1)^s\rangle$);
2. the excesses of $\alpha_v$ are the excesses read off the symbol (§7.7, p. 383), so by the relation between the
   excesses and the Hasse invariants (`pExcess_eq_hasse`, `oddity_eq_hasse`, `signature_eq_hasse`) the oddity
   formula (30) says that the number of places with Hasse invariant $-1$ is even, and (with (29)) that the
   determinant of $\alpha_2$ is $d$ up to a $2$-adic unit square;
3. Cassels Ch. 6, Thm. 1.3 (`Cassels.exists_form_of_local`) gives a rational form with these local classes, and Cassels
   Ch. 9, Thm. 1.2 (`Siegel.exists_form_of_local_forms`) an integral form $\mathbb Z_p$-equivalent to the local
   realizations.
Hilbert reciprocity enters only through the oddity formula and Cassels Ch. 6 (reciprocity is used only where
the global statement needs it).

**Defines** `GenusSymbolData.IsSymbolsOf` (a symbol system is that of the integral form with Gram matrix $A$), the
integer diagonal models `dyDiag`, `realVec`, `placeVec`, the integer Gram matrix `dyMatInt` of a block decomposition.

**Proves**
* `theorem11` (**Theorem 11**, unconditional): every system satisfying (29)–(35) is the system of symbols of an
  integral form; `theorem11_pos`, `theorem11_zero`;
* `exists_rational_form`: the rational form with the prescribed local classes, and the congruence modulo 8 of the
  unit part of the 2-adic determinant (forced by (29) and the oddity formula (30));
* `pExcess_diag_eq`: the $p$-excess of $\operatorname{diag}(p^{z_i}w_i)$ is the $p$-excess of its symbol;
  `oddity_dyDiag`: the oddity of the diagonal model of a 2-adic block decomposition is the oddity of its symbol;
  `det_dyMat`, `valSum_eq`, `signProd_blockSymbol`, `signProd_oddSymbolOfDiag`: (29) for realized symbols;
* bridges: `isometricGL_gramForm_iff` (forms $\vec x^{\mathsf T}M\vec x$ vs congruence of matrices),
  `natAbs_eq_of_local` (integers with the same $p$-adic valuations everywhere).
-/
import QuadFormsKB.Literature.ConwaySloane.LocalExistence
import QuadFormsKB.Literature.Cassels.Ch6.Sec7
import QuadFormsKB.Literature.Cassels.Ch9Sec5Exist
import QuadFormsKB.Binary.GenusLocal
import QuadFormsKB.Literature.LocalGlobal.ConwaySloane
import QuadFormsKB.Literature.Cassels.Ch8.Ex5
import QuadFormsKB.Literature.Cassels.Ch8.Ex2
import QuadFormsKB.Literature.ConwaySloane.Rational

namespace QuadFormsKB.ConwaySloane

open Finset Matrix

/-! ### Odd primes: the $p$-excess of a diagonal form from its symbol -/

section OddExcess

variable {p : ℕ} [hp : Fact p.Prime]

theorem four_mul_ind8 (c : Prop) [Decidable c] : 4 * ind8 c = if c then 4 else 0 := by
  unfold ind8; split_ifs <;> simp

theorem padicValInt_pow_mul {z : ℕ} {w : ℤ} (hw : ¬ (p : ℤ) ∣ w) : padicValInt p ((p : ℤ) ^ z * w) = z := by
  have hw0 : w ≠ 0 := fun h => hw (h ▸ dvd_zero _)
  have hpz : (p : ℤ) ^ z ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [padicValInt.mul hpz hw0, padicValInt.eq_zero_of_not_dvd hw, add_zero]
  simp [padicValInt, Int.natAbs_pow]

theorem unitPart_pow_mul {z : ℕ} {w : ℤ} (hw : ¬ (p : ℤ) ∣ w) : unitPart p ((p : ℤ) ^ z * w) = w := by
  have hpz : (p : ℤ) ^ z ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  unfold unitPart
  rw [padicValInt_pow_mul hw]
  exact Int.mul_ediv_cancel_left w hpz

/-- The $p$-excess of $\langle p^zw\rangle$, $p \nmid w$: $p^z - 1 + 4[z \text{ odd and } (w/p) = -1]$. -/
theorem pExcessEntry_pow_mul (z : ℕ) {w : ℤ} (hw : ¬ (p : ℤ) ∣ w) :
    pExcessEntry p ((p : ℤ) ^ z * w) = ((p : ZMod 8) ^ z - 1) + sgn4 (if Odd z then jacobiSym w p else 1) := by
  unfold pExcessEntry
  rw [padicValInt_pow_mul hw, unitPart_pow_mul hw]
  congr 1
  by_cases hz : Odd z <;> simp [hz, sgn4]

/-- An integer prime to the odd prime $p$ is a square in $\mathbb Q_p$ iff it is a quadratic residue. -/
theorem isSquare_intCast_padic_iff (hp2 : p ≠ 2) {w : ℤ} (hw : ¬ (p : ℤ) ∣ w) :
    IsSquare (w : ℚ_[p]) ↔ jacobiSym w p = 1 := by
  obtain ⟨u, hu⟩ := exists_unit_of_not_dvd (p := p) w hw
  have h1 : ((u : ℤ_[p]) : ℚ_[p]) = (w : ℚ_[p]) := by rw [hu]; simp
  rw [← h1, HilbertLocal.isSquare_unit_iff hp2, hu, map_intCast, ← jacobiSym.legendreSym.to_jacobiSym,
    _root_.legendreSym.eq_one_iff]
  exact fun h => hw ((ZMod.intCast_zmod_eq_zero_iff_dvd w p).mp h)

theorem jacobiSym_pm_of_not_dvd {w : ℤ} (hw : ¬ (p : ℤ) ∣ w) : jacobiSym w p = 1 ∨ jacobiSym w p = -1 := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  rcases _root_.legendreSym.eq_one_or_neg_one p (a := w) (fun h => hw ((ZMod.intCast_zmod_eq_zero_iff_dvd w p).mp h))
    with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **The $p$-excess of $\operatorname{diag}(p^{z_i}w_i)$ is the $p$-excess of its $p$-adic symbol** (Conway–Sloane,
§7.7, p. 383: $p$-excess $\equiv \sum_q n_q(q-1) + 4k_p$), for an odd prime $p$, units $w_i$ prime to $p$ and exponents
$z_i < N$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, p. 383 (p-excess from the symbol)"]
theorem pExcess_diag_eq (hp2 : p ≠ 2) {n N : ℕ} (z : Fin n → ℕ) (w : Fin n → ℤ) (hw : ∀ i, ¬ (p : ℤ) ∣ w i)
    (hz : ∀ i, z i < N) :
    pExcess p (fun i => (p : ℤ) ^ (z i) * w i) = (oddSymbolOfDiag p z fun i => (w i : ℚ_[p])).pExcess p N := by
  classical
  unfold pExcess OddSymbol.pExcess
  simp only [pExcessEntry_pow_mul _ (hw _)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := z) (t := range N) (fun i _ => mem_range.mpr (hz i))]
  refine sum_congr rfl fun k _ => ?_
  have hS : ∀ i ∈ univ.filter (fun i => z i = k), z i = k := fun i hi => (mem_filter.mp hi).2
  rw [sum_add_distrib, sum_congr rfl fun i hi => by rw [hS i hi], sum_const, nsmul_eq_mul,
    sum_congr rfl fun i hi => by rw [hS i hi]]
  unfold oddSymbolOfDiag
  simp only
  rw [Fintype.card_subtype, four_mul_ind8]
  congr 1
  by_cases hk : Odd k
  · simp only [hk, ite_true, true_and]
    rw [← sgn4_prod _ _ (fun i => jacobiSym_pm_of_not_dvd (hw i)), ← jacobiSym_prod_left]
    have hprod : ∏ i : {i // z i = k}, (w i : ℚ_[p]) = ((∏ i ∈ univ.filter (fun i => z i = k), w i : ℤ) : ℚ_[p]) := by
      rw [Int.cast_prod]
      exact (Finset.prod_subtype (univ.filter fun i => z i = k) (by simp) (fun i => (w i : ℚ_[p]))).symm
    have hnd : ¬ (p : ℤ) ∣ ∏ i ∈ univ.filter (fun i => z i = k), w i := by
      intro h
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp hp.out) _).mp h
      exact hw i hi
    rw [hprod, isSquare_intCast_padic_iff hp2 hnd]
    rcases jacobiSym_pm_of_not_dvd hnd with h | h <;> simp [h, sgn4]
  · simp [hk, sgn4]

end OddExcess

/-! ### $p = 2$: integer diagonal models of Cassels' blocks -/

section TwoDiag

open Cassels

/-- **The integer diagonal model of a block** (over $\mathbb Q_2$): $2^eux^2 \mapsto \langle 2^eu\rangle$,
$2^e\cdot 2xy \mapsto \langle 2^e, -2^e\rangle$, $2^e(2x^2 + 2xy + 2y^2) \mapsto \langle 2^{e+1}, 3\cdot 2^{e+1}\rangle$
(exponents $e \ge 0$; `Int.toNat`). -/
def blockDiag : (b : DyBlock) → Fin b.dim → ℤ
  | .sq e u => ![2 ^ e.toNat * u]
  | .hyp e => ![2 ^ e.toNat, -2 ^ e.toNat]
  | .ell e => ![2 ^ (e.toNat + 1), 3 * 2 ^ (e.toNat + 1)]

/-- The integer diagonal model of an orthogonal sum of blocks. -/
def dyDiag : (D : List DyBlock) → Fin (dyDim D) → ℤ
  | [] => Fin.elim0
  | b :: D => Fin.append (blockDiag b) (dyDiag D)

/-- The unit part of the determinant of a block: $u$, $-1$, $3$. -/
def blockUnit : DyBlock → ℤ
  | .sq _ u => u
  | .hyp _ => -1
  | .ell _ => 3

theorem qequiv_sq (k : ℕ) (u : ℤ) :
    Ex5.QEquiv !![(2 : ℚ_[2]) ^ (k : ℤ) * u] (Matrix.diagonal fun i => (((![2 ^ k * u] : Fin 1 → ℤ) i : ℤ) : ℚ_[2])) := by
  refine ⟨1, by simp, ?_⟩
  ext i j
  fin_cases i; fin_cases j
  simp

theorem qequiv_hyp (k : ℕ) :
    Ex5.QEquiv ((2 : ℚ_[2]) ^ (k : ℤ) • !![0, 1; 1, 0])
      (Matrix.diagonal fun i => (((![2 ^ k, -2 ^ k] : Fin 2 → ℤ) i : ℤ) : ℚ_[2])) := by
  refine ⟨!![1, 1; 1 / 2, -1 / 2], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem qequiv_ell (k : ℕ) :
    Ex5.QEquiv ((2 : ℚ_[2]) ^ (k : ℤ) • !![2, 1; 1, 2])
      (Matrix.diagonal fun i => (((![2 ^ (k + 1), 3 * 2 ^ (k + 1)] : Fin 2 → ℤ) i : ℤ) : ℚ_[2])) := by
  refine ⟨!![1, -1; 0, 2], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring

/-- Each block is $\mathbb Q_2$-equivalent to its diagonal model. -/
theorem qequiv_blockDiag (b : DyBlock) (he : 0 ≤ blockExp b) :
    Ex5.QEquiv b.mat (Matrix.diagonal fun i => ((blockDiag b i : ℤ) : ℚ_[2])) := by
  cases b with
  | sq e u =>
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ e from he)
    exact qequiv_sq k u
  | hyp e =>
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ e from he)
    exact qequiv_hyp k
  | ell e =>
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ e from he)
    exact qequiv_ell k

theorem cast_comp_append {m k : ℕ} (a : Fin m → ℤ) (c : Fin k → ℤ) :
    (fun i => ((Fin.append a c i : ℤ) : ℚ_[2])) =
      Fin.append (fun i => ((a i : ℤ) : ℚ_[2])) (fun i => ((c i : ℤ) : ℚ_[2])) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

/-- An orthogonal sum of blocks is $\mathbb Q_2$-equivalent to its integer diagonal model. -/
theorem qequiv_dyDiag : ∀ (D : List DyBlock), (∀ b ∈ D, 0 ≤ blockExp b) →
    Ex5.QEquiv (dyMat D) (Matrix.diagonal fun i => ((dyDiag D i : ℤ) : ℚ_[2]))
  | [], _ => by
    refine ⟨1, by simp, ?_⟩
    ext i; exact i.elim0
  | b :: D, h => by
    have h1 := Ex5.QEquiv.orthSum (qequiv_blockDiag b (h b (List.mem_cons_self ..)))
      (qequiv_dyDiag D fun c hc => h c (List.mem_cons_of_mem _ hc))
    rw [Ex5.orthSum_diagonal, ← cast_comp_append] at h1
    exact h1

end TwoDiag

/-! ### $p = 2$: the invariants of the diagonal model from the symbol -/

section TwoInvariants

open Cassels

theorem oddity_append {m k : ℕ} (a : Fin m → ℤ) (c : Fin k → ℤ) :
    oddity (Fin.append a c) = oddity a + oddity c := by
  unfold oddity
  rw [Fin.sum_univ_add]
  simp

theorem prod_append {m k : ℕ} (a : Fin m → ℤ) (c : Fin k → ℤ) :
    ∏ i, Fin.append a c i = (∏ i, a i) * ∏ i, c i := by
  rw [Fin.prod_univ_add]
  simp

theorem four_ind8_mul (k : ℕ) (s t : Sign) :
    4 * ind8 (Odd k ∧ s.mul t = .minus) = 4 * ind8 (Odd k ∧ s = .minus) + 4 * ind8 (Odd k ∧ t = .minus) := by
  by_cases hk : Odd k <;> cases s <;> cases t <;> simp [hk, ind8, Sign.mul, Sign.flip] <;> decide

theorem blockSymbol_cons_oddity (b : DyBlock) (D : List DyBlock) (k : ℕ) :
    (blockSymbol (b :: D) k).oddity = (if blockExp b = k then blockOddity b else 0) + (blockSymbol D k).oddity := by
  unfold blockSymbol
  simp only [List.filter_cons]
  split_ifs with h h' <;> simp_all

theorem blockSymbol_cons_sign (b : DyBlock) (D : List DyBlock) (k : ℕ) :
    (blockSymbol (b :: D) k).sign =
      if blockExp b = k then (blockSign b).mul (blockSymbol D k).sign else (blockSymbol D k).sign := by
  unfold blockSymbol
  simp only [List.filter_cons]
  split_ifs with h h' <;> simp_all [Sign.prodList]

theorem blockSymbol_cons_dim (b : DyBlock) (D : List DyBlock) (k : ℕ) :
    (blockSymbol (b :: D) k).dim = (if blockExp b = k then b.dim else 0) + (blockSymbol D k).dim := by
  unfold blockSymbol
  simp only [List.filter_cons]
  split_ifs with h h' <;> simp_all

theorem blockExp_eq_iff {b : DyBlock} (he : 0 ≤ blockExp b) (k : ℕ) : blockExp b = k ↔ (blockExp b).toNat = k := by
  omega

/-- The oddity of the diagonal model of one block: $t + 4[e \text{ odd}, \varepsilon = -]$. -/
theorem oddity_blockDiag (b : DyBlock) (hv : b.Valid) :
    oddity (blockDiag b) = blockOddity b + 4 * ind8 (Odd (blockExp b).toNat ∧ blockSign b = .minus) := by
  have h1 : ∀ k : ℕ, oddityEntry (2 ^ k) = 1 + if Odd k ∧ ((1 : ZMod 8) = 3 ∨ (1 : ZMod 8) = 5) then 4 else 0 :=
    fun k => by simpa using Rational.oddityEntry_two_pow_mul k 1 (by decide)
  have h3 : ∀ k : ℕ, oddityEntry (3 * 2 ^ k) = 3 + if Odd k ∧ ((3 : ZMod 8) = 3 ∨ (3 : ZMod 8) = 5) then 4 else 0 :=
    fun k => by rw [mul_comm]; simpa using Rational.oddityEntry_two_pow_mul k 3 (by decide)
  have hm : ∀ k : ℕ, oddityEntry (-2 ^ k) = -1 + if Odd k ∧ ((-1 : ZMod 8) = 3 ∨ (-1 : ZMod 8) = 5) then 4 else 0 :=
    fun k => by
      have := Rational.oddityEntry_two_pow_mul k (-1) (by decide)
      rw [mul_neg_one] at this; rw [this]; push_cast; rfl
  cases b with
  | sq e u =>
    have hu : ¬ (2 : ℤ) ∣ u := by
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    change oddity (![2 ^ e.toNat * u] : Fin 1 → ℤ) = _
    simp only [oddity, Fin.sum_univ_one, Matrix.cons_val_zero, blockOddity, blockExp, blockSign]
    rw [Rational.oddityEntry_two_pow_mul _ _ hu]
    simp only [ind8]
    rcases hv with rfl | rfl | rfl | rfl <;> by_cases hk : Odd e.toNat <;> simp [hk, jacobiTwo] <;> decide
  | hyp e =>
    change oddity (![2 ^ e.toNat, -2 ^ e.toNat] : Fin 2 → ℤ) = _
    simp only [oddity, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, blockOddity,
      blockExp, blockSign]
    rw [h1, hm]
    simp only [ind8]
    by_cases hk : Odd e.toNat <;> simp [hk] <;> decide
  | ell e =>
    change oddity (![2 ^ (e.toNat + 1), 3 * 2 ^ (e.toNat + 1)] : Fin 2 → ℤ) = _
    simp only [oddity, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, blockOddity,
      blockExp, blockSign]
    rw [h1, h3]
    simp only [ind8]
    rcases Nat.even_or_odd e.toNat with hk | hk
    · have hk' : Odd (e.toNat + 1) := hk.add_one
      have hk'' : ¬ Odd e.toNat := Nat.not_odd_iff_even.mpr hk
      simp [hk', hk'']; decide
    · have hk' : ¬ Odd (e.toNat + 1) := Nat.not_odd_iff_even.mpr hk.add_one
      simp [hk, hk']; decide

/-- **The oddity of the diagonal model is the oddity of the 2-adic symbol** (Conway–Sloane, §7.7, p. 383:
oddity $\equiv \sum_q t_q + 4k_2$), for valid blocks of exponents in $[0, N)$. -/
theorem oddity_dyDiag {N : ℕ} : ∀ (D : List DyBlock), (∀ b ∈ D, b.Valid) →
    (∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < N) → oddity (dyDiag D) = (blockSymbol D).oddity N
  | [], _, _ => by
    have : IsEmpty (Fin (dyDim [])) := ⟨fun i => i.elim0⟩
    simp [oddity, Finset.univ_eq_empty, TwoSymbol.oddity, blockSymbol, Sign.prodList, ind8]
  | b :: D, hv, he => by
    have ih := oddity_dyDiag D (fun c hc => hv c (List.mem_cons_of_mem _ hc))
      (fun c hc => he c (List.mem_cons_of_mem _ hc))
    obtain ⟨he0, heN⟩ := he b (List.mem_cons_self ..)
    refine (oddity_append (blockDiag b) (dyDiag D)).trans ?_
    rw [ih, oddity_blockDiag b (hv b (List.mem_cons_self ..))]
    unfold TwoSymbol.oddity
    simp only [blockSymbol_cons_oddity, blockSymbol_cons_sign, blockExp_eq_iff he0]
    have : ∀ k, (((if (blockExp b).toNat = k then blockOddity b else 0) + (blockSymbol D k).oddity) +
        4 * ind8 (Odd k ∧ (if (blockExp b).toNat = k then (blockSign b).mul (blockSymbol D k).sign
          else (blockSymbol D k).sign) = .minus)) =
        ((blockSymbol D k).oddity + 4 * ind8 (Odd k ∧ (blockSymbol D k).sign = .minus)) +
          if (blockExp b).toNat = k then blockOddity b + 4 * ind8 (Odd k ∧ blockSign b = .minus) else 0 := by
      intro k
      split_ifs with h
      · rw [four_ind8_mul]; ring
      · ring
    simp only [this, sum_add_distrib]
    rw [Finset.sum_ite_eq, if_pos (mem_range.mpr (by omega))]
    ring

end TwoInvariants

/-! ### $p = 2$: determinant, valuation and signs of a block decomposition -/

section TwoDet

open Cassels

/-- $\sum_b \dim(b)\,e_b$: the $2$-adic valuation of the determinant of a block decomposition. -/
def valSum (D : List DyBlock) : ℕ := (D.map fun b => b.dim * (blockExp b).toNat).sum

/-- The unit part of the determinant of a block decomposition: the product of the `blockUnit`s. -/
def unitProd (D : List DyBlock) : ℤ := (D.map blockUnit).prod

theorem odd_unitProd : ∀ (D : List DyBlock), (∀ b ∈ D, b.Valid) → ¬ (2 : ℤ) ∣ unitProd D
  | [], _ => by simp [unitProd]
  | b :: D, hv => by
    have ih := odd_unitProd D fun c hc => hv c (List.mem_cons_of_mem _ hc)
    have hb : ¬ (2 : ℤ) ∣ blockUnit b := by
      have := hv b (List.mem_cons_self ..)
      cases b with
      | sq e u => rcases this with rfl | rfl | rfl | rfl <;> simp only [blockUnit] <;> decide
      | hyp e => simp only [blockUnit]; decide
      | ell e => simp only [blockUnit]; decide
    simp only [unitProd, List.map_cons, List.prod_cons] at ih ⊢
    exact fun h => (Int.prime_two.dvd_or_dvd h).elim hb ih

theorem prod_blockDiag (b : DyBlock) :
    ∃ m : ℕ, ∏ i, blockDiag b i = 4 ^ m * (2 ^ (b.dim * (blockExp b).toNat) * blockUnit b) := by
  cases b with
  | sq e u =>
    refine ⟨0, ?_⟩
    change ∏ i, (![2 ^ e.toNat * u] : Fin 1 → ℤ) i = _
    simp [blockExp, blockUnit, DyBlock.dim]
  | hyp e =>
    refine ⟨0, ?_⟩
    change ∏ i, (![2 ^ e.toNat, -2 ^ e.toNat] : Fin 2 → ℤ) i = _
    simp [Fin.prod_univ_two, blockExp, blockUnit, DyBlock.dim]
    ring
  | ell e =>
    refine ⟨1, ?_⟩
    change ∏ i, (![2 ^ (e.toNat + 1), 3 * 2 ^ (e.toNat + 1)] : Fin 2 → ℤ) i = _
    simp [Fin.prod_univ_two, blockExp, blockUnit, DyBlock.dim]
    ring

/-- The determinant of the diagonal model: $4^m \cdot 2^{\sum \dim(b) e_b} \cdot \prod_b u_b$. -/
theorem prod_dyDiag : ∀ (D : List DyBlock), ∃ m : ℕ, ∏ i, dyDiag D i = 4 ^ m * (2 ^ valSum D * unitProd D)
  | [] => ⟨0, by
    have : IsEmpty (Fin (dyDim [])) := ⟨fun i => i.elim0⟩
    simp [valSum, unitProd, Finset.univ_eq_empty]⟩
  | b :: D => by
    obtain ⟨m, hm⟩ := prod_dyDiag D
    obtain ⟨m', hm'⟩ := prod_blockDiag b
    refine ⟨m' + m, ?_⟩
    refine (prod_append (blockDiag b) (dyDiag D)).trans ?_
    rw [hm, hm']
    simp only [valSum, unitProd, List.map_cons, List.sum_cons, List.prod_cons]
    ring

theorem det_blockMat (b : DyBlock) (he : 0 ≤ blockExp b) :
    b.mat.det = (((2 : ℤ) ^ (b.dim * (blockExp b).toNat) * blockUnit b : ℤ) : ℚ_[2]) := by
  cases b with
  | sq e u =>
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ e from he)
    change (!![(2 : ℚ_[2]) ^ (k : ℤ) * u]).det = _
    simp [blockExp, blockUnit, DyBlock.dim]
  | hyp e =>
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ e from he)
    change ((2 : ℚ_[2]) ^ (k : ℤ) • !![(0 : ℚ_[2]), 1; 1, 0]).det = _
    rw [Matrix.det_smul, Matrix.det_fin_two_of]
    simp [blockExp, blockUnit, DyBlock.dim]
    ring
  | ell e =>
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ e from he)
    change ((2 : ℚ_[2]) ^ (k : ℤ) • !![(2 : ℚ_[2]), 1; 1, 2]).det = _
    rw [Matrix.det_smul, Matrix.det_fin_two_of]
    simp [blockExp, blockUnit, DyBlock.dim]
    ring

/-- The determinant of a block decomposition: $2^{\sum \dim(b) e_b} \prod_b u_b$. -/
theorem det_dyMat : ∀ (D : List DyBlock), (∀ b ∈ D, 0 ≤ blockExp b) →
    (dyMat D).det = (((2 : ℤ) ^ valSum D * unitProd D : ℤ) : ℚ_[2])
  | [], _ => by
    have : IsEmpty (Fin (dyDim [])) := ⟨fun i => i.elim0⟩
    simp [valSum, unitProd, Matrix.det_isEmpty]
  | b :: D, he => by
    show (orthSumMat b.mat (dyMat D)).det = _
    rw [dyadic_det_orthSumMat, det_blockMat b (he b (List.mem_cons_self ..)),
      det_dyMat D fun c hc => he c (List.mem_cons_of_mem _ hc)]
    simp only [valSum, unitProd, List.map_cons, List.sum_cons, List.prod_cons]
    push_cast
    ring

/-- $\sum_b \dim(b)\,e_b = \sum_{k < N} k\,n_{2^k}$ for the symbol of the decomposition. -/
theorem valSum_eq {N : ℕ} : ∀ (D : List DyBlock), (∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < N) →
    valSum D = ∑ k ∈ range N, k * (blockSymbol D k).dim
  | [], _ => by simp [valSum, blockSymbol]
  | b :: D, he => by
    obtain ⟨he0, heN⟩ := he b (List.mem_cons_self ..)
    have ih := valSum_eq D fun c hc => he c (List.mem_cons_of_mem _ hc)
    simp only [valSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [blockSymbol_cons_dim, blockExp_eq_iff he0, mul_add, sum_add_distrib]
    have : ∀ k, k * (if (blockExp b).toNat = k then b.dim else 0) =
        if (blockExp b).toNat = k then b.dim * (blockExp b).toNat else 0 := by
      intro k; split_ifs with h <;> simp [h, mul_comm]
    simp only [this]
    rw [Finset.sum_ite_eq, if_pos (mem_range.mpr (by omega))]

theorem toInt_injective : Function.Injective Sign.toInt := by
  intro s t h; cases s <;> cases t <;> simp_all [Sign.toInt]

theorem toInt_signProd (s : ℕ → Sign) (N : ℕ) : (signProd s N).toInt = ∏ k ∈ range N, (s k).toInt := by
  induction N with
  | zero => rfl
  | succ N ih => rw [signProd, Sign.toInt_mul, ih, prod_range_succ]

theorem toInt_jacobiTwo_mul {x y : ℤ} (hx : ¬ (2 : ℤ) ∣ x) (hy : ¬ (2 : ℤ) ∣ y) :
    (jacobiTwo (x * y)).toInt = (jacobiTwo x).toInt * (jacobiTwo y).toInt := by
  have hx' : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  have hy' : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by omega
  have hxy : x * y % 8 = (x % 8) * (y % 8) % 8 := Int.mul_emod x y 8
  simp only [jacobiTwo]
  rcases hx' with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;>
    rw [h, h'] at hxy <;> norm_num at hxy <;> simp [h, h', hxy, Sign.toInt]

theorem blockSign_eq (b : DyBlock) (hv : b.Valid) : blockSign b = jacobiTwo (blockUnit b) := by
  cases b with
  | sq e u => rfl
  | hyp e => rfl
  | ell e => rfl

/-- The product of the signs of the symbol of a block decomposition is $\left(\frac{\prod_b u_b}{2}\right)$. -/
theorem signProd_blockSymbol {N : ℕ} : ∀ (D : List DyBlock), (∀ b ∈ D, b.Valid) →
    (∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < N) →
    signProd (fun k => (blockSymbol D k).sign) N = jacobiTwo (unitProd D)
  | [], _, _ => by
    apply toInt_injective
    rw [toInt_signProd]
    simp [blockSymbol, Sign.prodList, unitProd, jacobiTwo, Sign.toInt]
  | b :: D, hv, he => by
    obtain ⟨he0, heN⟩ := he b (List.mem_cons_self ..)
    have ih := signProd_blockSymbol D (fun c hc => hv c (List.mem_cons_of_mem _ hc))
      (fun c hc => he c (List.mem_cons_of_mem _ hc))
    apply toInt_injective
    have ih' := congrArg Sign.toInt ih
    rw [toInt_signProd] at ih' ⊢
    rw [show unitProd (b :: D) = blockUnit b * unitProd D from by simp [unitProd]]
    rw [toInt_jacobiTwo_mul ?_ (odd_unitProd D fun c hc => hv c (List.mem_cons_of_mem _ hc))]
    · rw [← blockSign_eq b (hv b (List.mem_cons_self ..))]
      rw [← ih']
      simp only [blockSymbol_cons_sign, blockExp_eq_iff he0]
      have : ∀ k, (if (blockExp b).toNat = k then (blockSign b).mul (blockSymbol D k).sign
          else (blockSymbol D k).sign).toInt =
          (if (blockExp b).toNat = k then (blockSign b).toInt else 1) * (blockSymbol D k).sign.toInt := by
        intro k; split_ifs <;> simp [Sign.toInt_mul]
      simp only [this, prod_mul_distrib]
      rw [Finset.prod_ite_eq, if_pos (mem_range.mpr (by omega))]
    · have := odd_unitProd [b] (by simpa using hv b (List.mem_cons_self ..))
      simpa [unitProd] using this

end TwoDet

/-! ### Odd primes: integer realizations and their determinants -/

section OddData

variable {p : ℕ} [hp : Fact p.Prime]

/-- An integer quadratic non-residue modulo the odd prime $p$. -/
theorem exists_int_nonresidue (hp2 : p ≠ 2) : ∃ r : ℤ, ¬ (p : ℤ) ∣ r ∧ jacobiSym r p = -1 := by
  have : Fact (ringChar (ZMod p) ≠ 2) := ⟨by rwa [ZMod.ringChar_zmod_n]⟩
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by simp [h]⟩
  have hcast : ((a.val : ℤ) : ZMod p) = a := by simp
  have hnd : ¬ (p : ℤ) ∣ (a.val : ℤ) := fun h => ha0 (by
    rw [← hcast]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h)
  refine ⟨a.val, hnd, ?_⟩
  rcases jacobiSym_pm_of_not_dvd hnd with h | h
  · exfalso; apply ha
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p (by rwa [hcast])] at h
    rwa [hcast] at h
  · exact h

/-- **Theorem 11, local part at an odd prime, with integer entries**: a $p$-adic symbol supported below $N$ whose
constituents satisfy (31) is the symbol of $\operatorname{diag}(p^{z_i}w_i)$ with integers $w_i \in \{1, r\}$ prime
to $p$, for a fixed integer non-residue $r$. -/
theorem exists_int_diag_of_oddSymbol (hp2 : p ≠ 2) {σ : OddSymbol} {N : ℕ} (hσ : σ.SupportedBelow N)
    (hex : ∀ k, (σ k).Exists) :
    ∃ (m : ℕ) (z : Fin m → ℕ) (w : Fin m → ℤ), m = ∑ k ∈ range N, (σ k).dim ∧ (∀ i, z i < N) ∧
      (∀ i, ¬ (p : ℤ) ∣ w i) ∧ oddSymbolOfDiag p z (fun i => (w i : ℚ_[p])) = σ := by
  classical
  obtain ⟨r, hrp, hrJ⟩ := exists_int_nonresidue hp2
  have hr1 : ‖(r : ℚ_[p])‖ = 1 := by
    obtain ⟨u, hu⟩ := exists_unit_of_not_dvd (p := p) r hrp
    have h1 : ((u : ℤ_[p]) : ℚ_[p]) = (r : ℚ_[p]) := by rw [hu]; simp
    rw [← h1, PadicInt.norm_coe]
    exact PadicInt.isUnit_iff.mp u.isUnit
  have hrs : ¬ IsSquare (r : ℚ_[p]) := by
    rw [isSquare_intCast_padic_iff hp2 hrp, hrJ]; decide
  obtain ⟨m, z, u, hm, hz, hu, hs⟩ := exists_diag_of_oddSymbol_of (r : ℚ_[p]) hr1 hrs hσ hex
  refine ⟨m, z, fun i => if u i = 1 then 1 else r, hm, hz, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact fun h => (Nat.prime_iff_prime_int.mp hp.out).not_dvd_one h
    · exact hrp
  · rw [← hs]
    congr 1
    funext i
    dsimp only
    split_ifs with h
    · simp [h]
    · rcases hu i with h' | h'
      · exact (h h').elim
      · rw [h']

/-- $\sum_i z_i = \sum_{k<N} k\,n_{p^k}$ for the symbol of $\operatorname{diag}(p^{z_i}u_i)$, $z_i < N$. -/
theorem sum_z_eq {n N : ℕ} (z : Fin n → ℕ) (u : Fin n → ℚ_[p]) (hz : ∀ i, z i < N) :
    ∑ i, z i = ∑ k ∈ range N, k * (oddSymbolOfDiag p z u k).dim := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := z) (t := range N) (fun i _ => mem_range.mpr (hz i))]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_congr rfl fun i hi => (mem_filter.mp hi).2]
  simp [oddSymbolOfDiag, Fintype.card_subtype, mul_comm]

theorem toInt_ofInt_jacobiSym {w : ℤ} (hw : ¬ (p : ℤ) ∣ w) : (Sign.ofInt (jacobiSym w p)).toInt = jacobiSym w p := by
  rcases jacobiSym_pm_of_not_dvd hw with h | h <;> simp [h, Sign.ofInt, Sign.toInt]

/-- The product of the signs of the symbol of $\operatorname{diag}(p^{z_i}w_i)$ is $\left(\frac{\prod_i w_i}{p}\right)$. -/
theorem signProd_oddSymbolOfDiag (hp2 : p ≠ 2) {n N : ℕ} (z : Fin n → ℕ) (w : Fin n → ℤ)
    (hw : ∀ i, ¬ (p : ℤ) ∣ w i) (hz : ∀ i, z i < N) :
    signProd (fun k => (oddSymbolOfDiag p z (fun i => (w i : ℚ_[p])) k).sign) N =
      Sign.ofInt (jacobiSym (∏ i, w i) p) := by
  classical
  have hnd : ∀ (T : Finset (Fin n)), ¬ (p : ℤ) ∣ ∏ i ∈ T, w i := fun T h => by
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp hp.out) _).mp h
    exact hw i hi
  apply toInt_injective
  rw [toInt_signProd, toInt_ofInt_jacobiSym (hnd univ)]
  rw [← Finset.prod_fiberwise_of_maps_to (g := z) (t := range N) (fun i _ => mem_range.mpr (hz i)),
    jacobiSym_prod_left]
  refine prod_congr rfl fun k _ => ?_
  rw [← toInt_ofInt_jacobiSym (hnd _)]
  congr 1
  have hprod : ∏ i : {i // z i = k}, (w i : ℚ_[p]) = ((∏ i ∈ univ.filter (fun i => z i = k), w i : ℤ) : ℚ_[p]) := by
    rw [Int.cast_prod]
    exact (Finset.prod_subtype (univ.filter fun i => z i = k) (by simp) (fun i => (w i : ℚ_[p]))).symm
  simp only [oddSymbolOfDiag]
  rw [hprod, isSquare_intCast_padic_iff hp2 (hnd _)]
  rcases jacobiSym_pm_of_not_dvd (hnd (univ.filter fun i => z i = k)) with h | h <;> simp [h, Sign.ofInt]

end OddData

/-! ### Gram matrices and `QuadForm`s -/

section GramBridge

open Siegel Lattices

variable {K : Type*} [CommRing K] {n : ℕ}

/-- Congruence of matrices over $K$: $M' = g^{\mathsf T}Mg$ for some $g \in \mathrm{GL}_n(K)$. -/
def CongrIn (K : Type*) [CommRing K] (M M' : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ g : GL (Fin n) K, g.valᵀ * M * g.val = M'

theorem CongrIn.refl (M : Matrix (Fin n) (Fin n) K) : CongrIn K M M := ⟨1, by simp⟩

theorem CongrIn.symm {M M' : Matrix (Fin n) (Fin n) K} (h : CongrIn K M M') : CongrIn K M' M := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  have h1 : g.val * (g⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (g⁻¹).valᵀ * (g.valᵀ * M * g.val) * (g⁻¹).val = (g.val * (g⁻¹).val)ᵀ * M * (g.val * (g⁻¹).val) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = M := by rw [h1]; simp

theorem CongrIn.trans {M M' M'' : Matrix (Fin n) (Fin n) K} (h : CongrIn K M M') (h' : CongrIn K M' M'') :
    CongrIn K M M'' := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨g', rfl⟩ := h'
  exact ⟨g * g', by simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]⟩

theorem dotProduct_transpose_mul (A M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    x ⬝ᵥ ((Aᵀ * M * A) *ᵥ x) = (A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem gramForm_map {L : Type*} [CommRing L] (f : K →+* L) (M : Matrix (Fin n) (Fin n) K) :
    (Cassels.Ch8Ex2.gramForm M).map f = Cassels.Ch8Ex2.gramForm (M.map f) := by
  ext i j
  simp only [QuadForm.map, Cassels.Ch8Ex2.gramForm, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

variable [IsDomain K] [CharZero K]

theorem eval_gramForm (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (Cassels.Ch8Ex2.gramForm M).eval x = x ⬝ᵥ (M *ᵥ x) := by
  have h := QuadForm.polar_eq_hessian K (Cassels.Ch8Ex2.gramForm M) x x
  have e : ∀ A : Matrix (Fin n) (Fin n) K, A.map (algebraMap K K) = A := fun A => by ext; simp
  rw [e, Cassels.Ch8Ex2.hessian_gramForm, Matrix.add_mulVec, dotProduct_add] at h
  have h2 : (Cassels.Ch8Ex2.gramForm M).evalIn K (x + x) = 4 * (Cassels.Ch8Ex2.gramForm M).evalIn K x := by
    rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, ← two_smul K x, Matrix.mulVec_smul,
      smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]; ring
  have ht : x ⬝ᵥ (Mᵀ *ᵥ x) = x ⬝ᵥ (M *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [h2, ht] at h
  have h3 : (2 : K) * (Cassels.Ch8Ex2.gramForm M).eval x = 2 * (x ⬝ᵥ (M *ᵥ x)) := by
    change (2 : K) * (Cassels.Ch8Ex2.gramForm M).evalIn K x = _
    linear_combination h
  exact mul_left_cancel₀ two_ne_zero h3

/-- For symmetric matrices, `IsometricGL` of the forms $\vec x^{\mathsf T}M\vec x$ is congruence of the matrices. -/
theorem isometricGL_gramForm_iff {M M' : Matrix (Fin n) (Fin n) K} (hM : Mᵀ = M) (hM' : M'ᵀ = M') :
    IsometricGL (Cassels.Ch8Ex2.gramForm M) (Cassels.Ch8Ex2.gramForm M') ↔ CongrIn K M M' := by
  constructor
  · rintro ⟨g, hg⟩
    have h := Cassels.Ch8Ex2.hessian_congr hg
    rw [Cassels.Ch8Ex2.hessian_gramForm, Cassels.Ch8Ex2.hessian_gramForm, hM, hM'] at h
    refine ⟨g, ?_⟩
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply] at this
    exact mul_left_cancel₀ (two_ne_zero (α := K)) (by linear_combination this)
  · rintro ⟨g, rfl⟩
    exact ⟨g, fun x => by rw [eval_gramForm, eval_gramForm, dotProduct_transpose_mul]⟩

end GramBridge

/-! ### Helpers for the global step -/

section GlobalHelpers

theorem even_card_of_sum_sgn4 {ι : Type*} (T : Finset ι) (ε : ι → ℤ) (h : ∑ i ∈ T, sgn4 (ε i) = 0) :
    Even (T.filter fun i => ε i = -1).card := by
  classical
  have h1 : ∑ i ∈ T, sgn4 (ε i) = 4 * ((T.filter fun i => ε i = -1).card : ZMod 8) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    unfold sgn4; split_ifs <;> simp
  rw [h1] at h
  have h8 : ((4 * (T.filter fun i => ε i = -1).card : ℕ) : ZMod 8) = 0 := by push_cast; exact h
  rw [ZMod.natCast_eq_zero_iff] at h8
  obtain ⟨k, hk⟩ := h8
  exact ⟨k, by omega⟩

theorem two_mul_sgn4 (s : ℤ) : (2 : ZMod 8) * sgn4 s = 0 := by
  unfold sgn4; split_ifs; decide; simp

theorem two_mul_oddityEntry (x : ℤ) : (2 : ZMod 8) * oddityEntry x = 2 * (unitPart 2 x : ZMod 8) := by
  unfold oddityEntry; split_ifs <;> ring_nf <;> simp [show (8 : ZMod 8) = 0 from rfl]

theorem pExcessEntry_eq_of {p : ℕ} {x y : ℤ} (hv : padicValInt p x = padicValInt p y)
    (hJ : jacobiSym (unitPart p x) p = jacobiSym (unitPart p y) p) : pExcessEntry p x = pExcessEntry p y := by
  unfold pExcessEntry; rw [hv, hJ]

theorem oddityEntry_eq_of {x y : ℤ} (hv : (Odd (padicValInt 2 x) ↔ Odd (padicValInt 2 y)))
    (hu : (unitPart 2 x : ZMod 8) = unitPart 2 y) : oddityEntry x = oddityEntry y := by
  unfold oddityEntry; rw [hu]; simp only [hv]

/-- Odd integers with the same $\left(\frac{\cdot}{2}\right)$ that agree modulo 4 agree modulo 8. -/
theorem zmod8_eq_of_jacobiTwo {x y : ℤ} (hx : ¬ (2 : ℤ) ∣ x) (hy : ¬ (2 : ℤ) ∣ y) (hJ : jacobiTwo x = jacobiTwo y)
    (h4 : (2 : ZMod 8) * x = 2 * y) : (x : ZMod 8) = y := by
  have ex : (x : ZMod 8) = ((x % 8 : ℤ) : ZMod 8) := (ZMod.intCast_mod x 8).symm
  have ey : (y : ZMod 8) = ((y % 8 : ℤ) : ZMod 8) := (ZMod.intCast_mod y 8).symm
  have hx' : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  have hy' : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by omega
  rw [ex, ey] at h4 ⊢
  simp only [jacobiTwo] at hJ
  rcases hx' with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;> rw [h, h'] at h4 ⊢ <;>
    simp_all <;> revert h4 <;> decide

/-- Nonzero rationals whose product is a square in $K$ are in the same square class of $K$. -/
theorem sameSquareClass_of_mul_sq (K : Type*) [Field K] [CharZero K] {X d : ℚ} (hX : X ≠ 0) (hd : d ≠ 0)
    (s : K) (hs : algebraMap ℚ K X * algebraMap ℚ K d = s ^ 2) : SameSquareClass K X d := by
  have hd' : algebraMap ℚ K d ≠ 0 := by simpa using hd
  have hX' : algebraMap ℚ K X ≠ 0 := by simpa using hX
  refine ⟨s / algebraMap ℚ K d, div_ne_zero (fun h => ?_) hd', ?_⟩
  · rw [h, zero_pow two_ne_zero] at hs
    exact mul_ne_zero hX' hd' hs
  · rw [div_pow, ← hs]
    field_simp

end GlobalHelpers

/-! ### The local data of a putative genus -/

section LocalData

open Cassels

/-- The $(-1)$-adic model $\langle 1^r, (-1)^{n-r}\rangle$. -/
def realVec (n r : ℕ) : Fin n → ℤ := fun i => if (i : ℕ) < r then 1 else -1

theorem realVec_ne_zero (n r : ℕ) (i : Fin n) : realVec n r i ≠ 0 := by
  unfold realVec; split_ifs <;> decide

theorem signature_realVec {n r : ℕ} (hr : r ≤ n) : signature (realVec n r) = (r : ℤ) - (n - r : ℕ) := by
  unfold signature realVec
  rw [Fin.sum_univ_eq_sum_range (fun i => Int.sign (if i < r then (1 : ℤ) else -1)) n]
  have : ∀ i, Int.sign (if i < r then (1 : ℤ) else -1) = if i < r then 1 else -1 := fun i => by
    split_ifs <;> rfl
  simp only [this, Finset.sum_ite, Finset.sum_const, smul_eq_mul, mul_one, mul_neg]
  have h1 : (range n).filter (· < r) = range r := by ext i; simp; omega
  have h2 : ((range n).filter fun i => ¬ i < r).card = n - r := by
    rw [show ((range n).filter fun i => ¬ i < r) = Ico r n by ext i; simp; omega, Nat.card_Ico]
  rw [h1, h2, card_range]
  push_cast; ring_nf

theorem prod_realVec {n r : ℕ} (hr : r ≤ n) : ∏ i, realVec n r i = (-1) ^ (n - r) := by
  unfold realVec
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < r then (1 : ℤ) else -1) n, Finset.prod_ite]
  have h1 : (range n).filter (· < r) = range r := by ext i; simp; omega
  have h2 : ((range n).filter fun i => ¬ i < r).card = n - r := by
    rw [show ((range n).filter fun i => ¬ i < r) = Ico r n by ext i; simp; omega, Nat.card_Ico]
  have h3 : ((range n).filter fun i => r ≤ i).card = n - r := by
    rw [show ((range n).filter fun i => r ≤ i) = Ico r n by ext i; simp; omega, Nat.card_Ico]
  simp [h3]

theorem twoRealization_exp_lt (σ : TwoSymbol) (N : ℕ) : ∀ b ∈ twoRealization σ N, blockExp b < N := by
  induction N with
  | zero => simp [twoRealization]
  | succ N ih =>
    intro b hb
    simp only [twoRealization, List.mem_append] at hb
    rcases hb with hb | hb
    · have := ih b hb; omega
    · rw [twoBlocks_exp N _ b hb]; push_cast; omega

/-- Local data at odd $p$ in the right dimension. -/
theorem exists_int_diag_dim {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {σ : OddSymbol} {N n : ℕ}
    (hσ : σ.SupportedBelow N) (hex : ∀ k, (σ k).Exists) (hdim : ∑ k ∈ range N, (σ k).dim = n) :
    ∃ (z : Fin n → ℕ) (w : Fin n → ℤ), (∀ i, z i < N) ∧ (∀ i, ¬ (p : ℤ) ∣ w i) ∧
      oddSymbolOfDiag p z (fun i => (w i : ℚ_[p])) = σ := by
  obtain ⟨m, z, w, hm, hz, hw, hs⟩ := exists_int_diag_of_oddSymbol hp2 hσ hex
  have : m = n := hm.trans hdim
  subst this
  exact ⟨z, w, hz, hw, hs⟩

theorem oddity_comp_cast {m k : ℕ} (h : m = k) (a : Fin m → ℤ) :
    oddity (fun i : Fin k => a (Fin.cast h.symm i)) = oddity a := by
  subst h; rfl

theorem prod_comp_cast {m k : ℕ} (h : m = k) (a : Fin m → ℤ) :
    ∏ i : Fin k, a (Fin.cast h.symm i) = ∏ i, a i := by
  subst h; rfl

/-- The $p$-adic valuation and unit part of $\prod_i p^{z_i}w_i$. -/
theorem prod_pow_mul {p : ℕ} [Fact p.Prime] {n : ℕ} (z : Fin n → ℕ) (w : Fin n → ℤ) :
    ∏ i, (p : ℤ) ^ (z i) * w i = (p : ℤ) ^ (∑ i, z i) * ∏ i, w i := by
  rw [prod_mul_distrib, prod_pow_eq_pow_sum]

end LocalData

/-! ### The global rational form -/

section RationalForm

open Cassels

/-- The diagonal model at each place: $\alpha_\infty$ at $\infty$, $\alpha_2$ at $2$, $\alpha_p$ at an odd prime. -/
def placeVec {n : ℕ} (aInf a2 : Fin n → ℤ) (ao : ℕ → Fin n → ℤ) : RatPlace → Fin n → ℚ
  | .infinite => fun i => aInf i
  | .finite q => if q.1 = 2 then fun i => a2 i else fun i => ao q.1 i

theorem padicValInt_two_pow_mul {z : ℕ} {w : ℤ} (hw : ¬ (2 : ℤ) ∣ w) : padicValInt 2 (2 ^ z * w) = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa using padicValInt_pow_mul (p := 2) (z := z) (by exact_mod_cast hw)

theorem unitPart_two_pow_mul {z : ℕ} {w : ℤ} (hw : ¬ (2 : ℤ) ∣ w) : unitPart 2 (2 ^ z * w) = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa using unitPart_pow_mul (p := 2) (z := z) (by exact_mod_cast hw)

theorem ofInt_inj {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) (h : Sign.ofInt x = Sign.ofInt y) :
    x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all [Sign.ofInt]

theorem jacobiTwo_eq_unitPart (d : ℤ) : d / 2 ^ padicValInt 2 d = unitPart 2 d := by
  simp [unitPart]

theorem sum_filter_ne_two (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (f : ℕ → ZMod 8) :
    ∑ p ∈ s.filter (· ≠ 2), f p = ∑ q ∈ (s.erase 2).subtype Nat.Prime, f q.1 := by
  classical
  rw [Finset.sum_subtype_eq_sum_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1⟩, hs p h1⟩
  · rintro ⟨⟨h2, h1⟩, -⟩; exact ⟨h1, h2⟩

/-- **The rational form of Theorem 11**: under the conditions (29)–(35) and given local realizations (diagonal models
`z`, `w` at odd primes, a block decomposition `D` at $2$), there is a rational diagonal form $\langle a\rangle$ that is
$\mathbb Q_v$-equivalent to the diagonal model at every place $v$ (Cassels Ch. 6, Thm. 1.3, with the parity of the
number of places with Hasse invariant $-1$ given by the oddity formula (30)). Also: the unit part of the determinant of
the block decomposition is that of $d$ modulo $8$. -/
theorem exists_rational_form (G : GenusSymbolData) (hG : G.Conditions) (hn : 1 ≤ G.n)
    (z : ℕ → Fin G.n → ℕ) (w : ℕ → Fin G.n → ℤ)
    (hz : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ i, z p i < G.N)
    (hw : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ i, ¬ (p : ℤ) ∣ w p i)
    (hs : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → oddSymbolOfDiag p (z p) (fun i => (w p i : ℚ_[p])) = G.odd p)
    (D : List DyBlock) (hDv : ∀ b ∈ D, b.Valid) (hDe : ∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < G.N)
    (hDdim : dyDim D = G.n) (hDs : blockSymbol D = G.two) :
    (unitProd D : ZMod 8) = (unitPart 2 G.det : ZMod 8) ∧
    ∃ a : Fin G.n → ℚ, (∀ i, a i ≠ 0) ∧ ∀ v : RatPlace, v.atPlace fun K _ _ =>
      (QuadForm.diag a).IsometricIn K (QuadForm.diag (placeVec (realVec G.n G.real.pos)
        (fun i => dyDiag D (Fin.cast hDdim.symm i)) (fun p i => (p : ℤ) ^ (z p i) * w p i) v)) := by
  classical
  have hd0 : G.det ≠ 0 := hG.ne_zero
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set αI : Fin G.n → ℤ := realVec G.n G.real.pos with hαI
  set α2 : Fin G.n → ℤ := fun i => dyDiag D (Fin.cast hDdim.symm i) with hα2
  set αo : ℕ → Fin G.n → ℤ := fun p i => (p : ℤ) ^ (z p i) * w p i with hαo
  have hr : G.real.pos ≤ G.n := by have := hG.real_dim; omega
  have hneg : G.n - G.real.pos = G.real.neg := by have := hG.real_dim; omega
  -- nonzero entries
  have hαI0 : ∀ i, αI i ≠ 0 := realVec_ne_zero G.n _
  obtain ⟨m2, hm2⟩ := prod_dyDiag D
  have hU : ¬ (2 : ℤ) ∣ unitProd D := odd_unitProd D hDv
  have hU0 : unitProd D ≠ 0 := fun h => hU (h ▸ dvd_zero _)
  have hP2 : ∏ i, α2 i = 2 ^ (2 * m2 + valSum D) * unitProd D := by
    rw [hα2, prod_comp_cast hDdim (dyDiag D), hm2, pow_add, pow_mul]; norm_num; ring
  have hα20 : ∀ i, α2 i ≠ 0 := fun i h => by
    have : ∏ i, α2 i = 0 := Finset.prod_eq_zero (mem_univ i) h
    rw [hP2] at this; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hU0 this
  have hpne : ∀ (p : ℕ) [Fact p.Prime], (p : ℤ) ≠ 0 := fun p hp => by exact_mod_cast hp.out.ne_zero
  have hαo0 : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ i, αo p i ≠ 0 := fun p _ hp2 i =>
    mul_ne_zero (pow_ne_zero _ (hpne p)) (fun h => hw p hp2 i (h ▸ dvd_zero _))
  have hWnd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ ∏ i, w p i := fun p hp hp2 h => by
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp hp.out) _).mp h
    exact hw p hp2 i hi
  -- valuations, unit parts and signs
  have hv2 : valSum D = padicValInt 2 G.det := by
    rw [valSum_eq D hDe, hDs]; exact hG.two_det.1
  have hJ2 : jacobiTwo (unitProd D) = jacobiTwo (unitPart 2 G.det) := by
    rw [← signProd_blockSymbol D hDv hDe, hDs, ← jacobiTwo_eq_unitPart]; exact hG.two_det.2
  have hvo : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∑ i, z p i = padicValInt p G.det := fun p hp hp2 => by
    rw [sum_z_eq (z p) (fun i => (w p i : ℚ_[p])) (hz p hp2), hs p hp2]; exact (hG.odd_det p hp.out hp2).1
  have hJo : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (∏ i, w p i) p = jacobiSym (unitPart p G.det) p :=
    fun p hp hp2 => by
      have h1 := signProd_oddSymbolOfDiag hp2 (z p) (w p) (hw p hp2) (hz p hp2)
      rw [hs p hp2, (hG.odd_det p hp.out hp2).2] at h1
      exact ofInt_inj (jacobiSym_pm_of_not_dvd (hWnd p hp2)) (jacobiSym_pm_of_not_dvd (not_dvd_unitPart hd0)) h1.symm
  have hPo : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∏ i, αo p i = (p : ℤ) ^ padicValInt p G.det * ∏ i, w p i :=
    fun p _ hp2 => by rw [hαo, prod_pow_mul, hvo p hp2]
  have hEo : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → pExcessEntry p (∏ i, αo p i) = pExcessEntry p G.det :=
    fun p _ hp2 => by
      refine pExcessEntry_eq_of ?_ ?_
      · rw [hPo p hp2, padicValInt_pow_mul (hWnd p hp2)]
      · rw [hPo p hp2, unitPart_pow_mul (hWnd p hp2), hJo p hp2]
  -- the excesses of the models are those of the symbols
  have hX1 : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → pExcess p (αo p) = (G.odd p).pExcess p G.N := fun p _ hp2 => by
    rw [← hs p hp2]; exact pExcess_diag_eq hp2 _ _ (hw p hp2) (hz p hp2)
  have hX2 : oddity α2 = G.two.oddity G.N := by
    rw [hα2, oddity_comp_cast hDdim (dyDiag D), oddity_dyDiag D hDv hDe, hDs]
  have hX3 : signature αI = G.signature := by
    rw [hαI, signature_realVec hr, hneg]; rfl
  -- the sign of the determinant
  have hsignI : Int.sign (∏ i, αI i) = Int.sign G.det := by
    rw [hαI, prod_realVec hr, hneg]
    rcases Nat.even_or_odd G.real.neg with he | ho
    · have : 0 < G.det := lt_of_le_of_ne (not_lt.mp fun h => (Nat.not_odd_iff_even.mpr he) (hG.real_sign.mp h))
        hd0.symm
      rw [he.neg_one_pow, Int.sign_eq_one_of_pos this]; rfl
    · have : G.det < 0 := hG.real_sign.mpr ho
      rw [ho.neg_one_pow, Int.sign_eq_neg_one_of_neg this]; rfl
  -- the Hasse invariants
  set εI := RatPlace.infinite.hasseSerre fun i => (αI i : ℚ) with hεI
  set ε2 := (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre fun i => (α2 i : ℚ) with hε2
  have hHI := signature_eq_hasse αI hαI0
  have hH2 := oddity_eq_hasse α2 hα20
  have hHo : ∀ (p : ℕ) [hp : Fact p.Prime], p ≠ 2 → pExcess p (αo p) = pExcessEntry p (∏ i, αo p i) +
      sgn4 ((RatPlace.finite ⟨p, hp.out⟩).hasseSerre fun i => (αo p i : ℚ)) :=
    fun p _ hp2 => pExcess_eq_hasse p hp2 (αo p) (hαo0 p hp2)
  rw [← hεI] at hHI
  rw [← hε2] at hH2
  -- the set of odd primes dividing `G.det`
  set S' : Finset Nat.Primes := (G.det.natAbs.primeFactors.erase 2).subtype Nat.Prime with hS'
  have hS'2 : ∀ q ∈ S', q.1 ≠ 2 := fun q hq => (mem_erase.mp (Finset.mem_subtype.mp hq)).1
  have hFd : (Int.sign G.det : ZMod 8) + ∑ q ∈ S', pExcessEntry q.1 G.det = oddityEntry G.det := by
    have h := oddity_formula (![G.det] : Fin 1 → ℤ) (fun i => by fin_cases i; exact hd0)
    simpa [signature, pExcess, oddity, oddPrimeSet, hS'] using h
  have hCo : (G.signature : ZMod 8) + ∑ q ∈ S', (G.odd q.1).pExcess q.1 G.N = G.two.oddity G.N := by
    have h := hG.oddity_formula
    rw [sum_filter_ne_two _ (fun p hp => Nat.prime_of_mem_primeFactors hp)] at h
    exact h
  -- modulo 4: the unit part at 2
  have hsum4 : ∑ q ∈ S', (2 : ZMod 8) * (G.odd q.1).pExcess q.1 G.N = ∑ q ∈ S', 2 * pExcessEntry q.1 G.det := by
    refine sum_congr rfl fun q hq => ?_
    haveI : Fact q.1.Prime := ⟨q.2⟩
    rw [← hX1 q.1 (hS'2 q hq), hHo q.1 (hS'2 q hq), mul_add, two_mul_sgn4, add_zero, hEo q.1 (hS'2 q hq)]
  have key4 : (2 : ZMod 8) * (unitProd D : ZMod 8) = 2 * (unitPart 2 G.det : ZMod 8) := by
    have hup : unitPart 2 (∏ i, α2 i) = unitProd D := by
      rw [hP2]; exact unitPart_two_pow_mul hU
    have e1 : (2 : ZMod 8) * oddityEntry (∏ i, α2 i) = 2 * oddityEntry G.det := by
      have a1 := congrArg ((2 : ZMod 8) * ·) hCo
      have a2 := congrArg ((2 : ZMod 8) * ·) hFd
      have a3 := congrArg ((2 : ZMod 8) * ·) hHI
      have a4 := congrArg ((2 : ZMod 8) * ·) hH2
      simp only [mul_add, Finset.mul_sum, two_mul_sgn4, add_zero] at a1 a2 a3 a4
      rw [hsum4, ← hX2, a4, ← hX3, a3, hsignI] at a1
      linear_combination a2 - a1
    rw [two_mul_oddityEntry, two_mul_oddityEntry, hup] at e1
    exact e1
  have hU8 : (unitProd D : ZMod 8) = (unitPart 2 G.det : ZMod 8) :=
    zmod8_eq_of_jacobiTwo hU (not_dvd_unitPart hd0) hJ2 key4
  have hE2 : oddityEntry (∏ i, α2 i) = oddityEntry G.det := by
    refine oddityEntry_eq_of ?_ ?_
    · rw [hP2, padicValInt_two_pow_mul hU, hv2]
      constructor
      · intro h; rcases h with ⟨k, hk⟩; exact ⟨k - m2, by omega⟩
      · intro h; rcases h with ⟨k, hk⟩; exact ⟨k + m2, by omega⟩
    · rw [hP2, unitPart_two_pow_mul hU, hU8]
  refine ⟨hU8, ?_⟩
  -- the diagonal models at all places
  set α : RatPlace → Fin G.n → ℚ := placeVec αI α2 αo with hα
  have hαv : ∀ v i, α v i ≠ 0 := by
    intro v i
    cases v with
    | infinite => simpa [hα, placeVec] using hαI0 i
    | finite q =>
      haveI : Fact q.1.Prime := ⟨q.2⟩
      simp only [hα, placeVec]
      split_ifs with hq
      · show ((α2 i : ℤ) : ℚ) ≠ 0; exact_mod_cast hα20 i
      · show ((αo q.1 i : ℤ) : ℚ) ≠ 0; exact_mod_cast hαo0 q.1 hq i
  have hHq : ∀ q : Nat.Primes, q.1 ≠ 2 → pExcess q.1 (αo q.1) = pExcessEntry q.1 (∏ i, αo q.1 i) +
      sgn4 ((RatPlace.finite q).hasseSerre (α (RatPlace.finite q))) := by
    intro q hq2
    haveI : Fact q.1.Prime := ⟨q.2⟩
    have h := pExcess_eq_hasse q.1 hq2 (αo q.1) (hαo0 q.1 hq2)
    simp only [hα, placeVec, if_neg hq2]
    exact h
  have hmemS : ∀ q : Nat.Primes, q ∈ S' ↔ q.1 ≠ 2 ∧ (q.1 : ℤ) ∣ G.det := by
    intro q
    have hm := @Finset.mem_subtype ℕ Nat.Prime _ (G.det.natAbs.primeFactors.erase 2) q
    rw [hS']
    refine hm.trans ?_
    rw [mem_erase, Nat.mem_primeFactors, Int.natCast_dvd]
    constructor
    · rintro ⟨h2, -, h, -⟩; exact ⟨h2, h⟩
    · rintro ⟨h2, h⟩; exact ⟨h2, q.2, h, Int.natAbs_ne_zero.mpr hd0⟩
  -- the Hasse invariant is $1$ at the odd primes not dividing $d$
  have hε1 : ∀ q : Nat.Primes, q.1 ≠ 2 → q ∉ S' → (RatPlace.finite q).hasseSerre (α (RatPlace.finite q)) = 1 := by
    intro q hq2 hqS
    haveI : Fact q.1.Prime := ⟨q.2⟩
    have hnd : ¬ (q.1 : ℤ) ∣ G.det := fun h => hqS ((hmemS q).mpr ⟨hq2, h⟩)
    have hz0 : ∀ i, z q.1 i = 0 := by
      have h := hvo q.1 hq2
      rw [padicValInt.eq_zero_of_not_dvd hnd] at h
      exact fun i => (Finset.sum_eq_zero_iff.mp h) i (mem_univ i)
    have hpx : pExcess q.1 (αo q.1) = 0 := by
      unfold pExcess
      refine Finset.sum_eq_zero fun i _ => ?_
      simp only [hαo, hz0 i, pow_zero, one_mul]
      exact pExcessEntry_of_not_dvd (hw q.1 hq2 i)
    have h := hHq q hq2
    rw [hpx, hEo q.1 hq2, pExcessEntry_of_not_dvd hnd, zero_add] at h
    exact (sgn4_eq_zero_iff (hasseSerre_pm _ _)).mp h.symm
  -- the sum of the Hasse defects over $\{\infty, 2\} \cup S'$ vanishes
  set T : Finset RatPlace := insert RatPlace.infinite (insert (RatPlace.finite (⟨2, Nat.prime_two⟩ : Nat.Primes))
    (S'.map ⟨RatPlace.finite, fun a b h => RatPlace.finite.inj h⟩)) with hT
  have hεI' : RatPlace.infinite.hasseSerre (α RatPlace.infinite) = εI := rfl
  have hε2' : (RatPlace.finite (⟨2, Nat.prime_two⟩ : Nat.Primes)).hasseSerre
      (α (RatPlace.finite (⟨2, Nat.prime_two⟩ : Nat.Primes))) = ε2 := rfl
  have hsumT : ∑ v ∈ T, sgn4 (v.hasseSerre (α v)) = 0 := by
    have hI : RatPlace.infinite ∉ insert (RatPlace.finite (⟨2, Nat.prime_two⟩ : Nat.Primes))
        (S'.map ⟨RatPlace.finite, fun a b h => RatPlace.finite.inj h⟩) := by simp
    have h2T : RatPlace.finite (⟨2, Nat.prime_two⟩ : Nat.Primes) ∉ S'.map ⟨RatPlace.finite, fun a b h => RatPlace.finite.inj h⟩ := by
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
      intro q hq h
      exact hS'2 q hq (by cases h; rfl)
    rw [hT, sum_insert hI, sum_insert h2T, sum_map, hεI', hε2']
    change sgn4 εI + (sgn4 ε2 + ∑ x ∈ S', sgn4 ((RatPlace.finite x).hasseSerre (α (RatPlace.finite x)))) = 0
    have hq_term : ∀ q ∈ S', sgn4 ((RatPlace.finite q).hasseSerre (α (RatPlace.finite q))) =
        (G.odd q.1).pExcess q.1 G.N - pExcessEntry q.1 G.det := by
      intro q hq
      haveI : Fact q.1.Prime := ⟨q.2⟩
      have h := hHq q (hS'2 q hq)
      rw [hX1 q.1 (hS'2 q hq), hEo q.1 (hS'2 q hq)] at h
      linear_combination -h
    rw [sum_congr rfl hq_term, sum_sub_distrib]
    rw [hX3, hsignI] at hHI
    rw [hX2, hE2] at hH2
    linear_combination (-1 : ZMod 8) * hHI + hH2 - neg_sgn4 ε2 + hCo - hFd
  -- finiteness and parity
  have hsub : ∀ v, v.hasseSerre (α v) = -1 → v ∈ T := by
    intro v hv
    cases v with
    | infinite => exact mem_insert_self _ _
    | finite q =>
      by_cases hq2 : q.1 = 2
      · have : q = (⟨2, Nat.prime_two⟩ : Nat.Primes) := Subtype.ext hq2
        subst this
        exact mem_insert_of_mem (mem_insert_self _ _)
      · by_cases hqS : q ∈ S'
        · exact mem_insert_of_mem (mem_insert_of_mem (Finset.mem_map_of_mem _ hqS))
        · rw [hε1 q hq2 hqS] at hv; exact absurd hv (by decide)
  have hset : {v : RatPlace | v.hasseCassels (α v) = -1} = ↑(T.filter fun v => v.hasseSerre (α v) = -1) := by
    ext v
    simp only [Set.mem_setOf_eq, coe_filter, RatPlace.hasseCassels_eq_hasseSerre]
    exact ⟨fun h => ⟨hsub v h, h⟩, fun h => h.2⟩
  have hfin : {v : RatPlace | v.hasseCassels (α v) = -1}.Finite := by
    rw [hset]; exact Finset.finite_toSet _
  have heven : Even {v : RatPlace | v.hasseCassels (α v) = -1}.ncard := by
    rw [hset, Set.ncard_coe_finset]
    exact even_card_of_sum_sgn4 T _ hsumT
  -- the determinants
  have hdet : ∀ v : RatPlace, v.atPlace fun K _ _ => SameSquareClass K (∏ i, α v i) (G.det : ℚ) := by
    intro v
    cases v with
    | infinite =>
      show SameSquareClass ℝ (∏ i, α RatPlace.infinite i) (G.det : ℚ)
      have hX : ∏ i, α RatPlace.infinite i = ((Int.sign G.det : ℤ) : ℚ) := by
        have e : ∏ i, αI i = Int.sign G.det := by
          rw [← hsignI, hαI, prod_realVec hr]
          rcases Nat.even_or_odd (G.n - G.real.pos) with he | ho
          · rw [he.neg_one_pow]; rfl
          · rw [ho.neg_one_pow]; rfl
        simp only [hα, placeVec]
        rw [← e]; push_cast; rfl
      have hs0 : Int.sign G.det ≠ 0 := fun h => hd0 (Int.sign_eq_zero_iff_zero.mp h)
      refine sameSquareClass_of_mul_sq ℝ (by rw [hX]; exact_mod_cast hs0) (by exact_mod_cast hd0)
        (Real.sqrt |(G.det : ℝ)|) ?_
      rw [hX, Real.sq_sqrt (abs_nonneg _)]
      have h1 : Int.sign G.det * G.det = |G.det| := by
        rw [Int.sign_mul_self_eq_natAbs, Int.natCast_natAbs]
      have h2 := congrArg (Int.cast : ℤ → ℝ) h1
      push_cast at h2
      simp only [eq_ratCast, Rat.cast_intCast]
      exact h2
    | finite q =>
      obtain ⟨q, hq⟩ := q
      haveI : Fact q.Prime := ⟨hq⟩
      show SameSquareClass ℚ_[q] (∏ i, α (RatPlace.finite ⟨q, hq⟩) i) (G.det : ℚ)
      have hda : G.det = (q : ℤ) ^ padicValInt q G.det * unitPart q G.det := eq_pow_mul_unitPart G.det
      have hua : ¬ (q : ℤ) ∣ unitPart q G.det := not_dvd_unitPart hd0
      by_cases hq2 : q = 2
      · subst hq2
        have hX : ∏ i, α (RatPlace.finite ⟨2, hq⟩) i = ((2 ^ (2 * m2 + valSum D) * unitProd D : ℤ) : ℚ) := by
          simp only [hα, placeVec, if_pos rfl]
          rw [← hP2]; push_cast; rfl
        have hc : ((unitProd D * unitPart 2 G.det : ℤ) : ZMod 8) = 1 := by
          push_cast
          rw [hU8, ← sq]
          exact Binary.sq_odd_zmod8 (by exact_mod_cast hua)
        obtain ⟨y, hy⟩ := Binary.exists_sq_padic_two hc
        have hX0 : ∏ i, α (RatPlace.finite ⟨2, hq⟩) i ≠ 0 := by
          rw [hX]; exact_mod_cast mul_ne_zero (pow_ne_zero _ two_ne_zero) hU0
        refine sameSquareClass_of_mul_sq ℚ_[2] hX0 (by exact_mod_cast hd0)
          ((2 : ℚ_[2]) ^ (m2 + valSum D) * (y : ℚ_[2])) ?_
        rw [hX]
        simp only [eq_ratCast, Rat.cast_intCast]
        have hy' : ((y : ℚ_[2])) ^ 2 = ((unitProd D * unitPart 2 G.det : ℤ) : ℚ_[2]) := by
          rw [← PadicInt.coe_pow, hy, PadicInt.coe_intCast]
        have e : (G.det : ℚ_[2]) = (((2 : ℤ) ^ padicValInt 2 G.det * unitPart 2 G.det : ℤ) : ℚ_[2]) := by
          exact_mod_cast hda
        rw [mul_pow, hy', e, ← hv2]
        push_cast
        ring
      · have hX : ∏ i, α (RatPlace.finite ⟨q, hq⟩) i =
            (((q : ℤ) ^ padicValInt q G.det * ∏ i, w q i : ℤ) : ℚ) := by
          simp only [hα, placeVec, if_neg hq2]
          rw [← hPo q hq2]; push_cast; rfl
        have hnd : ¬ (q : ℤ) ∣ (∏ i, w q i) * unitPart q G.det := fun h =>
          ((Nat.prime_iff_prime_int.mp hq).dvd_or_dvd h).elim (hWnd q hq2) hua
        have hJ : jacobiSym ((∏ i, w q i) * unitPart q G.det) q = 1 := by
          rw [jacobiSym.mul_left, hJo q hq2]
          rcases jacobiSym_pm_of_not_dvd hua with h | h <;> rw [h] <;> norm_num
        obtain ⟨y, hy⟩ := Binary.exists_sq_padic_odd hq2 hnd hJ
        have hW0 : (∏ i, w q i) ≠ 0 := fun h => hWnd q hq2 (h ▸ dvd_zero _)
        have hX0 : ∏ i, α (RatPlace.finite ⟨q, hq⟩) i ≠ 0 := by
          rw [hX]; exact_mod_cast mul_ne_zero (pow_ne_zero _ (hpne q)) hW0
        refine sameSquareClass_of_mul_sq ℚ_[q] hX0 (by exact_mod_cast hd0)
          ((q : ℚ_[q]) ^ padicValInt q G.det * (y : ℚ_[q])) ?_
        rw [hX]
        simp only [eq_ratCast, Rat.cast_intCast]
        have hy' : ((y : ℚ_[q])) ^ 2 = (((∏ i, w q i) * unitPart q G.det : ℤ) : ℚ_[q]) := by
          rw [← PadicInt.coe_pow, hy, PadicInt.coe_intCast]
        have e : (G.det : ℚ_[q]) = (((q : ℤ) ^ padicValInt q G.det * unitPart q G.det : ℤ) : ℚ_[q]) := by
          exact_mod_cast hda
        rw [mul_pow, hy', e]
        push_cast
        ring
  obtain ⟨a, ha, -, hiso⟩ := Cassels.Ch6.exists_form_of_local hn (G.det : ℚ) (by exact_mod_cast hd0) α hαv hdet
    hfin heven
  exact ⟨a, ha, hiso⟩

end RationalForm

/-! ### Integer matrices of block decompositions; adjusting determinants -/

section IntMatrices

open Cassels

/-- The integer Gram matrix of a block ($e \ge 0$). -/
def blockMatInt : (b : DyBlock) → Matrix (Fin b.dim) (Fin b.dim) ℤ
  | .sq e u => !![2 ^ e.toNat * u]
  | .hyp e => !![0, 2 ^ e.toNat; 2 ^ e.toNat, 0]
  | .ell e => !![2 ^ (e.toNat + 1), 2 ^ e.toNat; 2 ^ e.toNat, 2 ^ (e.toNat + 1)]

/-- The integer Gram matrix of a block decomposition. -/
def dyMatInt : (D : List DyBlock) → Matrix (Fin (dyDim D)) (Fin (dyDim D)) ℤ
  | [] => 0
  | b :: D => orthSumMat (blockMatInt b) (dyMatInt D)

theorem map_blockMatInt (b : DyBlock) (he : 0 ≤ blockExp b) :
    (blockMatInt b).map (Int.castRingHom ℚ_[2]) = b.mat := by
  cases b with
  | sq e u =>
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ e from he)
    change (!![(2 : ℤ) ^ k * u] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.castRingHom ℚ_[2]) =
      !![(2 : ℚ_[2]) ^ (k : ℤ) * u]
    ext i j; fin_cases i; fin_cases j; simp
  | hyp e =>
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ e from he)
    change (!![0, (2 : ℤ) ^ k; 2 ^ k, 0] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ_[2]) =
      (2 : ℚ_[2]) ^ (k : ℤ) • !![0, 1; 1, 0]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | ell e =>
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ e from he)
    change (!![(2 : ℤ) ^ (k + 1), 2 ^ k; 2 ^ k, 2 ^ (k + 1)] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.castRingHom ℚ_[2]) = (2 : ℚ_[2]) ^ (k : ℤ) • !![2, 1; 1, 2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pow_succ, mul_comm]

theorem map_dyMatInt : ∀ (D : List DyBlock), (∀ b ∈ D, 0 ≤ blockExp b) →
    (dyMatInt D).map (Int.castRingHom ℚ_[2]) = dyMat D
  | [], _ => by ext i; exact i.elim0
  | b :: D, he => by
    show (orthSumMat (blockMatInt b) (dyMatInt D)).map (Int.castRingHom ℚ_[2]) = orthSumMat b.mat (dyMat D)
    rw [Ex5.map_orthSum, map_blockMatInt b (he b (List.mem_cons_self ..)),
      map_dyMatInt D fun c hc => he c (List.mem_cons_of_mem _ hc)]

theorem orthSumMat_transpose {R : Type*} [CommRing R] {a b : ℕ} (A : Matrix (Fin a) (Fin a) R)
    (B : Matrix (Fin b) (Fin b) R) : (orthSumMat A B)ᵀ = orthSumMat Aᵀ Bᵀ := by
  rw [dyadic_orthSumMat_eq, dyadic_orthSumMat_eq, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]
  simp

theorem transpose_blockMatInt (b : DyBlock) : (blockMatInt b)ᵀ = blockMatInt b := by
  cases b with
  | sq e u =>
    change (!![(2 : ℤ) ^ e.toNat * u] : Matrix (Fin 1) (Fin 1) ℤ)ᵀ = !![(2 : ℤ) ^ e.toNat * u]
    ext i j; fin_cases i; fin_cases j; rfl
  | hyp e =>
    change (!![0, (2 : ℤ) ^ e.toNat; 2 ^ e.toNat, 0] : Matrix (Fin 2) (Fin 2) ℤ)ᵀ =
      !![0, (2 : ℤ) ^ e.toNat; 2 ^ e.toNat, 0]
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  | ell e =>
    change (!![(2 : ℤ) ^ (e.toNat + 1), 2 ^ e.toNat; 2 ^ e.toNat, 2 ^ (e.toNat + 1)] : Matrix (Fin 2) (Fin 2) ℤ)ᵀ =
      !![(2 : ℤ) ^ (e.toNat + 1), 2 ^ e.toNat; 2 ^ e.toNat, 2 ^ (e.toNat + 1)]
    ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem transpose_dyMatInt : ∀ (D : List DyBlock), (dyMatInt D)ᵀ = dyMatInt D
  | [] => by ext i; exact i.elim0
  | b :: D => by
    show (orthSumMat (blockMatInt b) (dyMatInt D))ᵀ = orthSumMat (blockMatInt b) (dyMatInt D)
    rw [orthSumMat_transpose, transpose_blockMatInt, transpose_dyMatInt D]

theorem det_dyMatInt (D : List DyBlock) (he : ∀ b ∈ D, 0 ≤ blockExp b) :
    (dyMatInt D).det = 2 ^ valSum D * unitProd D := by
  have h := det_dyMat D he
  rw [← map_dyMatInt D he] at h
  have e : ((dyMatInt D).map (Int.castRingHom ℚ_[2])).det = (((dyMatInt D).det : ℤ) : ℚ_[2]) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [e] at h
  exact_mod_cast h

/-- **Adjusting the determinant by a unit square**: a symmetric matrix over $\mathbb Z_p$ is $\mathbb Z_p$-equivalent to
a symmetric matrix of determinant $c^2 \det M$, for any unit $c$ ($n \ge 1$). -/
theorem exists_det_adjust {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℤ_[p])
    (hM : Mᵀ = M) {c : ℤ_[p]} (hc : IsUnit c) :
    ∃ T : GL (Fin n) ℤ_[p], (T.valᵀ * M * T.val)ᵀ = T.valᵀ * M * T.val ∧
      (T.valᵀ * M * T.val).det = c ^ 2 * M.det := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let t : Fin n → ℤ_[p] := Function.update (fun _ => 1) i0 c
  have ht : (Matrix.diagonal t).det = c := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (mem_univ i0)]
    simp
  let T : GL (Fin n) ℤ_[p] := ((Matrix.isUnit_iff_isUnit_det _).mpr (ht ▸ hc)).unit
  refine ⟨T, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hM, Matrix.mul_assoc]
  · show ((Matrix.diagonal t)ᵀ * M * Matrix.diagonal t).det = _
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ht]; ring

end IntMatrices

/-! ### Bridges for the final step -/

section FinalHelpers

open Cassels Siegel Lattices

theorem natAbs_eq_of_local {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ (p : ℕ) [Fact p.Prime], ∃ u : ℤ_[p], IsUnit u ∧ (x : ℤ_[p]) = u * y) : x.natAbs = y.natAbs := by
  refine Nat.eq_of_factorization_eq (Int.natAbs_ne_zero.mpr hx) (Int.natAbs_ne_zero.mpr hy) fun p => ?_
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    change padicValInt p x = padicValInt p y
    obtain ⟨u, hu, hxy⟩ := h p
    have hn : ‖(x : ℤ_[p])‖ = ‖(y : ℤ_[p])‖ := by
      rw [hxy, norm_mul, PadicInt.isUnit_iff.mp hu, one_mul]
    have key : ∀ k : ℕ, ((p : ℤ) ^ k ∣ x ↔ (p : ℤ) ^ k ∣ y) := fun k => by
      rw [← PadicInt.norm_int_le_pow_iff_dvd, ← PadicInt.norm_int_le_pow_iff_dvd, hn]
    apply le_antisymm
    · have := (key _).mp (padicValInt_dvd x)
      rcases (padicValInt_dvd_iff _ _).mp this with h0 | h0
      · exact absurd h0 hy
      · exact h0
    · have := (key _).mpr (padicValInt_dvd y)
      rcases (padicValInt_dvd_iff _ _).mp this with h0 | h0
      · exact absurd h0 hx
      · exact h0
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem diag_eq_gramForm {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) :
    QuadForm.diag a = Cassels.Ch8Ex2.gramForm (Matrix.diagonal a) := by
  ext i j
  simp only [QuadForm.diag, Cassels.Ch8Ex2.gramForm, Matrix.of_apply, Matrix.diagonal_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne, h.ne']
  · simp
  · simp [h.ne', not_lt.mpr h.le]

theorem congrIn_of_isometricIn_diag {K : Type*} [Field K] [CharZero K] {n : ℕ} (a b : Fin n → ℚ)
    (h : (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    CongrIn K (Matrix.diagonal fun i => (a i : K)) (Matrix.diagonal fun i => (b i : K)) := by
  obtain ⟨P, hP, hPx⟩ := h
  have hmap : ∀ c : Fin n → ℚ, (QuadForm.diag c).map (algebraMap ℚ K) =
      Cassels.Ch8Ex2.gramForm (Matrix.diagonal fun i => (c i : K)) := fun c => by
    rw [diag_eq_gramForm, gramForm_map, Matrix.diagonal_map (map_zero _)]
    simp [eq_ratCast]
  have hev : ∀ (c : Fin n → ℚ) (x : Fin n → K), (QuadForm.diag c).evalIn K x =
      (Cassels.Ch8Ex2.gramForm (Matrix.diagonal fun i => (c i : K))).eval x := fun c x => by
    rw [← hmap]
    simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.map, Matrix.map_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  have hiso : IsometricGL (Cassels.Ch8Ex2.gramForm (Matrix.diagonal fun i => (a i : K)))
      (Cassels.Ch8Ex2.gramForm (Matrix.diagonal fun i => (b i : K))) :=
    ⟨Matrix.nonsingInvUnit P hP, fun x => by rw [← hev, ← hev]; exact hPx x⟩
  exact (isometricGL_gramForm_iff (Matrix.diagonal_transpose _) (Matrix.diagonal_transpose _)).mp hiso

theorem congrIn_of_zpEquiv {p : ℕ} [Fact p.Prime] {n : ℕ} {F G : Matrix (Fin n) (Fin n) ℚ_[p]}
    (h : ZpEquiv F G) : CongrIn ℚ_[p] F G := by
  obtain ⟨T, hT⟩ := h
  refine ⟨⟨T.val.map PadicInt.Coe.ringHom, (T⁻¹).val.map PadicInt.Coe.ringHom, ?_, ?_⟩, hT⟩
  · rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem congrIn_of_qequiv {n : ℕ} {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : Ex5.QEquiv F G) :
    CongrIn ℚ_[2] F G := by
  obtain ⟨P, hP, hPG⟩ := h
  exact ⟨Matrix.nonsingInvUnit P hP, hPG⟩

theorem qequiv_cast {m k : ℕ} (h : m = k) {M N : Matrix (Fin m) (Fin m) ℚ_[2]} (hq : Ex5.QEquiv M N) :
    Ex5.QEquiv (M.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) (N.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) := by
  subst h; simpa using hq

theorem congrIn_diagonal_scale {K : Type*} [CommRing K] {n : ℕ} (x t : Fin n → K) (ht : IsUnit (∏ i, t i)) :
    CongrIn K (Matrix.diagonal x) (Matrix.diagonal fun i => t i ^ 2 * x i) := by
  have hT : IsUnit (Matrix.diagonal t).det := by rwa [Matrix.det_diagonal]
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hT).unit, ?_⟩
  show (Matrix.diagonal t)ᵀ * Matrix.diagonal x * Matrix.diagonal t = _
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; ring

/-- From `IsometricGL` of an integer form (with Hessian $A + A$) and a Gram form over a characteristic-zero domain, the
congruence of the Gram matrices. -/
theorem congr_of_isometricGL_hessian {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {n : ℕ}
    (f : QuadForm ℤ n) (A : Matrix (Fin n) (Fin n) ℤ) (hA : f.hessian = A + A) (M : Matrix (Fin n) (Fin n) K)
    (hM : Mᵀ = M) (h : IsometricGL (f.map (Int.castRingHom K)) (Cassels.Ch8Ex2.gramForm M)) :
    ∃ T : GL (Fin n) K, T.valᵀ * A.map (Int.castRingHom K) * T.val = M := by
  obtain ⟨g, hg⟩ := h
  have h1 := Cassels.Ch8Ex2.hessian_congr hg
  rw [Cassels.Ch8Ex2.hessian_gramForm, hM, Siegel.hessian_map, hA, Matrix.map_add _ (map_add _)] at h1
  refine ⟨g, ?_⟩
  ext i j
  have := congrFun (congrFun h1 i) j
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply] at this
  exact mul_left_cancel₀ (two_ne_zero (α := K)) (by linear_combination this)

end FinalHelpers

/-! ### Theorem 11 -/

section Main

open Cassels Siegel Lattices

/-- **The system of local symbols of an integral form** (Conway–Sloane, §7.7–7.8): the symmetric integer matrix $A$
(the Gram matrix of a classically integral form $f(x) = xAx^{\mathsf T}$ in $n$ variables) has determinant $d$,
$(-1)$-adic symbol $+^r-^s$ (it is $\mathbb R$-equivalent to $\langle 1^r, (-1)^s\rangle$), $p$-adic symbol `G.odd p` at
every odd prime (`IsOddSymbolOf`) and 2-adic symbol `G.two` (`IsTwoSymbolOf`, one of its 2-adic symbols). -/
@[kb "conwaysloane1999" "Ch. 15, §7.7–7.8, pp. 382–384"]
def GenusSymbolData.IsSymbolsOf (G : GenusSymbolData) (A : Matrix (Fin G.n) (Fin G.n) ℤ) : Prop :=
  Aᵀ = A ∧ A.det = G.det ∧
    CongrIn ℝ (A.map (Int.castRingHom ℝ)) (Matrix.diagonal fun i => ((realVec G.n G.real.pos i : ℤ) : ℝ)) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → IsOddSymbolOf p (A.map (Int.castRingHom ℚ_[p])) (G.odd p)) ∧
    IsTwoSymbolOf (A.map (Int.castRingHom ℚ_[2])) G.two

theorem exists_unit_sq_mul {p : ℕ} [Fact p.Prime] {X d W a : ℤ} (v : ℕ) (hX : X = (p : ℤ) ^ v * W)
    (hd : d = (p : ℤ) ^ v * a) (hW : ¬ (p : ℤ) ∣ W) (ha : ¬ (p : ℤ) ∣ a) (y : ℤ_[p]) (hy : y ^ 2 = W * a) :
    ∃ c : ℤ_[p], IsUnit c ∧ c ^ 2 * (X : ℤ_[p]) = d := by
  have hWa : IsUnit ((W * a : ℤ) : ℤ_[p]) := Binary.isUnit_intCast_padic fun h =>
    ((Nat.prime_iff_prime_int.mp Fact.out).dvd_or_dvd h).elim hW ha
  have hyu : IsUnit y := by
    have : IsUnit (y ^ 2) := by rw [hy]; exact_mod_cast hWa
    exact (isUnit_pow_iff two_ne_zero).mp this
  set u := hyu.unit with hu_def
  have hu : (u : ℤ_[p]) * ↑u⁻¹ = 1 := Units.mul_inv u
  have hyu' : (u : ℤ_[p]) ^ 2 = W * a := by rw [hu_def, IsUnit.unit_spec]; exact_mod_cast hy
  refine ⟨(a : ℤ_[p]) * ↑u⁻¹, (Binary.isUnit_intCast_padic ha).mul (Units.isUnit _), ?_⟩
  rw [hX, hd]
  push_cast
  linear_combination (-((p : ℤ_[p]) ^ v * a * (↑u⁻¹ : ℤ_[p]) ^ 2)) * hyu' +
    ((p : ℤ_[p]) ^ v * a * ((u : ℤ_[p]) * ↑u⁻¹ + 1)) * hu

/-- **Theorem 11 for $n \ge 1$.** -/
theorem theorem11_pos (G : GenusSymbolData) (hG : G.Conditions) (hn : 1 ≤ G.n) :
    ∃ A : Matrix (Fin G.n) (Fin G.n) ℤ, G.IsSymbolsOf A := by
  classical
  have hd0 : G.det ≠ 0 := hG.ne_zero
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : G.real.pos ≤ G.n := by have := hG.real_dim; omega
  have hneg : G.n - G.real.pos = G.real.neg := by have := hG.real_dim; omega
  -- local data at the odd primes
  have H : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ (z : Fin G.n → ℕ) (w : Fin G.n → ℤ), (∀ i, z i < G.N) ∧
      (∀ i, ¬ (p : ℤ) ∣ w i) ∧ oddSymbolOfDiag p z (fun i => (w i : ℚ_[p])) = G.odd p :=
    fun p hp hp2 => exists_int_diag_dim hp2 (hG.odd_supp p) (hG.odd_exists p hp.out hp2) (hG.odd_dim p hp.out hp2)
  choose! z w hz hw hs using H
  -- local data at 2
  set D := twoRealization G.two G.N with hD
  have hDv : ∀ b ∈ D, b.Valid := twoRealization_valid hG.two_exists G.N
  have hDe : ∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < G.N :=
    fun b hb => ⟨twoRealization_exp _ _ b hb, twoRealization_exp_lt _ _ b hb⟩
  have hDdim : dyDim D = G.n := (dyDim_twoRealization hG.two_exists G.N).trans hG.two_dim
  have hDs : blockSymbol D = G.two := blockSymbol_twoRealization hG.two_supp hG.two_exists
  obtain ⟨hU8, a, ha, hiso⟩ := exists_rational_form G hG hn z w hz hw hs D hDv hDe hDdim hDs
  -- the local integer matrices
  set F2Z : Matrix (Fin G.n) (Fin G.n) ℤ := (dyMatInt D).submatrix (Fin.cast hDdim.symm) (Fin.cast hDdim.symm)
    with hF2Z
  set L : ℕ → Matrix (Fin G.n) (Fin G.n) ℤ := fun p =>
    if p = 2 then F2Z else Matrix.diagonal fun i => (p : ℤ) ^ (z p i) * w p i with hL
  have hLsym : ∀ p, (L p)ᵀ = L p := by
    intro p
    simp only [hL]
    split_ifs
    · rw [hF2Z, Matrix.transpose_submatrix, transpose_dyMatInt]
    · exact Matrix.diagonal_transpose _
  have hF2map : F2Z.map (Int.castRingHom ℚ_[2]) =
      (dyMat D).submatrix (Fin.cast hDdim.symm) (Fin.cast hDdim.symm) := by
    rw [hF2Z, ← Matrix.submatrix_map, map_dyMatInt D fun b hb => (hDe b hb).1]
  -- adjusting the determinants to `d`
  have hc : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℤ_[p], IsUnit c ∧ c ^ 2 * (((L p).det : ℤ) : ℤ_[p]) = (G.det : ℤ_[p]) := by
    intro p hp
    have hda : G.det = (p : ℤ) ^ padicValInt p G.det * unitPart p G.det := eq_pow_mul_unitPart G.det
    have hua : ¬ (p : ℤ) ∣ unitPart p G.det := not_dvd_unitPart hd0
    by_cases hp2 : p = 2
    · subst hp2
      have hdet : (L 2).det = (2 : ℤ) ^ padicValInt 2 G.det * unitProd D := by
        have e : L 2 = F2Z := by simp [hL]
        rw [e, hF2Z]
        rw [show (Fin.cast hDdim.symm : Fin G.n → Fin (dyDim D)) = ⇑(finCongr hDdim.symm) from rfl,
          Matrix.det_submatrix_equiv_self, det_dyMatInt D fun b hb => (hDe b hb).1, valSum_eq D hDe, hDs,
          hG.two_det.1]
      have hcU : ((unitProd D * unitPart 2 G.det : ℤ) : ZMod 8) = 1 := by
        push_cast; rw [hU8, ← sq]; exact Binary.sq_odd_zmod8 (by exact_mod_cast hua)
      obtain ⟨y, hy⟩ := Binary.exists_sq_padic_two hcU
      exact exists_unit_sq_mul (p := 2) _ hdet hda (odd_unitProd D hDv) hua y (by rw [hy]; push_cast; ring)
    · have hvo : ∑ i, z p i = padicValInt p G.det := by
        rw [sum_z_eq (z p) (fun i => (w p i : ℚ_[p])) (hz p hp2), hs p hp2]; exact (hG.odd_det p hp.out hp2).1
      have hWnd : ¬ (p : ℤ) ∣ ∏ i, w p i := fun h => by
        obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp hp.out) _).mp h
        exact hw p hp2 i hi
      have hJo : jacobiSym (∏ i, w p i) p = jacobiSym (unitPart p G.det) p := by
        have h1 := signProd_oddSymbolOfDiag hp2 (z p) (w p) (hw p hp2) (hz p hp2)
        rw [hs p hp2, (hG.odd_det p hp.out hp2).2] at h1
        exact ofInt_inj (jacobiSym_pm_of_not_dvd hWnd) (jacobiSym_pm_of_not_dvd hua) h1.symm
      have hdet : (L p).det = (p : ℤ) ^ padicValInt p G.det * ∏ i, w p i := by
        simp only [hL, if_neg hp2, Matrix.det_diagonal]
        rw [prod_pow_mul, hvo]
      have hnd : ¬ (p : ℤ) ∣ (∏ i, w p i) * unitPart p G.det := fun h =>
        ((Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h).elim hWnd hua
      have hJ : jacobiSym ((∏ i, w p i) * unitPart p G.det) p = 1 := by
        rw [jacobiSym.mul_left, hJo]
        rcases jacobiSym_pm_of_not_dvd hua with h | h <;> rw [h] <;> norm_num
      obtain ⟨y, hy⟩ := Binary.exists_sq_padic_odd hp2 hnd hJ
      exact exists_unit_sq_mul _ hdet hda hWnd hua y (by rw [hy]; push_cast; ring)
  choose c hcu hcd using hc
  -- the local Gram matrices of determinant `d`
  have Hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ Gp : Matrix (Fin G.n) (Fin G.n) ℤ_[p], Gpᵀ = Gp ∧
      Gp.det = (G.det : ℤ_[p]) ∧ ZpEquiv ((L p).map (Int.castRingHom ℚ_[p])) (Gp.map PadicInt.Coe.ringHom) := by
    intro p hp
    set M := (L p).map (Int.castRingHom ℤ_[p]) with hM
    have hMs : Mᵀ = M := by rw [hM, ← Matrix.transpose_map, hLsym]
    obtain ⟨T, hTs, hTd⟩ := exists_det_adjust hn M hMs (hcu p)
    refine ⟨T.valᵀ * M * T.val, hTs, ?_, T, ?_⟩
    · rw [hTd, ← hcd p, hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    · have e : (L p).map (Int.castRingHom ℚ_[p]) = M.map PadicInt.Coe.ringHom := by
        rw [hM, Matrix.map_map]; congr 1
      rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  choose Gp hGs hGd hGe using Hloc
  -- the local forms
  let fp : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] G.n := fun p _ => Cassels.Ch8Ex2.gramForm (Gp p)
  have hfp : ∀ (p : ℕ) [Fact p.Prime], (fp p).hessian.det = ((2 ^ G.n * G.det : ℤ) : ℤ_[p]) := by
    intro p hp
    show (Cassels.Ch8Ex2.gramForm (Gp p)).hessian.det = _
    rw [Cassels.Ch8Ex2.hessian_gramForm, hGs, ← two_smul ℤ_[p], Matrix.det_smul, hGd, Fintype.card_fin]
    push_cast; ring
  -- the real form
  set i0 : Fin G.n := ⟨0, hn⟩ with hi0
  set eR : Fin G.n → ℝ := Function.update (fun i => ((realVec G.n G.real.pos i : ℤ) : ℝ)) i0
    (|(G.det : ℝ)| * ((realVec G.n G.real.pos i0 : ℤ) : ℝ)) with heR
  have hprodR : ∏ i, realVec G.n G.real.pos i = Int.sign G.det := by
    rw [prod_realVec hr, hneg]
    rcases Nat.even_or_odd G.real.neg with he | ho
    · have : 0 < G.det := lt_of_le_of_ne (not_lt.mp fun h => (Nat.not_odd_iff_even.mpr he) (hG.real_sign.mp h))
        hd0.symm
      rw [he.neg_one_pow, Int.sign_eq_one_of_pos this]
    · have : G.det < 0 := hG.real_sign.mpr ho
      rw [ho.neg_one_pow, Int.sign_eq_neg_one_of_neg this]
  have hsabs : (Int.sign G.det : ℝ) * |(G.det : ℝ)| = G.det := by
    have h1 : Int.sign G.det * |G.det| = G.det := by
      rcases lt_or_gt_of_ne hd0 with h | h
      · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg h]; ring
      · rw [Int.sign_eq_one_of_pos h, abs_of_pos h]; ring
    exact_mod_cast h1
  have hprodE : ∏ i, eR i = G.det := by
    rw [heR, Finset.prod_update_of_mem (mem_univ i0)]
    have h1 := Finset.prod_sdiff (f := fun i => ((realVec G.n G.real.pos i : ℤ) : ℝ)) (Finset.subset_univ {i0})
    rw [Finset.prod_singleton] at h1
    have h3 : ∏ i, ((realVec G.n G.real.pos i : ℤ) : ℝ) = (Int.sign G.det : ℝ) := by
      rw [← hprodR]; push_cast; rfl
    linear_combination |(G.det : ℝ)| * h1 + |(G.det : ℝ)| * h3 + hsabs
  let finf : QuadForm ℝ G.n := Cassels.Ch8Ex2.gramForm (Matrix.diagonal eR)
  have hfinf : finf.hessian.det = ((2 ^ G.n * G.det : ℤ) : ℝ) := by
    show (Cassels.Ch8Ex2.gramForm (Matrix.diagonal eR)).hessian.det = _
    rw [Cassels.Ch8Ex2.hessian_gramForm, Matrix.diagonal_transpose, ← two_smul ℝ, Matrix.det_smul,
      Matrix.det_diagonal, hprodE, Fintype.card_fin]
    push_cast; ring
  have hscale : CongrIn ℝ (Matrix.diagonal fun i => ((realVec G.n G.real.pos i : ℤ) : ℝ)) (Matrix.diagonal eR) := by
    have h1 := congrIn_diagonal_scale (fun i => ((realVec G.n G.real.pos i : ℤ) : ℝ))
      (Function.update (fun _ => (1 : ℝ)) i0 (Real.sqrt |(G.det : ℝ)|)) (by
        rw [Finset.prod_update_of_mem (mem_univ i0)]
        simp only [prod_const_one, mul_one]
        exact (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hd0))).ne'.isUnit)
    convert h1 using 2
    funext i
    rw [heR]
    by_cases hi : i = i0
    · subst hi; simp [Real.sq_sqrt (abs_nonneg _)]
    · simp [hi]
  -- the rational form and its local equivalences
  let g : QuadForm ℚ G.n := QuadForm.diag a
  have hgmap : ∀ (K : Type) [Field K] [CharZero K],
      g.map (Rat.castHom K) = Cassels.Ch8Ex2.gramForm (Matrix.diagonal fun i => (a i : K)) := by
    intro K _ _
    show (QuadForm.diag a).map _ = _
    rw [diag_eq_gramForm, gramForm_map, Matrix.diagonal_map (map_zero _)]
    rfl
  have hg : ∀ (p : ℕ) [Fact p.Prime],
      IsometricGL (g.map (Rat.castHom ℚ_[p])) ((fp p).map PadicInt.Coe.ringHom) := by
    intro p hp
    rw [hgmap, show (fp p).map PadicInt.Coe.ringHom = Cassels.Ch8Ex2.gramForm ((Gp p).map PadicInt.Coe.ringHom)
      from gramForm_map _ _]
    refine (isometricGL_gramForm_iff (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, hGs])).mpr ?_
    have h1 := congrIn_of_isometricIn_diag (K := ℚ_[p]) _ _ (hiso (RatPlace.finite ⟨p, hp.out⟩))
    refine h1.trans (CongrIn.trans ?_ (congrIn_of_zpEquiv (hGe p)))
    by_cases hp2 : p = 2
    · subst hp2
      have e : L 2 = F2Z := by simp [hL]
      rw [e, hF2map]
      have hq := qequiv_cast hDdim (qequiv_dyDiag D fun b hb => (hDe b hb).1)
      have hd : (Matrix.diagonal fun i => ((dyDiag D i : ℤ) : ℚ_[2])).submatrix (Fin.cast hDdim.symm)
          (Fin.cast hDdim.symm) = Matrix.diagonal fun i => ((placeVec (realVec G.n G.real.pos)
            (fun i => dyDiag D (Fin.cast hDdim.symm i)) (fun p i => (p : ℤ) ^ (z p i) * w p i)
            (RatPlace.finite ⟨2, hp.out⟩) i : ℚ) : ℚ_[2]) := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, placeVec, if_pos rfl, Fin.cast_inj]
        split_ifs <;> simp
      rw [hd] at hq
      exact (congrIn_of_qequiv hq).symm
    · have e : L p = Matrix.diagonal fun i => (p : ℤ) ^ (z p i) * w p i := by simp [hL, hp2]
      rw [e, Matrix.diagonal_map (map_zero _)]
      have : (fun i => ((placeVec (realVec G.n G.real.pos) (fun i => dyDiag D (Fin.cast hDdim.symm i))
          (fun p i => (p : ℤ) ^ (z p i) * w p i) (RatPlace.finite ⟨p, hp.out⟩) i : ℚ) : ℚ_[p])) =
          fun i => (Int.castRingHom ℚ_[p]) ((p : ℤ) ^ (z p i) * w p i) := by
        funext i
        simp only [placeVec, if_neg hp2]
        simp
      rw [this]
      exact CongrIn.refl _
  have hginf : IsometricGL (g.map (Rat.castHom ℝ)) finf := by
    rw [hgmap]
    refine (isometricGL_gramForm_iff (Matrix.diagonal_transpose _) (Matrix.diagonal_transpose _)).mpr ?_
    have h1 := congrIn_of_isometricIn_diag (K := ℝ) _ _ (hiso RatPlace.infinite)
    refine h1.trans (CongrIn.trans ?_ hscale)
    have : (fun i => ((placeVec (realVec G.n G.real.pos) (fun i => dyDiag D (Fin.cast hDdim.symm i))
        (fun p i => (p : ℤ) ^ (z p i) * w p i) RatPlace.infinite i : ℚ) : ℝ)) =
        fun i => ((realVec G.n G.real.pos i : ℤ) : ℝ) := by
      funext i; simp [placeVec]
    rw [this]
    exact CongrIn.refl _
  -- the integral form (Cassels Ch. 9, Thm. 1.2)
  have hD0 : (2 ^ G.n * G.det : ℤ) ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hd0
  obtain ⟨f, hf, hfR, -⟩ := Siegel.exists_form_of_local_forms hD0 fp hfp finf hfinf g hg hginf
  -- `f` is classically integral: its Hessian is even
  have hev : ∀ i j, (2 : ℤ) ∣ f.hessian i j := by
    intro i j
    obtain ⟨g2, hg2⟩ := (hf 2).symm
    have h1 := Cassels.Ch8Ex2.hessian_congr hg2
    rw [Cassels.Ch8Ex2.hessian_gramForm, hGs, Siegel.hessian_map] at h1
    have h2 := congrFun (congrFun h1 i) j
    rw [Matrix.map_apply] at h2
    have h2' : ((f.hessian i j : ℤ) : ℤ_[2]) = 2 * ((g2.valᵀ * Gp 2 * g2.val) i j) := by
      rw [← eq_intCast (Int.castRingHom ℤ_[2]), ← h2]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]; ring
    refine Binary.int_dvd_of_padic_dvd (p := 2) ⟨(g2.valᵀ * Gp 2 * g2.val) i j, ?_⟩
    rw [h2']; push_cast; ring
  set A : Matrix (Fin G.n) (Fin G.n) ℤ := Matrix.of fun i j => f.hessian i j / 2 with hA
  have hA2 : f.hessian = A + A := by
    ext i j
    simp only [hA, Matrix.add_apply, Matrix.of_apply]
    rw [← two_mul, Int.mul_ediv_cancel' (hev i j)]
  have hAs : Aᵀ = A := by
    ext i j
    simp only [hA, Matrix.transpose_apply, Matrix.of_apply, QuadForm.hessian, Matrix.add_apply]
    try ring_nf
  -- local equivalences of `A`
  have hAp : ∀ (p : ℕ) [Fact p.Prime], ∃ T : GL (Fin G.n) ℤ_[p],
      T.valᵀ * A.map (Int.castRingHom ℤ_[p]) * T.val = Gp p :=
    fun p _ => congr_of_isometricGL_hessian f A hA2 (Gp p) (hGs p) (hf p)
  have hAz : ∀ (p : ℕ) [Fact p.Prime], ZpEquiv (A.map (Int.castRingHom ℚ_[p])) ((L p).map (Int.castRingHom ℚ_[p])) := by
    intro p hp
    obtain ⟨T, hT⟩ := hAp p
    refine ZpEquiv.trans ⟨T, ?_⟩ (hGe p).symm
    have e : A.map (Int.castRingHom ℚ_[p]) = (A.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom := by
      rw [Matrix.map_map]; congr 1
    rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hT]
  obtain ⟨TR, hTR⟩ := congr_of_isometricGL_hessian (K := ℝ) f A hA2 (Matrix.diagonal eR)
    (Matrix.diagonal_transpose _) hfR
  -- the determinant
  have hdetA : A.det = G.det := by
    have hAd0 : A.det ≠ 0 := by
      intro h0
      obtain ⟨T, hT⟩ := hAp 2
      have := congrArg Matrix.det hT
      rw [Matrix.det_mul, Matrix.det_mul, hGd, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0] at this
      simp at this
      exact hd0 (by exact_mod_cast this.symm)
    have habs : A.det.natAbs = G.det.natAbs := by
      refine natAbs_eq_of_local hAd0 hd0 fun p hp => ?_
      obtain ⟨T, hT⟩ := hAp p
      have hTu : IsUnit T.val.det := (Matrix.isUnit_iff_isUnit_det _).mp T.isUnit
      obtain ⟨v, hv⟩ := hTu
      refine ⟨↑v⁻¹ ^ 2, (Units.isUnit _).pow 2, ?_⟩
      have := congrArg Matrix.det hT
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hGd, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, ← hv] at this
      have hvv : (v : ℤ_[p]) * ↑v⁻¹ = 1 := Units.mul_inv v
      have this' : (v : ℤ_[p]) * (A.det : ℤ_[p]) * v = G.det := by simpa using this
      rw [← this']
      linear_combination (-((A.det : ℤ_[p])) * ((v : ℤ_[p]) * ↑v⁻¹ + 1)) * hvv
    have hsgn : Int.sign A.det = Int.sign G.det := by
      have := congrArg Matrix.det hTR
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hprodE,
        ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      have hT0 : TR.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp TR.isUnit).ne_zero
      have hpos : 0 < TR.val.det * TR.val.det := mul_self_pos.mpr hT0
      change TR.val.det * ((A.det : ℤ) : ℝ) * TR.val.det = (G.det : ℝ) at this
      rcases lt_or_gt_of_ne hd0 with h | h
      · have : ((A.det : ℤ) : ℝ) < 0 := by nlinarith [(show (G.det : ℝ) < 0 by exact_mod_cast h)]
        rw [Int.sign_eq_neg_one_of_neg h, Int.sign_eq_neg_one_of_neg (by exact_mod_cast this)]
      · have : 0 < ((A.det : ℤ) : ℝ) := by nlinarith [(show 0 < (G.det : ℝ) by exact_mod_cast h)]
        rw [Int.sign_eq_one_of_pos h, Int.sign_eq_one_of_pos (by exact_mod_cast this)]
    rw [← Int.sign_mul_natAbs A.det, ← Int.sign_mul_natAbs G.det, hsgn, habs]
  refine ⟨A, hAs, hdetA, ?_, ?_, ?_⟩
  · exact CongrIn.trans (show CongrIn ℝ _ _ from ⟨TR, hTR⟩) hscale.symm
  · intro p hp hp2
    refine ⟨z p, fun i => (w p i : ℚ_[p]), fun i => ?_, ?_, (hs p hp2).symm⟩
    · show ‖(w p i : ℚ_[p])‖ = 1
      obtain ⟨u, hu⟩ := exists_unit_of_not_dvd (p := p) (w p i) (hw p hp2 i)
      have h1 : ((u : ℤ_[p]) : ℚ_[p]) = (w p i : ℚ_[p]) := by rw [hu]; simp
      rw [← h1, PadicInt.norm_coe]
      exact PadicInt.isUnit_iff.mp u.isUnit
    · have e : (L p).map (Int.castRingHom ℚ_[p]) =
          Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z p i) * (w p i : ℚ_[p]) := by
        simp only [hL, if_neg hp2, Matrix.diagonal_map (map_zero _)]
        simp
      rw [← e]; exact hAz p
  · refine ⟨D, hDv, fun b hb => (hDe b hb).1, hDdim, ?_, hDs.symm⟩
    have e : L 2 = F2Z := by simp [hL]
    have := hAz 2
    rw [e, hF2map] at this
    exact this


end Main

/-! ### Theorem 11, all dimensions -/

section Final

open Cassels

/-- **Theorem 11 in dimension $0$**: the only system of symbols is the trivial one, $d = 1$. -/
theorem theorem11_zero (G : GenusSymbolData) (hG : G.Conditions) (hn0 : G.n = 0) :
    ∃ A : Matrix (Fin G.n) (Fin G.n) ℤ, G.IsSymbolsOf A := by
  classical
  have hE : IsEmpty (Fin G.n) := by rw [hn0]; infer_instance
  have hd0 : G.det ≠ 0 := hG.ne_zero
  -- every constituent is zero-dimensional
  have hodd0 : ∀ p, p.Prime → p ≠ 2 → ∀ k, G.odd p k = OddFactor.trivial := by
    intro p hp hp2 k
    by_cases hk : k < G.N
    · have h1 := hG.odd_dim p hp hp2
      rw [hn0] at h1
      have hd : (G.odd p k).dim = 0 := (Finset.sum_eq_zero_iff.mp h1) k (mem_range.mpr hk)
      have hs : (G.odd p k).sign = .plus := hG.odd_exists p hp hp2 k hd
      cases h : G.odd p k; simp_all [OddFactor.trivial]
    · exact hG.odd_supp p k (by omega)
  have htwo0 : ∀ k, G.two k = TwoFactor.trivial := by
    intro k
    by_cases hk : k < G.N
    · have h1 := hG.two_dim
      rw [hn0] at h1
      have hd : (G.two k).dim = 0 := (Finset.sum_eq_zero_iff.mp h1) k (mem_range.mpr hk)
      obtain ⟨h0, -, -, hpar, hII⟩ := hG.two_exists k
      obtain ⟨ht, hs⟩ := h0 hd
      have ho := hII ht
      cases h : G.two k; simp_all [TwoFactor.trivial]
    · exact hG.two_supp k (by omega)
  -- the determinant is $1$
  have hv : ∀ p, p.Prime → padicValInt p G.det = 0 := by
    intro p hp
    by_cases hp2 : p = 2
    · subst hp2
      rw [← hG.two_det.1]
      exact Finset.sum_eq_zero fun k _ => by rw [htwo0 k]; simp [TwoFactor.trivial]
    · rw [← (hG.odd_det p hp hp2).1]
      exact Finset.sum_eq_zero fun k _ => by rw [hodd0 p hp hp2 k]; simp [OddFactor.trivial]
  have habs : G.det.natAbs = 1 := by
    refine Nat.eq_of_factorization_eq (Int.natAbs_ne_zero.mpr hd0) one_ne_zero fun p => ?_
    by_cases hp : p.Prime
    · rw [Nat.factorization_def _ hp, Nat.factorization_one]
      have := hv p hp
      exact this
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hpos : 0 < G.det := by
    rcases lt_or_gt_of_ne hd0 with h | h
    · have := hG.real_sign.mp h
      have h2 := hG.real_dim
      rw [hn0] at h2
      have : G.real.neg = 0 := by omega
      simp_all
    · exact h
  have hdet1 : G.det = 1 := by omega
  refine ⟨0, ?_, ?_, ?_, ?_, ?_⟩
  · ext i; exact hE.elim i
  · rw [Matrix.det_isEmpty, hdet1]
  · exact ⟨1, Subsingleton.elim _ _⟩
  · intro p hp hp2
    refine ⟨fun i => hE.elim i, fun i => hE.elim i, fun i => hE.elim i, ⟨1, Subsingleton.elim _ _⟩, ?_⟩
    funext k
    rw [hodd0 p hp.out hp2 k]
    simp [oddSymbolOfDiag, OddFactor.trivial, Fintype.card_eq_zero]
  · refine ⟨[], by simp, by simp, hn0.symm, ⟨1, Subsingleton.elim _ _⟩, ?_⟩
    funext k
    rw [htwo0 k]
    simp [blockSymbol, TwoFactor.trivial, Sign.prodList]

/-- **Theorem 11** (Conway–Sloane, §7.7, p. 383): *a putative system of local symbols satisfying the conditions
(29)–(35) is the system of symbols of an integral quadratic form*: there is a symmetric integer matrix $A$ (the Gram
matrix of a classically integral form in $n$ variables) of determinant $d$, real signature $+^r-^s$, with the given
$p$-adic symbol at every odd prime $p$ and the given 2-adic symbol (as one of its 2-adic symbols, §7.5).

*Proof* (the book gives none, p. 378): local realizations (`LocalExistence.lean`), the oddity formula (30) through the
excess–Hasse relations (the parity of the number of places with Hasse invariant $-1$, and the 2-adic determinant
class), Cassels Ch. 6, Thm. 1.3 (a rational form with the prescribed local classes) and Cassels Ch. 9, Thm. 1.2 (an
integral form with the prescribed $\mathbb Z_p$-classes); see the file header. Unconditional. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, Thm. 11, p. 383"]
theorem theorem11 (G : GenusSymbolData) (hG : G.Conditions) :
    ∃ A : Matrix (Fin G.n) (Fin G.n) ℤ, G.IsSymbolsOf A := by
  rcases Nat.eq_zero_or_pos G.n with h | h
  · exact theorem11_zero G hG h
  · exact theorem11_pos G hG h

end Final

end QuadFormsKB.ConwaySloane
