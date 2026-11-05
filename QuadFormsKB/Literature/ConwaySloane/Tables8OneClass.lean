/-
# Conway–Sloane, Ch. 15, §8: "one class" claims for indefinite forms

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §8, pp. 386–388, and the
remarks of §1 (p. 353) and §7 (p. 378) (`conwaysloane1999`).

**Layer.** A form is its symmetric integer Gram matrix $A$ (classically integral), as in `Spinor.lean`; the genus and
class are those of `MoreThanOneClass`; "indefinite" is `Lattices.IsIndefinite (csQ A)`.

**Proves** (all unconditional; they use Theorem 19 and Corollary 22 of §9.7, which are proved in the library)
* `oneClass_of_natAbs_lt`: an indefinite form of dimension $n \ge 3$ with $\lvert\det A\rvert < 128$ has one class in
  its genus (§1, p. 353; §7, p. 378); `oneClass_of_natAbs_le_eleven` is the instance for the indefinite cases of
  Table 15.4 ($\lvert\det A\rvert \le 11$, §8.1, p. 386).
* `IsPElementary` and `oneClass_of_isPElementary`: an indefinite $p$-elementary form of dimension $n \ge 3$ has one
  class in its genus (Thm. 13 (a), (b), pp. 386–388). *Proof:* by Theorem 19 a genus with more than one class has a
  $p'$-adic diagonalization (basis $\gamma$ of $\mathbb Z_{p'}^n$) with pairwise different absolute values of the
  diagonal entries; for a $p$-elementary form the entries $a_k$ of the diagonal $\gamma^{\mathsf T}A\gamma$ satisfy
  $\lvert p\rvert_{p'} \le \lvert a_k\rvert_{p'} \le 1$ (since $pA^{-1}$ is integral), which leaves at most two
  absolute values, contradicting $n \ge 3$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Cor22

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

open scoped Classical

variable {n : ℕ}

/-! ### Small determinants -/

theorem d0_ge_128 (hn : 3 ≤ n) : 128 ≤ d0 n := by
  unfold d0
  by_cases h3 : n = 3
  · subst h3; simp
  · have h4 : 4 ≤ n := by omega
    have hc : 6 ≤ n.choose 2 := by
      have := Nat.choose_le_choose 2 h4
      simpa [Nat.choose] using this
    have h5 : 5 ^ 6 ≤ 5 ^ n.choose 2 := Nat.pow_le_pow_right (by norm_num) hc
    have : (128 : ℕ) ≤ 5 ^ 6 := by norm_num
    simp only [show n ≠ 2 by omega, h3, ite_false]
    split_ifs
    · omega
    · omega

/-- **Indefinite forms of dimension $\ge 3$ with $\lvert\det\rvert < 128$ have one class in their genus**
(Conway–Sloane, §1, p. 353 and §7, p. 378: "for indefinite forms of dimension $\ge 3$ there is one class in the genus
whenever $\lvert\det f\rvert < 128$"). Follows from Cor. 22 ($d_0(n) \ge 128$ for $n \ge 3$). Unconditional. -/
@[kb "conwaysloane1999" "Ch. 15, §1, p. 353 and §7, p. 378 (one class when indefinite, n ≥ 3, |det| < 128)"]
theorem oneClass_of_natAbs_lt (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hind : IsIndefinite (csQ A)) (hlt : A.det.natAbs < 128) : ¬ MoreThanOneClass A := fun h => by
  have := corollary22_ge_three hn hA hd hind h
  have := d0_ge_128 hn
  omega

/-- **Table 15.4 (indefinite cases)** (Conway–Sloane, §8.1, p. 386: "for indefinite cases of dimension $\ge 3$ these
are also the integral equivalence classes"): an indefinite form of dimension $n \ge 3$ with $\lvert\det A\rvert \le 11$
has one class in its genus. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, p. 386 (Table 15.4: one class when indefinite, n ≥ 3)"]
theorem oneClass_of_natAbs_le_eleven (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (hind : IsIndefinite (csQ A)) (hle : A.det.natAbs ≤ 11) : ¬ MoreThanOneClass A :=
  oneClass_of_natAbs_lt hn hA hd hind (by omega)

/-! ### $p$-elementary forms -/

/-- **$p$-elementary lattices** (Conway–Sloane, §8.2, p. 386: "forms for which $L^*/L$ is a nontrivial elementary
abelian $p$-group"). For the lattice $L = \mathbb Z^n$ with Gram matrix $A$ (nondegenerate), $L^* = A^{-1}\mathbb Z^n$
in coordinates, and $L^*/L$ is elementary abelian $p$-group iff $pL^* \subseteq L$ iff $pA^{-1}$ has integer entries,
i.e. $AB = pI$ for an integer matrix $B$; it is nontrivial iff $L^* \ne L$ iff $A$ is not unimodular
($\lvert\det A\rvert \ne 1$). Here $p$ is a natural number; the results below take it prime. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, p. 386 (p-elementary)"]
def IsPElementary (A : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) : Prop :=
  (∃ B : Matrix (Fin n) (Fin n) ℤ, A * B = (p : ℤ) • 1) ∧ A.det.natAbs ≠ 1

/-! ### Local lemmas -/

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ

/-- A matrix over $\mathbb Q_v$ has entries of absolute value $\le 1$. -/
def IntM (M : Matrix (Fin n) (Fin n) Fv) : Prop := ∀ i j, Valued.v (M i j) ≤ 1

variable {v}

theorem IntM.mul {M N : Matrix (Fin n) (Fin n) Fv} (hM : IntM v M) (hN : IntM v N) : IntM v (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by
    rw [map_mul]; exact mul_le_one' (hM i k) (hN k j)

theorem IntM.transpose {M : Matrix (Fin n) (Fin n) Fv} (hM : IntM v M) : IntM v Mᵀ :=
  fun i j => hM j i

theorem intM_map_intCast (B : Matrix (Fin n) (Fin n) ℤ) :
    IntM v (B.map (Int.cast : ℤ → Fv)) := fun i j => valued_intCast_le_one' v (B i j)

/-- Core estimate: $\lvert p\rvert \le \lvert a_k\rvert \le 1$ for the diagonal entries $a_k$ of a diagonal
$g^{\mathsf T}Ag$, $g \in \mathrm{GL}_n(\mathbb Z_v)$, when $AB = pI$ with $B$ integral. -/
theorem diag_bounds (g gi : Matrix (Fin n) (Fin n) Fv) (hg : IntM v g) (hgi : IntM v gi) (hgig : gi * g = 1)
    (hggi : g * gi = 1) (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℤ) (hAB : A * B = p • 1)
    (hdiag : ∀ k l, k ≠ l → (gᵀ * A.map (Int.cast : ℤ → Fv) * g) k l = 0) (k : Fin n) :
    Valued.v ((p : ℤ) : Fv) ≤ Valued.v ((gᵀ * A.map (Int.cast : ℤ → Fv) * g) k k) ∧
      Valued.v ((gᵀ * A.map (Int.cast : ℤ → Fv) * g) k k) ≤ 1 := by
  set Am : Matrix (Fin n) (Fin n) Fv := A.map (Int.cast : ℤ → Fv) with hAm
  set Bm : Matrix (Fin n) (Fin n) Fv := B.map (Int.cast : ℤ → Fv) with hBm
  have hAmBm : Am * Bm = (p : Fv) • 1 := by
    ext i j
    have h := congrFun (congrFun hAB i) j
    rw [Matrix.mul_apply] at h
    have h2 := congrArg (Int.cast : ℤ → Fv) h
    push_cast at h2
    simp only [hAm, hBm, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply] at h2 ⊢
    rw [h2]
    split_ifs <;> simp
  have hAmI : IntM v Am := intM_map_intCast A
  have hBmI : IntM v Bm := intM_map_intCast B
  have hA' : IntM v (gᵀ * Am * g) := (hg.transpose.mul hAmI).mul hg
  set C : Matrix (Fin n) (Fin n) Fv := gi * Bm * giᵀ with hC
  have hCI : IntM v C := (hgi.mul hBmI).mul hgi.transpose
  have hprod : (gᵀ * Am * g) * C = (p : Fv) • 1 := by
    have e1 : (gᵀ * Am * g) * C = gᵀ * (Am * (g * gi) * Bm) * giᵀ := by
      simp only [hC, Matrix.mul_assoc]
    rw [e1, hggi, Matrix.mul_one, hAmBm, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Matrix.transpose_mul, hgig, Matrix.transpose_one]
  have hkk : (p : Fv) = (gᵀ * Am * g) k k * C k k := by
    have h := congrFun (congrFun hprod k) k
    rw [Matrix.mul_apply, Finset.sum_eq_single k] at h
    · simpa using h.symm
    · intro l _ hl
      rw [hdiag k l hl.symm, zero_mul]
    · simp
  refine ⟨?_, hA' k k⟩
  rw [hkk, map_mul]
  exact mul_le_of_le_one_right' (hCI k k)

end Local

theorem two_vals {x : WithZero (Multiplicative ℤ)} (h1 : exp (-2) < x) (h2 : x ≤ 1) :
    x = exp 0 ∨ x = exp (-1) := by
  have hx : x ≠ 0 := ((zero_le :(0 : WithZero (Multiplicative ℤ)) ≤ exp (-2)).trans_lt h1).ne'
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = exp k := ⟨log x, (exp_log hx).symm⟩
  rw [exp_lt_exp] at h1
  rw [← exp_zero, exp_le_exp] at h2
  rcases (by omega : k = 0 ∨ k = -1) with rfl | rfl
  · left; rfl
  · right; rfl

/-- **$p$-elementary indefinite forms of dimension $\ge 3$ have one class in their genus** (Conway–Sloane, §8.2,
Thm. 13 (a), (b), pp. 386–388: "one class when indefinite, dimension $\ge 3$"; the $p$-elementary genera of Thm. 13
(a) and (b) are those of $L^*/L$ an elementary abelian $p$-group). Unconditional (uses Thm. 19, §9.7). *Proof:* see the
module docstring. -/
@[kb "conwaysloane1999" "Ch. 15, §8.2, Thm. 13 (a), (b), pp. 386–388 (one class when indefinite, n ≥ 3)"]
theorem oneClass_of_isPElementary (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : Aᵀ = A) (hd : A.det ≠ 0) (hind : IsIndefinite (csQ A)) (hpe : IsPElementary A p) :
    ¬ MoreThanOneClass A := fun h => by
  obtain ⟨⟨B, hAB⟩, -⟩ := hpe
  obtain ⟨v, γ, hγ, horth, hinj⟩ := theorem19 hn hA hd hind h
  have hstd : locAct v γ (std v) = std v := by
    rw [← hγ, loc_std_eq_locAct_one v, locAct_one]
  have hstd' : std v = locAct v γ⁻¹ (std v) := locAct_eq_iff.mp hstd
  have hg : IntM v γ.val := by
    intro i j
    have hm : γ.val *ᵥ Pi.single j 1 ∈ std v := by
      rw [← hstd, mem_locAct]; exact ⟨_, single_mem_std j (by simp), rfl⟩
    have := mem_std_iff.mp hm i
    simpa [Matrix.mulVec_single_one] using this
  have hgi : IntM v (γ⁻¹).val := by
    intro i j
    have hm : (γ⁻¹).val *ᵥ Pi.single j 1 ∈ std v := by
      rw [hstd', mem_locAct]; exact ⟨_, single_mem_std j (by simp), rfl⟩
    have := mem_std_iff.mp hm i
    simpa [Matrix.mulVec_single_one] using this
  have hgig : (γ⁻¹).val * γ.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hggi : γ.val * (γ⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set Am : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ) := A.map (Int.cast : ℤ → v.adicCompletion ℚ) with hAm
  have hG1 : locGram (csQ A) v 1 = (2 : v.adicCompletion ℚ) • Am := by
    ext k l
    rw [locGram_one_int, hessian_csForm hA]
    simp [hAm]
  have hG : locGram (csQ A) v γ = (2 : v.adicCompletion ℚ) • (γ.valᵀ * Am * γ.val) := by
    have := locGram_mul (Q := csQ A) (v := v) 1 γ
    rw [one_mul] at this
    rw [this, hG1, Matrix.mul_smul, Matrix.smul_mul]
  have hdiag : ∀ k l, k ≠ l → (γ.valᵀ * Am * γ.val) k l = 0 := by
    intro k l hkl
    have := horth k l hkl
    rw [hG] at this
    simpa using this
  have hbd := fun k => diag_bounds γ.val (γ⁻¹).val hg hgi hgig hggi A B (p : ℤ) hAB hdiag k
  -- the absolute value of p exceeds exp(-2)
  have hp2 : exp (-2) < Valued.v (((p : ℤ) : v.adicCompletion ℚ)) := by
    by_contra hle
    push Not at hle
    have h2 := (valued_intCast_le_iff v (p : ℤ) 2).mp (by simpa using hle)
    have h3 : (Rat.HeightOneSpectrum.natGenerator v) ^ 2 ∣ p := by exact_mod_cast h2
    have h4 := Rat.HeightOneSpectrum.prime_natGenerator v
    have h5 : Rat.HeightOneSpectrum.natGenerator v ∣ p := dvd_trans (dvd_pow_self _ two_ne_zero) h3
    have h6 := (Nat.prime_dvd_prime_iff_eq h4 hp).mp h5
    rw [h6] at h3
    have := Nat.le_of_dvd hp.pos h3
    have := hp.two_le
    nlinarith
  have hvals : ∀ k, Valued.v ((γ.valᵀ * Am * γ.val) k k) = exp 0 ∨
      Valued.v ((γ.valᵀ * Am * γ.val) k k) = exp (-1) := fun k =>
    two_vals (lt_of_lt_of_le hp2 (hbd k).1) (hbd k).2
  have hinj' : ∀ i j, Valued.v ((γ.valᵀ * Am * γ.val) i i) = Valued.v ((γ.valᵀ * Am * γ.val) j j) → i = j := by
    intro i j hij
    apply hinj
    show Valued.v (locGram (csQ A) v γ i i) = Valued.v (locGram (csQ A) v γ j j)
    rw [hG]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hij]
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := fun e => by have := congrArg Fin.val e; simp [i0, i1] at this
  have h02 : i0 ≠ i2 := fun e => by have := congrArg Fin.val e; simp [i0, i2] at this
  have h12 : i1 ≠ i2 := fun e => by have := congrArg Fin.val e; simp [i1, i2] at this
  have n01 := fun e => h01 (hinj' _ _ e)
  have n02 := fun e => h02 (hinj' _ _ e)
  have n12 := fun e => h12 (hinj' _ _ e)
  rcases hvals i0 with a | a <;> rcases hvals i1 with b | b <;> rcases hvals i2 with c | c
  all_goals first
    | exact n01 (a.trans b.symm)
    | exact n02 (a.trans c.symm)
    | exact n12 (b.trans c.symm)

end QuadFormsKB.ConwaySloane
