/-
# Conway–Sloane, Ch. 15, §8.1: forms of determinant $\pm1$ and $\pm3$, at the level of symbols

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §8.1,
pp. 385–386 (`conwaysloane1999`; printed page = PDF page of the chapter file + 351).

The statements are about `GenusSymbolData` (the putative systems of local symbols of `Existence.lean`) satisfying
`GenusSymbolData.Conditions` ((29)–(35) of §7.7): "a genus with this signature, determinant and type exists" means
"there is a system of symbols satisfying the conditions of §7.7". Passing from symbols to forms is Thm. 11
(not part of this file).

**Determinant $\pm1$ (§8.1, "Determinant $\pm1$", p. 385; row §8.1.r2).**
* `smallDet_one_typeI`: a genus $\mathrm I_{r,s}$ (2-adic symbol $1_t^{+(r+s)}$, type I) exists iff $(r,s) \ne (0,0)$;
* `smallDet_one_typeII`: a genus $\mathrm{II}_{r,s}$ (type II) exists iff $r - s \equiv 0 \pmod 8$.
The necessity part shows that the 2-adic symbol of a system with $\lvert\det\rvert = 1$ is $1_t^{+(r+s)}$ with $t \equiv r - s$.

**Determinant $\pm3$ (§8.1, "Determinant $\pm3$", pp. 385–386; row §8.1.r3).** The four genera
$\mathrm I_{r,s}(3^{\pm1})$, $\mathrm{II}_{r,s}(3^{\pm1})$: $e = \pm$ is the sign of the constituent $3^{e1}$, and the 2-adic
symbol is $1_t^{-(r+s)}$ (type I) or $1^{-(r+s)}$ (type II), with the oddity conditions
$r - s + 2 \equiv t$ ($e = +$), $r - s + 6 \equiv t$ ($e = -$) (type I), and $r - s + 2 \equiv 0$, $r - s + 6 \equiv 0$ (type II).
* `smallDet_three_typeI`, `smallDet_three_typeII`: iff statements (existence of a system of symbols with these data
  $\Leftrightarrow$ the oddity condition together with the existence conditions on the 2-adic constituent and
  (31) on the 3-adic one);
* `smallDet_three_typeI_explicit`, `smallDet_three_small_cases`: for $\mathrm I_{r,s}(3^{e})$ the genus exists except exactly for the
  *failures* of the book: $(r,s) \in \{(0,0), (0,1), (0,2)\}$ for $e = +$ ("$0, 1_-, 2_-$" in the book's notation
  $n_\sigma$, $\sigma = r - s$) and $\{(0,0), (1,0), (2,0)\}$ for $e = -$ (the book's Table 15.4: "$0, 1_{\mp1}, 2_{\mp2}$").

**Deviations.** The ambiguous sign "$\pm$" of the book's 3-adic symbols $1^{\pm(r+s-1)}3^{1}$ is not an input here: it
is forced by (29) (`det3Data`). The oddity cast $r - s \in \mathbb Z/8$ is taken in `ZMod 8`.
-/
import QuadFormsKB.Literature.ConwaySloane.Existence

namespace QuadFormsKB.ConwaySloane

open Finset

/-! ### Helper lemmas on signs and sums -/

theorem Sign.mul_plus (x : Sign) : x.mul .plus = x := by cases x <;> rfl

theorem Sign.mul_self_eq (x : Sign) : x.mul x = .plus := by cases x <;> rfl

theorem Sign.mul_mul_self (x e : Sign) : (x.mul e).mul e = x := by cases x <;> cases e <;> rfl

/-- The product of signs stabilizes once all later signs are $+$. -/
theorem signProd_stable (s : ℕ → Sign) {a b : ℕ} (hab : a ≤ b) (h : ∀ k, a ≤ k → s k = .plus) :
    signProd s b = signProd s a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hb ih => rw [signProd, ih, h b hb, Sign.mul_plus]

/-- Sums over $\{k < N\}$ and $\{k < m\}$ agree when the summand vanishes from $m$ on and from $N$ on. -/
theorem sum_range_stable {f : ℕ → ZMod 8} {m N : ℕ} (hm : ∀ k, m ≤ k → f k = 0) (hN : ∀ k, N ≤ k → f k = 0) :
    ∑ k ∈ range N, f k = ∑ k ∈ range m, f k := by
  rcases le_total m N with h | h
  · refine (Finset.sum_subset (range_subset_range.2 h) fun k hk hk' => ?_).symm
    exact hm k (by simpa using hk')
  · refine Finset.sum_subset (range_subset_range.2 h) fun k hk hk' => ?_
    exact hN k (by simpa using hk')

theorem sum_range_stable_nat {f : ℕ → ℕ} {m N : ℕ} (hm : ∀ k, m ≤ k → f k = 0) (hN : ∀ k, N ≤ k → f k = 0) :
    ∑ k ∈ range N, f k = ∑ k ∈ range m, f k := by
  rcases le_total m N with h | h
  · refine (Finset.sum_subset (range_subset_range.2 h) fun k hk hk' => ?_).symm
    exact hm k (by simpa using hk')
  · refine Finset.sum_subset (range_subset_range.2 h) fun k hk hk' => ?_
    exact hN k (by simpa using hk')

theorem padicValInt_negOnePow (p s : ℕ) : padicValInt p ((-1 : ℤ) ^ s) = 0 := by
  simp [padicValInt, Int.natAbs_pow]

theorem jacobiTwo_pm_one (s : ℕ) : jacobiTwo ((-1 : ℤ) ^ s) = .plus := by
  rcases Nat.even_or_odd s with h | h <;> simp [h.neg_one_pow, jacobiTwo]

theorem jacobiTwo_pm_three (s : ℕ) : jacobiTwo (3 * (-1 : ℤ) ^ s) = .minus := by
  rcases Nat.even_or_odd s with h | h <;> simp [h.neg_one_pow, jacobiTwo]

theorem ofInt_jacobi_three (s : ℕ) :
    Sign.ofInt (jacobiSym ((-1 : ℤ) ^ s) 3) = if Even s then .plus else .minus := by
  rcases Nat.even_or_odd s with h | h
  · simp [h.neg_one_pow, h, Sign.ofInt]
  · have h' : ¬ Even s := Nat.not_even_iff_odd.2 h
    have : jacobiSym (-1) 3 = -1 := by
      rw [jacobiSym.at_neg_one (by decide)]
      exact ZMod.χ₄_nat_three_mod_four (by norm_num)
    simp [h.neg_one_pow, h', this, Sign.ofInt]

/-! ### The 2-adic part of a system of symbols with odd determinant -/

/-- **The 2-adic symbol of a system with odd determinant** has only the scale $1$: $1_t^{\varepsilon n}$ with
$\varepsilon = \left(\frac{d}{2}\right)$ (Conway–Sloane, §8.1, pp. 385–386: "the possible 2-adic symbols"). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, p. 385 (2-adic symbols for odd determinant)"]
theorem GenusSymbolData.two_part (G : GenusSymbolData) (hc : G.Conditions) (hv : padicValInt 2 G.det = 0) :
    (∀ k, 0 < k → G.two k = TwoFactor.trivial) ∧ (G.two 0).dim = G.n ∧ (G.two 0).sign = jacobiTwo G.det ∧
      G.two.oddity G.N = (G.two 0).oddity ∧ (G.two 0).Exists := by
  have hdim : ∀ k, 0 < k → (G.two k).dim = 0 := by
    intro k hk
    by_cases hkN : k < G.N
    · have h := hc.two_det.1
      rw [hv] at h
      have := (Finset.sum_eq_zero_iff.1 h) k (mem_range.2 hkN)
      simpa [hk.ne'] using this
    · rw [hc.two_supp k (not_lt.1 hkN)]; rfl
  have htriv : ∀ k, 0 < k → G.two k = TwoFactor.trivial := by
    intro k hk
    obtain ⟨h32, -, -, -, hII⟩ := hc.two_exists k
    have h1 : (G.two k).dim = 0 := hdim k hk
    obtain ⟨h2, h3⟩ := h32 h1
    have h4 : (G.two k).oddity = 0 := hII h2
    generalize G.two k = f at h1 h2 h3 h4
    obtain ⟨d, s, t, o⟩ := f
    dsimp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  have hzero : G.N ≤ 0 → G.two 0 = TwoFactor.trivial := fun h => hc.two_supp 0 h
  refine ⟨htriv, ?_, ?_, ?_, hc.two_exists 0⟩
  · rw [← hc.two_dim]
    symm
    refine Finset.sum_eq_single 0 (fun k _ hk => hdim k (Nat.pos_of_ne_zero hk)) fun h0 => ?_
    have : G.N ≤ 0 := by simpa using h0
    rw [hzero this]; rfl
  · have h := hc.two_det.2
    rw [hv, pow_zero, Int.ediv_one] at h
    rw [← h]
    have hs : ∀ k, 1 ≤ k → (fun k => (G.two k).sign) k = .plus := fun k hk => by
      simp [htriv k hk, TwoFactor.trivial]
    rcases Nat.eq_zero_or_pos G.N with hN | hN
    · rw [hN]
      have := hc.two_supp 0 (by omega)
      simp [signProd, this, TwoFactor.trivial]
    · rw [signProd_stable (fun k => (G.two k).sign) hN hs]
      simp only [signProd]
      cases (G.two 0).sign <;> rfl
  · unfold TwoSymbol.oddity
    rw [Finset.sum_eq_single 0]
    · simp [ind8]
    · intro k _ hk
      simp [htriv k (Nat.pos_of_ne_zero hk), TwoFactor.trivial, ind8]
    · intro h0
      have : G.N ≤ 0 := by simpa using h0
      simp [hzero this, TwoFactor.trivial, ind8]

/-! ### Determinant $\pm1$ -/

theorem val_sub_mod_two (r s : ℕ) : ((r : ZMod 8) - s).val % 2 = (r + s) % 2 := by
  have e : ((r : ZMod 8) - s) = (((r : ℤ) - s : ℤ) : ZMod 8) := by push_cast; rfl
  rw [e]
  have h := ZMod.val_intCast (n := 8) ((r : ℤ) - s)
  omega

theorem sub_eq_zero_iff_mod (r s : ℕ) : ((r : ZMod 8) - s = 0) ↔ ((r : ℤ) - s) % 8 = 0 := by
  have := ZMod.intCast_zmod_eq_zero_iff_dvd ((r : ℤ) - s) 8
  push_cast at this
  rw [this]
  omega

/-- **The system of symbols of $\mathrm I_{r,s}$ / $\mathrm{II}_{r,s}$** (Conway–Sloane, §8.1, p. 385): determinant
$(-1)^s$, $(-1)$-adic symbol $+^r-^s$, the $p$-adic symbol $1^{\varepsilon(r+s)}$ ($\varepsilon = \left(\frac{-1}{p}\right)^s$)
at every odd $p$, and the 2-adic symbol $1^{+(r+s)}$ of type `T` and oddity `t`. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, p. 385"]
def det1Data (r s : ℕ) (T : ScaledType) (t : ZMod 8) : GenusSymbolData where
  n := r + s
  det := (-1) ^ s
  real := ⟨r, s⟩
  odd := fun p k => if k = 0 then ⟨r + s, Sign.ofInt (jacobiSym ((-1) ^ s) p)⟩ else OddFactor.trivial
  two := fun k => if k = 0 then ⟨r + s, .plus, T, t⟩ else TwoFactor.trivial
  N := 1

theorem det1Data_conditions (r s : ℕ) (T : ScaledType) (t : ZMod 8)
    (hE : (⟨r + s, .plus, T, t⟩ : TwoFactor).Exists) (ht : (r : ZMod 8) - s = t) :
    (det1Data r s T t).Conditions where
  ne_zero := pow_ne_zero _ (by norm_num)
  real_dim := rfl
  real_sign := by
    rcases Nat.even_or_odd s with h | h <;> simp [det1Data, h.neg_one_pow, h, Nat.not_even_iff_odd]
  odd_supp p k hk := by
    have hk' : 1 ≤ k := hk
    simp [det1Data, show k ≠ 0 by omega]
  two_supp k hk := by
    have hk' : 1 ≤ k := hk
    simp [det1Data, show k ≠ 0 by omega]
  odd_dim p _ _ := by simp [det1Data]
  two_dim := by simp [det1Data]
  odd_det p _ _ := by
    refine ⟨?_, ?_⟩
    · simp [det1Data, padicValInt_negOnePow]
    · simp [det1Data, padicValInt_negOnePow, signProd, Sign.mul]
  two_det := by
    refine ⟨by simp [det1Data, padicValInt_negOnePow], ?_⟩
    simp [det1Data, padicValInt_negOnePow, signProd, Sign.mul, jacobiTwo_pm_one]
  odd_exists p _ _ k := by
    by_cases hk : k = 0
    · subst hk
      simp only [det1Data, if_true]
      intro h0
      have h0' : r + s = 0 := h0
      have hr : r = 0 := by omega
      have hs : s = 0 := by omega
      subst hr hs
      simp [Sign.ofInt]
    · simp only [det1Data, if_neg hk]
      exact fun _ => rfl
  two_exists k := by
    by_cases hk : k = 0
    · subst hk; simpa [det1Data] using hE
    · simp only [det1Data, if_neg hk]
      decide
  oddity_formula := by
    simp [det1Data, GenusSymbolData.signature, TwoSymbol.oddity, ind8, Int.natAbs_pow, ht]

/-- **The oddity condition for determinant $\pm1$**: $r - s \equiv t \pmod 8$ for the 2-adic constituent
$1_t^{+(r+s)}$ (Conway–Sloane, §8.1, p. 385). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, p. 385"]
theorem GenusSymbolData.det1_oddity (G : GenusSymbolData) (hc : G.Conditions) (hd : G.det.natAbs = 1) :
    (G.signature : ZMod 8) = (G.two 0).oddity := by
  have hv : padicValInt 2 G.det = 0 := by simp [padicValInt, hd]
  have h := hc.oddity_formula
  rw [hd] at h
  simp at h
  rw [h]
  exact (G.two_part hc hv).2.2.2.1

theorem typeI_exists (r s : ℕ) (h : r + s ≠ 0) :
    (⟨r + s, .plus, .I, (r : ZMod 8) - s⟩ : TwoFactor).Exists := by
  refine ⟨fun h0 => absurd h0 h, fun h1 => ?_, fun h2 _ => ?_, ?_, fun h => nomatch h⟩
  · have h1' : r + s = 1 := h1
    rcases (by omega : (r = 1 ∧ s = 0) ∨ (r = 0 ∧ s = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · have h2' : r + s = 2 := h2
    rcases (by omega : (r = 2 ∧ s = 0) ∨ (r = 1 ∧ s = 1) ∨ (r = 0 ∧ s = 2)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · exact val_sub_mod_two r s

theorem typeII_exists (r s : ℕ) (h : (r : ZMod 8) - s = 0) :
    (⟨r + s, .plus, .II, 0⟩ : TwoFactor).Exists := by
  have hp : (r + s) % 2 = 0 := by
    have := val_sub_mod_two r s
    rw [h] at this
    simp at this
    omega
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun h1 => ?_, (fun _ hI => by cases hI), ?_, fun _ => rfl⟩
  · have h1' : r + s = 1 := h1
    exfalso
    omega
  · show (0 : ZMod 8).val % 2 = (r + s) % 2
    simp
    omega

/-- **Determinant $\pm1$, genus $\mathrm I_{r,s}$** (Conway–Sloane, §8.1, "Determinant $\pm1$", p. 385; §8.1.r2): a
system of symbols satisfying (29)–(35) with $\lvert\det\rvert = 1$, $(-1)$-adic symbol $+^r-^s$ and 2-adic constituent
of type I exists iff $(r,s) \ne (0,0)$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, p. 385 (I_{r,s} exists unless r = s = 0)"]
theorem smallDet_one_typeI (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 1 ∧ (G.two 0).type = .I) ↔
      (r ≠ 0 ∨ s ≠ 0) := by
  constructor
  · rintro ⟨G, hc, hr, hd, hT⟩
    have hv : padicValInt 2 G.det = 0 := by simp [padicValInt, hd]
    obtain ⟨-, hdim, -, -, hE⟩ := G.two_part hc hv
    have hn : G.n = r + s := by rw [← hc.real_dim, hr]
    by_contra hcon
    push Not at hcon
    have h0 : (G.two 0).dim = 0 := by rw [hdim, hn]; omega
    have := (hE.1 h0).1
    rw [hT] at this
    exact absurd this (by decide)
  · intro h
    have hne : r + s ≠ 0 := by omega
    exact ⟨det1Data r s .I ((r : ZMod 8) - s), det1Data_conditions r s .I _ (typeI_exists r s hne) rfl,
      rfl, by simp [det1Data], by simp [det1Data]⟩

/-- **Determinant $\pm1$, genus $\mathrm{II}_{r,s}$** (Conway–Sloane, §8.1, p. 385; §8.1.r2): the same with 2-adic
constituent of type II exists iff $r - s \equiv 0 \pmod 8$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, p. 385 (II_{r,s} exists iff r ≡ s mod 8)"]
theorem smallDet_one_typeII (r s : ℕ) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 1 ∧ (G.two 0).type = .II) ↔
      ((r : ℤ) - s) % 8 = 0 := by
  rw [← sub_eq_zero_iff_mod]
  constructor
  · rintro ⟨G, hc, hr, hd, hT⟩
    have hv : padicValInt 2 G.det = 0 := by simp [padicValInt, hd]
    obtain ⟨-, -, -, -, hE⟩ := G.two_part hc hv
    have h := G.det1_oddity hc hd
    rw [hE.2.2.2.2 hT] at h
    simpa [GenusSymbolData.signature, hr] using h
  · intro h
    exact ⟨det1Data r s .II 0, det1Data_conditions r s .II 0 (typeII_exists r s h) h, rfl, by simp [det1Data],
      by simp [det1Data]⟩

/-! ### Determinant $\pm3$ -/

theorem Sign.plus_mul (x : Sign) : Sign.plus.mul x = x := rfl

theorem padicValInt_three_negOnePow (s : ℕ) : padicValInt 3 (3 * (-1 : ℤ) ^ s) = 1 := by
  simp [padicValInt, Int.natAbs_mul, Int.natAbs_pow]

theorem padicValInt_three_negOnePow_of_ne (p s : ℕ) (hp : p.Prime) (h3 : p ≠ 3) :
    padicValInt p (3 * (-1 : ℤ) ^ s) = 0 := by
  have : ¬ p ∣ 3 := fun h => h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  simp [padicValInt, Int.natAbs_mul, Int.natAbs_pow, padicValNat.eq_zero_of_not_dvd this]

theorem padicValInt_two_three (s : ℕ) : padicValInt 2 (3 * (-1 : ℤ) ^ s) = 0 := by
  have : ¬ 2 ∣ 3 := by norm_num
  simp [padicValInt, Int.natAbs_mul, Int.natAbs_pow, padicValNat.eq_zero_of_not_dvd this]

/-- **The system of symbols of $\mathrm I_{r,s}(3^{\pm1})$ / $\mathrm{II}_{r,s}(3^{\pm1})$** (Conway–Sloane, §8.1,
p. 385): determinant $3(-1)^s$, $(-1)$-adic symbol $+^r-^s$, the 3-adic symbol $1^{\varepsilon(r+s-1)}3^{e1}$ with
$\varepsilon$ forced by (29), the symbols $1^{\varepsilon(r+s)}$ at the other odd primes, and the 2-adic symbol
$1^{-(r+s)}$ of type `T` and oddity `t`. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, p. 385"]
def det3Data (r s : ℕ) (e : Sign) (T : ScaledType) (t : ZMod 8) : GenusSymbolData where
  n := r + s
  det := 3 * (-1) ^ s
  real := ⟨r, s⟩
  odd := fun p k =>
    if p = 3 then
      (if k = 0 then ⟨r + s - 1, (Sign.ofInt (jacobiSym ((-1) ^ s) 3)).mul e⟩
       else if k = 1 then ⟨1, e⟩ else OddFactor.trivial)
    else (if k = 0 then ⟨r + s, Sign.ofInt (jacobiSym (3 * (-1) ^ s) p)⟩ else OddFactor.trivial)
  two := fun k => if k = 0 then ⟨r + s, .minus, T, t⟩ else TwoFactor.trivial
  N := 2

theorem det3Data_conditions (r s : ℕ) (e : Sign) (T : ScaledType) (t : ZMod 8) (hn : 1 ≤ r + s)
    (hcompat : r + s = 1 → e = Sign.ofInt (jacobiSym ((-1) ^ s) 3))
    (hE : (⟨r + s, .minus, T, t⟩ : TwoFactor).Exists)
    (ht : (r : ZMod 8) - s + (if e = .minus then 6 else 2) = t) :
    (det3Data r s e T t).Conditions where
  ne_zero := mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  real_dim := rfl
  real_sign := by
    rcases Nat.even_or_odd s with h | h
    · have : ¬ Odd s := Nat.not_odd_iff_even.2 h
      simp [det3Data, h.neg_one_pow, this]
    · simp [det3Data, h.neg_one_pow, h]
  odd_supp p k hk := by
    have hk' : 2 ≤ k := hk
    by_cases hp : p = 3
    · simp [det3Data, hp, show k ≠ 0 by omega, show k ≠ 1 by omega]
    · simp [det3Data, hp, show k ≠ 0 by omega]
  two_supp k hk := by
    have hk' : 2 ≤ k := hk
    simp [det3Data, show k ≠ 0 by omega]
  odd_dim p _ _ := by
    by_cases hp : p = 3
    · simp [det3Data, hp, Finset.sum_range_succ]
      omega
    · simp [det3Data, hp, Finset.sum_range_succ, OddFactor.trivial]
  two_dim := by simp [det3Data, Finset.sum_range_succ, TwoFactor.trivial]
  odd_det p hp hp2 := by
    by_cases h3 : p = 3
    · subst h3
      refine ⟨?_, ?_⟩
      · simp [det3Data, padicValInt_three_negOnePow, Finset.sum_range_succ]
      · have hd : (3 * (-1 : ℤ) ^ s) / ((3 : ℕ) : ℤ) ^ 1 = (-1) ^ s := by simp
        simp [det3Data, padicValInt_three_negOnePow, signProd, hd, Sign.plus_mul, Sign.mul_mul_self]
    · refine ⟨?_, ?_⟩
      · simp [det3Data, h3, padicValInt_three_negOnePow_of_ne p s hp h3, Finset.sum_range_succ,
          OddFactor.trivial]
      · simp [det3Data, h3, padicValInt_three_negOnePow_of_ne p s hp h3, signProd, Sign.plus_mul,
          Sign.mul_plus, OddFactor.trivial]
  two_det := by
    refine ⟨by simp [det3Data, padicValInt_two_three, Finset.sum_range_succ, TwoFactor.trivial], ?_⟩
    simp [det3Data, padicValInt_two_three, signProd, jacobiTwo_pm_three, Sign.mul, TwoFactor.trivial,
      Sign.flip]
  odd_exists p hp hp2 k := by
    by_cases h3 : p = 3
    · subst h3
      by_cases hk0 : k = 0
      · subst hk0
        simp only [det3Data, if_true]
        intro h0
        have h0' : r + s - 1 = 0 := h0
        rw [hcompat (by omega)]
        exact Sign.mul_self_eq _
      · by_cases hk1 : k = 1
        · subst hk1
          simp [det3Data, OddFactor.Exists]
        · simp [det3Data, hk0, hk1, OddFactor.Exists, OddFactor.trivial]
    · by_cases hk0 : k = 0
      · subst hk0
        simp only [det3Data, h3, if_true, if_false]
        intro h0
        have h0' : r + s = 0 := h0
        omega
      · simp [det3Data, h3, hk0, OddFactor.Exists, OddFactor.trivial]
  two_exists k := by
    by_cases hk : k = 0
    · subst hk; simpa [det3Data] using hE
    · simp only [det3Data, if_neg hk]
      decide
  oddity_formula := by
    have hna : (det3Data r s e T t).det.natAbs = 3 := by
      simp [det3Data, Int.natAbs_mul, Int.natAbs_pow]
    rw [hna, Nat.Prime.primeFactors Nat.prime_three, Finset.filter_singleton, if_pos (by norm_num),
      Finset.sum_singleton]
    simp [det3Data, GenusSymbolData.signature, OddSymbol.pExcess, TwoSymbol.oddity, ind8,
      Finset.sum_range_succ, TwoFactor.trivial, OddFactor.trivial]
    cases e
    · simp at ht ⊢
      linear_combination ht
    · simp at ht ⊢
      linear_combination ht

/-- **The data forced by the conditions when $\lvert\det\rvert = 3$** (Conway–Sloane, §8.1, pp. 385–386): $n \ge 1$; the
3-adic symbol is $1^{\pm(n-1)}3^{e1}$; the 2-adic symbol is $1_t^{-n}$ (sign $-$ since $\det \equiv \pm3 \pmod 8$) with
$t \equiv r - s + 2$ ($e = +$) or $r - s + 6$ ($e = -$): the 3-excess is $2 + 4[e = -]$; and for $n = 1$ the
constituent $1^{\pm 0}$ must have sign $+$ (31), which fixes $e$. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, pp. 385–386 (determinant ±3)"]
theorem GenusSymbolData.three_part (G : GenusSymbolData) (hc : G.Conditions) (hd : G.det.natAbs = 3) :
    1 ≤ G.n ∧ (G.two 0).dim = G.n ∧ (G.two 0).sign = .minus ∧ (G.two 0).Exists ∧
    (G.signature : ZMod 8) + (if (G.odd 3 1).sign = .minus then 6 else 2) = (G.two 0).oddity ∧
    (G.n = 1 → (G.odd 3 1).sign = Sign.ofInt (jacobiSym (G.det / 3) 3)) := by
  have hv2 : padicValInt 2 G.det = 0 := by
    have : ¬ 2 ∣ 3 := by norm_num
    simp [padicValInt, hd, padicValNat.eq_zero_of_not_dvd this]
  have hv3 : padicValInt 3 G.det = 1 := by simp [padicValInt, hd]
  obtain ⟨-, hdim2, hsign2, hoddeq, hE2⟩ := G.two_part hc hv2
  have hdet : G.det = 3 ∨ G.det = -3 := by omega
  have hsign : (G.two 0).sign = .minus := by
    rw [hsign2]; rcases hdet with h | h <;> rw [h] <;> decide
  have p3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hs3, hsg3⟩ := hc.odd_det 3 p3 (by norm_num)
  rw [hv3] at hs3
  have hsupp := hc.odd_supp 3
  have hex := hc.odd_exists 3 p3 (by norm_num)
  have d2 : ∀ k, 2 ≤ k → (G.odd 3 k).dim = 0 := by
    intro k hk
    by_cases hkN : k < G.N
    · have hle : k * (G.odd 3 k).dim ≤ ∑ k ∈ range G.N, k * (G.odd 3 k).dim :=
        Finset.single_le_sum (f := fun k => k * (G.odd 3 k).dim) (fun i _ => Nat.zero_le _) (mem_range.2 hkN)
      rw [hs3] at hle
      by_contra hne
      have h1 : 1 ≤ (G.odd 3 k).dim := Nat.pos_of_ne_zero hne
      have := Nat.mul_le_mul hk h1
      omega
    · rw [hsupp k (not_lt.1 hkN)]; rfl
  have t3 : ∀ k, 2 ≤ k → G.odd 3 k = OddFactor.trivial := by
    intro k hk
    have h1 : (G.odd 3 k).dim = 0 := d2 k hk
    have h2 : (G.odd 3 k).sign = .plus := hex k h1
    generalize G.odd 3 k = f at h1 h2
    obtain ⟨d, s⟩ := f
    dsimp only at h1 h2
    subst h1 h2
    rfl
  have d1 : (G.odd 3 1).dim = 1 := by
    have h : ∑ k ∈ range G.N, k * (G.odd 3 k).dim = 1 * (G.odd 3 1).dim := by
      refine Finset.sum_eq_single 1 (fun k _ hk => ?_) (fun h1 => ?_)
      · rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · have : k = 0 := by omega
          simp [this]
        · simp [d2 k hk2]
      · have : G.N ≤ 1 := by simpa using h1
        rw [hsupp 1 this]; simp [OddFactor.trivial]
    rw [h] at hs3
    omega
  have hN2 : 2 ≤ G.N := by
    by_contra h
    have h' : G.N ≤ 1 := by omega
    have := hsupp 1 h'
    rw [this] at d1
    simp [OddFactor.trivial] at d1
  have hdimsum : (G.odd 3 0).dim + 1 = G.n := by
    have h := hc.odd_dim 3 p3 (by norm_num)
    rw [sum_range_stable_nat (f := fun k => (G.odd 3 k).dim) (m := 2) (fun k hk => d2 k hk)
      (fun k hk => by rw [hsupp k hk]; rfl)] at h
    simpa [Finset.sum_range_succ, d1] using h
  have hexc : (G.odd 3).pExcess 3 G.N = (if (G.odd 3 1).sign = .minus then 6 else 2) := by
    rw [OddSymbol.pExcess_congr 3 (σ := G.odd 3) (N := 2) t3 hN2]
    unfold OddSymbol.pExcess
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, d1]
    cases (G.odd 3 1).sign <;> simp [ind8] <;> decide
  refine ⟨by omega, hdim2, hsign, hE2, ?_, ?_⟩
  · have h := hc.oddity_formula
    rw [hd, Nat.Prime.primeFactors p3, Finset.filter_singleton, if_pos (by norm_num), Finset.sum_singleton,
      hexc] at h
    rw [h]
    exact hoddeq
  · intro hn1
    have h0 : (G.odd 3 0).dim = 0 := by omega
    have hs0 : (G.odd 3 0).sign = .plus := hex 0 h0
    rw [signProd_stable (fun k => (G.odd 3 k).sign) hN2
      (fun k hk => by simp [t3 k hk, OddFactor.trivial]), hv3] at hsg3
    simpa [signProd, hs0, Sign.plus_mul] using hsg3

/-- Helper: a symbol system with $\lvert\det\rvert = 3$ and $(-1)$-adic symbol $+^r-^s$ has the 2-adic constituent
$\langle r+s, -, T, (r - s) + \text{excess}\rangle$ at scale $1$. -/
theorem GenusSymbolData.three_two_zero (G : GenusSymbolData) (hc : G.Conditions) (hd : G.det.natAbs = 3)
    {r s : ℕ} (hr : G.real = ⟨r, s⟩) :
    1 ≤ r + s ∧ G.two 0 = ⟨r + s, .minus, (G.two 0).type,
        (r : ZMod 8) - s + (if (G.odd 3 1).sign = .minus then 6 else 2)⟩ ∧ (G.two 0).Exists ∧
      (r + s = 1 → (G.odd 3 1).sign = if Even s then .plus else .minus) := by
  obtain ⟨h1, hdim, hsign, hE, hodd, hcompat⟩ := G.three_part hc hd
  have hn : G.n = r + s := by rw [← hc.real_dim, hr]
  have hsig : (G.signature : ZMod 8) = (r : ZMod 8) - s := by
    simp [GenusSymbolData.signature, hr]
  refine ⟨by omega, ?_, hE, ?_⟩
  · rw [← hsig, hodd]
    generalize G.two 0 = f at hdim hsign
    obtain ⟨d, sg, t, o⟩ := f
    dsimp only at hdim hsign ⊢
    subst hsign
    rw [hdim, hn]
  · intro h1'
    rw [hcompat (by omega)]
    have h := hc.real_sign
    rw [hr] at h
    have h' : G.det < 0 ↔ Odd s := h
    rcases Nat.even_or_odd s with he | ho
    · have hnl : ¬ G.det < 0 := fun hl => (Nat.not_odd_iff_even.2 he) (h'.1 hl)
      have h3 : G.det = 3 := by omega
      have : G.det / 3 = (-1) ^ s := by rw [h3, he.neg_one_pow]; norm_num
      rw [this, ofInt_jacobi_three]
    · have hl : G.det < 0 := h'.2 ho
      have h3 : G.det = -3 := by omega
      have : G.det / 3 = (-1) ^ s := by rw [h3, ho.neg_one_pow]; norm_num
      rw [this, ofInt_jacobi_three]

theorem zmod_cast_iff (r s : ℕ) (c : ℤ) :
    ((r : ZMod 8) - s + (c : ZMod 8) = 0) ↔ ((r : ℤ) - s + c) % 8 = 0 := by
  have := ZMod.intCast_zmod_eq_zero_iff_dvd ((r : ℤ) - s + c) 8
  push_cast at this
  rw [this]
  omega

theorem excess_cast_iff (r s : ℕ) (e : Sign) :
    ((r : ZMod 8) - s + (if e = .minus then 6 else 2) = 0) ↔
      ((r : ℤ) - s + (if e = .minus then 6 else 2)) % 8 = 0 := by
  cases e
  · simpa using zmod_cast_iff r s 2
  · simpa using zmod_cast_iff r s 6

/-- **Determinant $\pm3$, genera $\mathrm I_{r,s}(3^{\pm1})$** (Conway–Sloane, §8.1, pp. 385–386; §8.1.r3). A system of
symbols satisfying (29)–(35), with $\lvert\det\rvert = 3$, $(-1)$-adic symbol $+^r-^s$, 2-adic constituent of type I and
the 3-adic constituent $3^{e1}$ exists iff $n = r + s \ge 1$, the 2-adic constituent
$1_t^{-n}$, $t \equiv r - s + 2$ ($e = +$) or $r - s + 6$ ($e = -$), satisfies (32)–(35), and, for $n = 1$, the 3-adic
$1^{\pm0}$ is allowed by (31) (i.e. $e = \left(\frac{-1}{3}\right)^s$). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, pp. 385–386 (I_{r,s}(3^{±1}) and its oddity condition)"]
theorem smallDet_three_typeI (r s : ℕ) (e : Sign) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 3 ∧ (G.two 0).type = .I ∧
        (G.odd 3 1).sign = e) ↔
      (1 ≤ r + s ∧ (r + s = 1 → e = if Even s then .plus else .minus) ∧
        (⟨r + s, .minus, .I, (r : ZMod 8) - s + (if e = .minus then 6 else 2)⟩ : TwoFactor).Exists) := by
  constructor
  · rintro ⟨G, hc, hr, hd, hT, he⟩
    obtain ⟨h1, h2, h3, h4⟩ := G.three_two_zero hc hd hr
    rw [he, hT] at h2
    rw [he] at h4
    refine ⟨h1, h4, ?_⟩
    rw [h2] at h3
    simpa [hT] using h3
  · rintro ⟨h1, hcompat, hE⟩
    refine ⟨det3Data r s e .I _, det3Data_conditions r s e .I _ h1 ?_ hE rfl, rfl, ?_, by simp [det3Data],
      by simp [det3Data]⟩
    · intro h; rw [ofInt_jacobi_three]; exact hcompat h
    · simp [det3Data, Int.natAbs_mul, Int.natAbs_pow]

/-- **Determinant $\pm3$, genera $\mathrm{II}_{r,s}(3^{\pm1})$** (Conway–Sloane, §8.1, pp. 385–386): exists iff
$r - s + 2 \equiv 0$ ($e = +$) or $r - s + 6 \equiv 0 \pmod 8$ ($e = -$). -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, pp. 385–386 (II_{r,s}(3^{±1}) and its oddity condition)"]
theorem smallDet_three_typeII (r s : ℕ) (e : Sign) :
    (∃ G : GenusSymbolData, G.Conditions ∧ G.real = ⟨r, s⟩ ∧ G.det.natAbs = 3 ∧ (G.two 0).type = .II ∧
        (G.odd 3 1).sign = e) ↔
      ((r : ℤ) - s + (if e = .minus then 6 else 2)) % 8 = 0 := by
  rw [← excess_cast_iff]
  constructor
  · rintro ⟨G, hc, hr, hd, hT, he⟩
    obtain ⟨h1, h2, h3, h4⟩ := G.three_two_zero hc hd hr
    rw [he, hT] at h2
    have := h3.2.2.2.2 hT
    rw [h2] at this
    simpa using this
  · intro h
    have hn : 1 ≤ r + s := by
      by_contra hn
      have hr0 : r = 0 := by omega
      have hs0 : s = 0 := by omega
      subst hr0 hs0
      cases e <;> revert h <;> decide
    have hpar : (r + s) % 2 = 0 := by
      have h' := (excess_cast_iff r s e).1 h
      cases e <;> simp at h' <;> omega
    refine ⟨det3Data r s e .II 0, det3Data_conditions r s e .II 0 hn (fun h1 => by omega) ?_ h, rfl, ?_,
      by simp [det3Data], by simp [det3Data]⟩
    · refine ⟨fun h0 => ?_, fun h1 => ?_, (fun _ hI => by cases hI), ?_, fun _ => rfl⟩
      · have h0' : r + s = 0 := h0
        omega
      · have h1' : r + s = 1 := h1
        exfalso
        omega
      show (0 : ZMod 8).val % 2 = (r + s) % 2
      simp
      omega
    · simp [det3Data, Int.natAbs_mul, Int.natAbs_pow]

theorem val_sub_add_mod_two (r s : ℕ) (c : ℤ) (hc : c % 2 = 0) :
    ((r : ZMod 8) - s + (c : ZMod 8)).val % 2 = (r + s) % 2 := by
  have e : ((r : ZMod 8) - s + (c : ZMod 8)) = (((r : ℤ) - s + c : ℤ) : ZMod 8) := by push_cast; rfl
  rw [e]
  have h := ZMod.val_intCast (n := 8) ((r : ℤ) - s + c)
  omega

/-- For $n = r + s \ge 3$ the 2-adic constituent $1_t^{-n}$ of type I always exists ((32)–(35)). -/
theorem typeI_three_exists (r s : ℕ) (e : Sign) (h : 3 ≤ r + s) :
    (⟨r + s, .minus, .I, (r : ZMod 8) - s + (if e = .minus then 6 else 2)⟩ : TwoFactor).Exists := by
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 _ => ?_, ?_, fun h => nomatch h⟩
  · have h0' : r + s = 0 := h0
    omega
  · have h1' : r + s = 1 := h1
    omega
  · have h2' : r + s = 2 := h2
    omega
  · show ((r : ZMod 8) - s + (if e = .minus then 6 else 2)).val % 2 = (r + s) % 2
    cases e
    · simpa using val_sub_add_mod_two r s 2 (by norm_num)
    · simpa using val_sub_add_mod_two r s 6 (by norm_num)

/-- **The failures of $\mathrm I_{r,s}(3^{\pm1})$ for small $n$** (Conway–Sloane, §8.1, p. 386; Table 15.4, rows
$\pm3$: exceptions "$0, 1_{\mp1}, 2_{\mp2}$"): the genus $\mathrm I_{r,s}(3^{e})$ exists for all $(r,s)$ except
$(0,0), (0,1), (0,2)$ if $e = +$ and $(0,0), (1,0), (2,0)$ if $e = -$. The listed 2-adic symbols in the book,
$1_2^{-0}, 1_3^{-1}, 1_1^{-1}, 1_4^{-2}, 1_2^{-2}, 1_0^{-2}$ for $(r,s) = (0,0), (1,0), (0,1), (2,0), (1,1), (0,2)$ and
$e = +$, are $t = r - s + 2$ in each case. -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, p. 386 (failures 0, 1_-, 2_- for I_{r,s}(3); Table 15.4)"]
theorem smallDet_three_typeI_explicit (r s : ℕ) (e : Sign) :
    (1 ≤ r + s ∧ (r + s = 1 → e = if Even s then .plus else .minus) ∧
        (⟨r + s, .minus, .I, (r : ZMod 8) - s + (if e = .minus then 6 else 2)⟩ : TwoFactor).Exists) ↔
      ¬ ((e = .plus ∧ r = 0 ∧ s ≤ 2) ∨ (e = .minus ∧ s = 0 ∧ r ≤ 2)) := by
  by_cases h3 : 3 ≤ r + s
  · constructor
    · rintro -
      rintro (⟨-, h1, h2⟩ | ⟨-, h1, h2⟩) <;> omega
    · intro _
      exact ⟨by omega, fun h => by omega, typeI_three_exists r s e h3⟩
  · have hr : r ≤ 2 := by omega
    have hs : s ≤ 2 := by omega
    interval_cases r <;> interval_cases s <;> (try omega) <;> cases e <;> decide

/-- **The six small cases of $\mathrm I_{r,s}(3)$** (Conway–Sloane, §8.1, p. 386), checked by `decide`: for
$(r,s) = (0,0), (1,0), (0,1), (2,0), (1,1), (0,2)$ the 2-adic constituent $1_t^{-(r+s)}$, $t = r - s + 2$, exists in
exactly the cases $\times, \checkmark, \times, \checkmark, \checkmark, \times$ of the book. (For $(0,1)$: $1_1^{-1}$,
and (33) requires $t \equiv \pm3$.) -/
@[kb "conwaysloane1999" "Ch. 15, §8.1, p. 386 (the six small cases of I_{r,s}(3))"]
theorem smallDet_three_small_cases :
    ¬ (⟨0 + 0, .minus, .I, ((0 : ℕ) : ZMod 8) - ((0 : ℕ) : ZMod 8) + 2⟩ : TwoFactor).Exists ∧
    (⟨1 + 0, .minus, .I, ((1 : ℕ) : ZMod 8) - ((0 : ℕ) : ZMod 8) + 2⟩ : TwoFactor).Exists ∧
    ¬ (⟨0 + 1, .minus, .I, ((0 : ℕ) : ZMod 8) - ((1 : ℕ) : ZMod 8) + 2⟩ : TwoFactor).Exists ∧
    (⟨2 + 0, .minus, .I, ((2 : ℕ) : ZMod 8) - ((0 : ℕ) : ZMod 8) + 2⟩ : TwoFactor).Exists ∧
    (⟨1 + 1, .minus, .I, ((1 : ℕ) : ZMod 8) - ((1 : ℕ) : ZMod 8) + 2⟩ : TwoFactor).Exists ∧
    ¬ (⟨0 + 2, .minus, .I, ((0 : ℕ) : ZMod 8) - ((2 : ℕ) : ZMod 8) + 2⟩ : TwoFactor).Exists := by
  decide

end QuadFormsKB.ConwaySloane
