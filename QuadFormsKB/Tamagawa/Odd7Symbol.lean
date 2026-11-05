/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Odd7Forms

/-!
# Paper 7 at odd primes: $p$-adic symbols of the tuples of Lemma 2.1

Conway–Sloane's $p$-adic symbol of a diagonal form $\operatorname{diag}(p^{z_i}w_i)$ ($w_i \in \mathbb Z_p^\times$,
$p$ odd) only sees the multiplicities $n_k = \#\{i : z_i = k\}$ and the quadratic characters
$\prod_{z_i = k}\left(\frac{w_i}{p}\right)$. This file makes that explicit:

* `chiU : ℤ_[p]ˣ →* ℤˣ`: the Legendre symbol of the residue; `isSquare_coe_unit_iff`: a $p$-adic unit is a square in
  $\mathbb Q_p$ iff $\chi = 1$;
* `symC z x`: the symbol with dimensions $\#\{z_i = k\}$ and signs $\prod_{z_i=k}x_i$;
  `oddSymbolOfDiag_eq_symC`: it is the symbol of the diagonal form;
* `symT a b x y z`: `symC` at $z = (0, a, b)$ written without sums; `symT_inj`: on the tuples of Lemma 2.1
  (`IsJordanTuple`) it is injective; `normT` normalizes arbitrary unit characters to a Jordan tuple with the same symbol.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Odd7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal QuadFormsKB.Siegel QuadFormsKB.Tamagawa

noncomputable section

section Chi

variable {p : ℕ} [hp : Fact p.Prime]

/-- The Legendre symbol of the residue of a $p$-adic integer, $\left(\frac{x}{p}\right)$ (zero if $p \mid x$). -/
def chi (x : ℤ_[p]) : ℤ := quadraticChar (ZMod p) (PadicInt.toZMod x)

/-- $\left(\frac{\cdot}{p}\right)$ as a monoid homomorphism $\mathbb Z_p \to \mathbb Z$. -/
def chiHom : ℤ_[p] →* ℤ where
  toFun := chi
  map_one' := by simp [chi]
  map_mul' x y := by unfold chi; rw [map_mul, map_mul]

theorem chiHom_apply (x : ℤ_[p]) : chiHom x = chi x := rfl

/-- **The Legendre symbol of a $p$-adic unit** as a homomorphism $\mathbb Z_p^\times \to \{\pm1\}$. -/
def chiU : ℤ_[p]ˣ →* ℤˣ := Units.map chiHom

theorem chiU_val (u : ℤ_[p]ˣ) : ((chiU u : ℤˣ) : ℤ) = chi (u : ℤ_[p]) := rfl

theorem chi_unit {x : ℤ_[p]} (hx : IsUnit x) : chi x = 1 ∨ chi x = -1 := by
  unfold chi
  exact quadraticChar_dichotomy (hx.map (PadicInt.toZMod (p := p))).ne_zero

theorem chi_mul (x y : ℤ_[p]) : chi (x * y) = chi x * chi y := map_mul chiHom x y

/-- The Legendre symbol of the square of a unit is $1$. -/
theorem chi_sq {s : ℤ_[p]} (hs : IsUnit s) : chi (s ^ 2) = 1 := by
  rw [sq, chi_mul]
  rcases chi_unit hs with h | h <;> rw [h] <;> norm_num

/-- **A $p$-adic unit is a square in $\mathbb Q_p$ iff its Legendre symbol is $1$** ($p$ odd; Hensel). -/
theorem isSquare_coe_unit_iff (hp2 : p ≠ 2) (u : ℤ_[p]ˣ) :
    IsSquare (((u : ℤ_[p]) : ℚ_[p])) ↔ chiU u = 1 := by
  rw [isSquare_unit_iff hp2 u, ← Units.val_eq_one, chiU_val]
  unfold chi
  exact (quadraticChar_one_iff_isSquare (u.isUnit.map (PadicInt.toZMod (p := p))).ne_zero).symm

theorem isUnit_intCast_of_not_dvd {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : IsUnit ((z : ℤ) : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  have h1 : ‖((z : ℤ) : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
  have h2 : ¬ ‖((z : ℤ) : ℤ_[p])‖ < 1 := fun h => hz ((PadicInt.norm_int_lt_one_iff_dvd z).1 h)
  exact le_antisymm h1 (not_lt.1 h2)

theorem chi_intCast_nonres {c : ℤ} (hc : jacobiSym c p = -1) : chi ((c : ℤ) : ℤ_[p]) = -1 := by
  unfold chi
  rw [map_intCast, ← hc, ← jacobiSym.legendreSym.to_jacobiSym]
  rfl

/-- The unit of $\mathbb Z_p$ representing the square class $e = \pm1$: $1$ or the non-residue $c$. -/
def repU {c : ℤ} (hc : jacobiSym c p = -1) (e : ℤˣ) : ℤ_[p]ˣ :=
  (isUnit_intCast_of_not_dvd (p := p) (z := rep c e) (by
    unfold rep
    split_ifs
    · exact (Nat.prime_iff_prime_int.mp hp.out).not_dvd_one
    · exact not_dvd_of_jacobiSym hc)).unit

theorem repU_val {c : ℤ} (hc : jacobiSym c p = -1) (e : ℤˣ) :
    ((repU hc e : ℤ_[p]ˣ) : ℤ_[p]) = ((rep c e : ℤ) : ℤ_[p]) := rfl

/-- **The Legendre symbol of `repU e` is $e$.** -/
theorem chiU_repU {c : ℤ} (hc : jacobiSym c p = -1) (e : ℤˣ) : chiU (repU hc e) = e := by
  apply Units.ext
  rw [chiU_val, repU_val]
  unfold rep
  by_cases he : e = 1
  · rw [if_pos he, he]
    simp [chi]
  · have he' : e = -1 := by
      rcases Int.units_eq_one_or e with h | h
      · exact absurd h he
      · exact h
    rw [if_neg he, chi_intCast_nonres hc, he']
    rfl

end Chi

/-! ### The combinatorial symbol -/

section SymC

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The symbol with multiplicities $\#\{i : z_i = k\}$ and signs $\prod_{z_i = k}x_i$** (as $\pm$). -/
def symC {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) : OddSymbol := fun k =>
  ⟨∑ i, if z i = k then 1 else 0, if (∏ i, if z i = k then x i else 1) = 1 then Sign.plus else Sign.minus⟩

theorem symC_perm {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) (σ : Equiv.Perm (Fin n)) :
    symC (fun i => z (σ i)) (fun i => x (σ i)) = symC z x := by
  funext k
  simp only [symC]
  have h1 : ∑ i, (if z (σ i) = k then 1 else 0) = ∑ i, (if z i = k then 1 else 0) :=
    Equiv.sum_comp σ (fun i => if z i = k then (1 : ℕ) else 0)
  have h2 : ∏ i, (if z (σ i) = k then x (σ i) else 1) = ∏ i, (if z i = k then x i else 1) :=
    Equiv.prod_comp σ (fun i => if z i = k then x i else 1)
  rw [h1, h2]

/-- **The $p$-adic symbol of the diagonal form $\operatorname{diag}(p^{z_i}w_i)$** (units $w_i \in \mathbb Z_p^\times$,
$p$ odd) is `symC z (χ(w_i))`. -/
theorem oddSymbolOfDiag_eq_symC (hp2 : p ≠ 2) {n : ℕ} (z : Fin n → ℕ) (w : Fin n → ℤ_[p]ˣ) :
    oddSymbolOfDiag p z (fun i => (((w i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) = symC z (fun i => chiU (w i)) := by
  funext k
  unfold oddSymbolOfDiag symC
  rw [card_subtype_eq_sum, prod_subtype_eq_prod_ite z k (fun i => (((w i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]))]
  let ι : ℤ_[p]ˣ →* ℚ_[p] := (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom.comp (Units.coeHom ℤ_[p])
  set W : ℤ_[p]ˣ := ∏ i, if z i = k then w i else 1 with hW
  have h1 : ι W = ∏ i, ι (if z i = k then w i else 1) := map_prod ι _ _
  have h2 : ∀ i, ι (if z i = k then w i else 1) =
      if z i = k then (((w i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) else 1 := by
    intro i
    split_ifs <;> simp [ι]
  have hcoe : ι W = ∏ i, if z i = k then (((w i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) else 1 := by
    rw [h1]
    exact Finset.prod_congr rfl fun i _ => h2 i
  have h3 : chiU W = ∏ i, if z i = k then chiU (w i) else 1 := by
    rw [hW, map_prod]
    exact Finset.prod_congr rfl fun i _ => by split_ifs <;> simp
  have key : IsSquare (∏ i, if z i = k then (((w i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) else 1) ↔
      (∏ i, if z i = k then chiU (w i) else 1) = 1 := by
    rw [← hcoe, ← h3]
    exact isSquare_coe_unit_iff hp2 W
  congr 1
  by_cases hA : IsSquare (∏ i, if z i = k then (((w i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) else 1)
  · rw [if_pos hA, if_pos (key.1 hA)]
  · rw [if_neg hA, if_neg (fun h => hA (key.2 h))]

end SymC

/-! ### The symbol of a tuple of Lemma 2.1, without sums -/

/-- **`symC` at the exponents $(0, a, b)$**, written out: the multiplicity of $p^k$ is
$[0 = k] + [a = k] + [b = k]$ and its sign is the product of the characters of the entries of exponent $k$. -/
def symT (a b : ℕ) (x y z : ℤˣ) : OddSymbol := fun k =>
  ⟨(if 0 = k then 1 else 0) + (if a = k then 1 else 0) + (if b = k then 1 else 0),
    if (if 0 = k then x else 1) * (if a = k then y else 1) * (if b = k then z else 1) = 1 then Sign.plus
    else Sign.minus⟩

theorem symC_three (a b : ℕ) (x y z : ℤˣ) : symC ![0, a, b] ![x, y, z] = symT a b x y z := by
  funext k
  simp only [symC, symT, Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rfl

/-- **Normalization of unit characters to a Jordan tuple** (Lemma 2.1, constraints (1)–(3)): the Jordan tuple
$(a, b; u_1, u_2, u_3)$ with the same symbol as the characters $(x, y, z)$ at the exponents $(0, a, b)$. -/
def normT (a b : ℕ) (x y z : ℤˣ) : ℤˣ × ℤˣ × ℤˣ :=
  if a = 0 ∧ b = 0 then (1, 1, x * y * z)
  else if a = 0 then (1, x * y, z)
  else if a = b then (x, 1, y * z)
  else (x, y, z)

theorem isJordanTuple_normT {a b : ℕ} (hab : a ≤ b) (x y z : ℤˣ) :
    IsJordanTuple a b (normT a b x y z).1 (normT a b x y z).2.1 (normT a b x y z).2.2 := by
  unfold IsJordanTuple normT
  by_cases h1 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h1
    simp
  · by_cases h2 : a = 0
    · subst h2
      have hb : b ≠ 0 := fun h => h1 ⟨rfl, h⟩
      simp [hb]
    · by_cases h3 : a = b
      · subst h3
        simp [h2]
      · simp [h1, h2, h3, hab]

theorem normT_1 {a b : ℕ} (h : a = 0 ∧ b = 0) (x y z : ℤˣ) : normT a b x y z = (1, 1, x * y * z) := by
  simp [normT, h]

theorem normT_2 {a b : ℕ} (ha : a = 0) (hb : b ≠ 0) (x y z : ℤˣ) : normT a b x y z = (1, x * y, z) := by
  simp [normT, ha, hb]

theorem normT_3 {a b : ℕ} (ha : a ≠ 0) (hab : a = b) (x y z : ℤˣ) : normT a b x y z = (x, 1, y * z) := by
  subst hab
  simp [normT, ha]

theorem normT_4 {a b : ℕ} (ha : a ≠ 0) (hab : a ≠ b) (x y z : ℤˣ) : normT a b x y z = (x, y, z) := by
  simp [normT, ha, hab]

theorem symT_normT (a b : ℕ) (x y z : ℤˣ) :
    symT a b x y z = symT a b (normT a b x y z).1 (normT a b x y z).2.1 (normT a b x y z).2.2 := by
  funext k
  by_cases h1 : a = 0 ∧ b = 0
  · rw [normT_1 h1]
    obtain ⟨rfl, rfl⟩ := h1
    by_cases hk : (0 : ℕ) = k <;> simp [symT, hk]
  · by_cases h2 : a = 0
    · have hb : b ≠ 0 := fun h => h1 ⟨h2, h⟩
      rw [normT_2 h2 hb]
      subst h2
      by_cases hk : (0 : ℕ) = k
      · subst hk
        simp [symT, hb]
      · by_cases hk' : b = k <;> simp [symT, hk, hk', hb]
    · by_cases h3 : a = b
      · rw [normT_3 h2 h3]
        subst h3
        by_cases hk : (0 : ℕ) = k
        · subst hk
          simp [symT, h2]
        · by_cases hk' : a = k <;> simp [symT, hk, hk', h2, mul_assoc]
      · rw [normT_4 h2 h3]

theorem units_eq_of_sign {P P' : ℤˣ}
    (h : (if P = 1 then Sign.plus else Sign.minus) = (if P' = 1 then Sign.plus else Sign.minus)) : P = P' := by
  have hn : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or P with rfl | rfl <;> rcases Int.units_eq_one_or P' with rfl | rfl <;>
    simp_all

theorem sum_dim_weighted (a b M : ℕ) (ha : a < M) (hb : b < M) (h0 : 0 < M) (f : ℕ → ℕ) :
    ∑ k ∈ range M, f k * ((if 0 = k then 1 else 0) + (if a = k then 1 else 0) + (if b = k then 1 else 0)) =
      f 0 + f a + f b := by
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  rw [if_pos h0, if_pos ha, if_pos hb]

theorem jordan_shape {a b : ℕ} (hab : a ≤ b) :
    (a = 0 ∧ b = 0) ∨ (a = 0 ∧ 0 < b) ∨ (0 < a ∧ a = b) ∨ (0 < a ∧ a < b) := by omega

/-- **The symbol separates the Jordan tuples of Lemma 2.1:** two Jordan tuples with the same symbol are equal. -/
theorem symT_inj {a b a' b' : ℕ} {x y z x' y' z' : ℤˣ}
    (h : IsJordanTuple a b x y z) (h' : IsJordanTuple a' b' x' y' z')
    (hs : symT a b x y z = symT a' b' x' y' z') :
    a = a' ∧ b = b' ∧ x = x' ∧ y = y' ∧ z = z' := by
  have hd : ∀ k, ((if 0 = k then 1 else 0) + (if a = k then 1 else 0) + (if b = k then 1 else 0) : ℕ) =
      (if 0 = k then 1 else 0) + (if a' = k then 1 else 0) + (if b' = k then 1 else 0) := fun k =>
    congrArg (fun s => (s k).dim) hs
  have hsg : ∀ k, (if (if 0 = k then x else 1) * (if a = k then y else 1) * (if b = k then z else 1) = 1
      then Sign.plus else Sign.minus) =
      (if (if 0 = k then x' else 1) * (if a' = k then y' else 1) * (if b' = k then z' else 1) = 1
      then Sign.plus else Sign.minus) := fun k => congrArg (fun s => (s k).sign) hs
  obtain ⟨hab, h1, h2, h3⟩ := h
  obtain ⟨hab', h1', h2', h3'⟩ := h'
  set M := b + b' + 1 with hM
  have hws : ∀ f : ℕ → ℕ, f 0 + f a + f b = f 0 + f a' + f b' := by
    intro f
    rw [← sum_dim_weighted a b M (by omega) (by omega) (by omega) f,
      ← sum_dim_weighted a' b' M (by omega) (by omega) (by omega) f]
    exact Finset.sum_congr rfl fun k _ => by rw [hd k]
  have e1 : a + b = a' + b' := by
    have := hws (fun k => k)
    simpa using this
  have e2 : a * a + b * b = a' * a' + b' * b' := by
    have := hws (fun k => k * k)
    simpa using this
  have hab_eq : a = a' ∧ b = b' := by
    have key : (a : ℤ) = a' ∨ (a : ℤ) = b' := by
      have e1' : (a : ℤ) + b = a' + b' := by exact_mod_cast e1
      have e2' : (a : ℤ) * a + b * b = a' * a' + b' * b' := by exact_mod_cast e2
      have h0 : 2 * (((a : ℤ) - a') * ((a : ℤ) - b')) = 0 := by
        linear_combination ((a : ℤ) - b - a' - b') * e1' + e2'
      rcases mul_eq_zero.1 (by linarith : ((a : ℤ) - a') * ((a : ℤ) - b') = 0) with h | h
      · left; linarith
      · right; linarith
    rcases key with h | h
    · have : a = a' := by exact_mod_cast h
      omega
    · have : a = b' := by exact_mod_cast h
      omega
  obtain ⟨rfl, rfl⟩ := hab_eq
  refine ⟨rfl, rfl, ?_⟩
  have p0 := units_eq_of_sign (hsg 0)
  have pa := units_eq_of_sign (hsg a)
  have pb := units_eq_of_sign (hsg b)
  rcases jordan_shape hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · subst ha hb
    obtain ⟨rfl, rfl⟩ := h1 rfl rfl
    obtain ⟨rfl, rfl⟩ := h1' rfl rfl
    simp at p0
    exact ⟨rfl, rfl, p0⟩
  · subst ha
    have hb' : b ≠ 0 := by omega
    obtain rfl := h2 rfl hb'
    obtain rfl := h2' rfl hb'
    simp [hb', hb'.symm] at p0 pb
    exact ⟨rfl, p0, pb⟩
  · subst hb
    have ha' : a ≠ 0 := by omega
    obtain rfl := h3 ha' rfl
    obtain rfl := h3' ha' rfl
    simp [ha', ha'.symm] at p0 pa
    exact ⟨p0, rfl, by simpa using pa⟩
  · have ha' : a ≠ 0 := by omega
    have hb' : a ≠ b := by omega
    have hb0 : b ≠ 0 := by omega
    simp [ha'.symm, hb', hb0.symm, hb'.symm, ha', hb0] at p0 pa pb
    exact ⟨p0, pa, pb⟩

end

end QuadFormsKB.Odd7
