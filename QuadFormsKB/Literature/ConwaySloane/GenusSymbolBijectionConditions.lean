/-
# Conway–Sloane, Ch. 15, §7.7: the symbols of an integral form satisfy (29), (31)–(35)

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.7, pp. 382–383
(`conwaysloane1999`). The conditions (29)–(35) of §7.7 are necessary: the system of symbols of a nondegenerate
integral form satisfies them. This file proves the *local* conditions — the dimensions, the determinant conditions
(29), the sign of the determinant, the existence conditions (31)–(35) — and the support bound; the oddity formula (30)
is the global one (`GenusSymbolBijectionOddity.lean`).

**Route.** At an odd prime $p$ the symbol of $A$ is that of an *integer* diagonal form $\operatorname{diag}(p^{z_i}w_i)$
(`exists_int_diag_dim`), which by Theorem 9 is $\mathbb Z_p$-equivalent to $A$; at $2$, $A$ is $\mathbb Z_2$-equivalent
to the integer block matrix `dyMatInt D` of its Jordan decomposition. So $\det A$ is the determinant of an explicit
integer matrix times a unit square of $\mathbb Z_p$, and (29) follows from `signProd_oddSymbolOfDiag`,
`signProd_blockSymbol`, `det_dyMatInt`, `valSum_eq` of `Theorem11.lean`.
-/
import QuadFormsKB.Literature.ConwaySloane.GenusSymbolBijection

namespace QuadFormsKB.ConwaySloane

open Matrix Cassels Siegel Finset GenusSymbolData

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} {G : GenusSymbolData}

/-! ### Helpers -/

/-- $\mathbb Z_p$-equivalent integral matrices have determinants differing by a unit *square* of $\mathbb Z_p$. -/
theorem det_sq_of_zpEquiv {p : ℕ} [Fact p.Prime] {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℤ}
    (h : ZpEquiv (A.map (Int.castRingHom ℚ_[p])) (B.map (Int.castRingHom ℚ_[p]))) :
    ∃ c : ℤ_[p], IsUnit c ∧ ((B.det : ℤ) : ℤ_[p]) = c ^ 2 * A.det := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.val.det, (Matrix.isUnit_iff_isUnit_det _).mp T.isUnit, ?_⟩
  have hd := congrArg Matrix.det hT
  rw [det_mul, det_mul, det_transpose, det_map_intCast, det_map_intCast] at hd
  have e := RingHom.map_det PadicInt.Coe.ringHom T.val
  rw [RingHom.mapMatrix_apply] at e
  rw [← e] at hd
  apply Subtype.ext
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_intCast]
  rw [← hd]
  change _ = (PadicInt.Coe.ringHom T.val.det) ^ 2 * _
  ring

/-- Nonzero integers that differ by a unit of $\mathbb Z_p$ have the same $p$-adic valuation. -/
theorem padicValInt_eq_of_unit_mul {p : ℕ} [Fact p.Prime] {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) {u : ℤ_[p]}
    (hu : IsUnit u) (hxy : (x : ℤ_[p]) = u * y) : padicValInt p x = padicValInt p y := by
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

/-- If $W = c^2 a$ in $\mathbb Z_p$ ($p$ odd, $W$, $a$ prime to $p$) then the Jacobi symbols of $W$ and $a$ agree. -/
theorem jacobiSym_eq_of_sq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {W a : ℤ} (hW : ¬ (p : ℤ) ∣ W)
    (ha : ¬ (p : ℤ) ∣ a) (c : ℤ_[p]) (h : (W : ℤ_[p]) = c ^ 2 * a) : jacobiSym W p = jacobiSym a p := by
  have hnd : ¬ (p : ℤ) ∣ W * a := fun hd =>
    ((Nat.prime_iff_prime_int.mp Fact.out).dvd_or_dvd hd).elim hW ha
  have hsq : IsSquare (((W * a : ℤ)) : ℚ_[p]) := by
    refine ⟨(c : ℚ_[p]) * a, ?_⟩
    have h' : (W : ℚ_[p]) = (c : ℚ_[p]) ^ 2 * a := by
      exact_mod_cast congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) h
    push_cast; rw [h']; ring
  have h1 := (isSquare_intCast_padic_iff hp2 hnd).1 hsq
  rw [jacobiSym.mul_left] at h1
  rcases jacobiSym_pm_of_not_dvd hW with h2 | h2 <;> rcases jacobiSym_pm_of_not_dvd ha with h3 | h3 <;>
    simp [h2, h3] at h1 ⊢

/-- If $U = c^2 a$ in $\mathbb Z_2$ with $c$ a unit then $U \equiv a \pmod 8$. -/
theorem mod_eight_eq_of_sq_mul {U a : ℤ} {c : ℤ_[2]} (hc : IsUnit c) (h : (U : ℤ_[2]) = c ^ 2 * a) :
    U % 8 = a % 8 := by
  have h1 := congrArg (PadicInt.toZModPow (p := 2) 3) h
  have hu : IsUnit (PadicInt.toZModPow (p := 2) 3 c) := hc.map _
  have key : ∀ x : ZMod 8, IsUnit x → x ^ 2 = 1 := by decide
  rw [map_intCast, map_mul, map_pow, map_intCast] at h1
  have h2 : ((U : ℤ) : ZMod 8) = a := by
    have h3 := key _ hu
    change ((U : ℤ) : ZMod 8) = ((PadicInt.toZModPow (p := 2) 3 c) ^ 2 * (a : ZMod 8)) at h1
    rw [h3, one_mul] at h1
    exact h1
  exact (ZMod.intCast_eq_intCast_iff' U a 8).1 h2

section OddHelpers

variable {p : ℕ} [Fact p.Prime]

open Classical in
/-- The constituents of the symbol of a diagonal form satisfy (31). -/
theorem oddSymbolOfDiag_exists {m : ℕ} (z : Fin m → ℕ) (u : Fin m → ℚ_[p]) (k : ℕ) :
    (oddSymbolOfDiag p z u k).Exists := by
  intro h
  have h0 : Fintype.card {i // z i = k} = 0 := h
  haveI : IsEmpty {i // z i = k} := Fintype.card_eq_zero_iff.1 h0
  show (if _ then Sign.plus else Sign.minus) = Sign.plus
  refine if_pos ?_
  rw [Fintype.prod_empty]
  exact ⟨1, by simp⟩

/-- A zero-dimensional factor satisfying (31) is the trivial factor. -/
theorem oddFactor_eq_trivial {f : OddFactor} (h : f.Exists) (hd : f.dim = 0) : f = OddFactor.trivial := by
  obtain ⟨d, s⟩ := f
  have h1 : s = .plus := h hd
  have h2 : d = 0 := hd
  subst h1; subst h2; rfl

/-- If the symbol of a diagonal form is supported below $N$, all exponents are $< N$. -/
theorem lt_of_supportedBelow_oddSymbolOfDiag {m N : ℕ} {z : Fin m → ℕ} {u : Fin m → ℚ_[p]}
    (h : (oddSymbolOfDiag p z u).SupportedBelow N) (i : Fin m) : z i < N := by
  by_contra hN
  have h1 := h (z i) (not_lt.mp hN)
  have h2 : Fintype.card {j // z j = z i} = 0 := congrArg OddFactor.dim h1
  have h3 : 0 < Fintype.card {j // z j = z i} := Fintype.card_pos_iff.2 ⟨⟨i, rfl⟩⟩
  omega

/-- The dimensions of the symbol of a diagonal form with exponents $< N$ add up to the size. -/
theorem sum_dim_oddSymbolOfDiag {m N : ℕ} (z : Fin m → ℕ) (u : Fin m → ℚ_[p]) (hz : ∀ i, z i < N) :
    ∑ k ∈ range N, (oddSymbolOfDiag p z u k).dim = m := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to (g := z) (t := range N) (s := (univ : Finset (Fin m)))
    (f := fun _ => (1 : ℕ)) (fun i _ => mem_range.mpr (hz i))
  simp only [sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_fin] at h
  refine Eq.trans (sum_congr rfl fun k _ => ?_) h
  simp [oddSymbolOfDiag, Fintype.card_subtype]

/-- The symbol of a diagonal form is supported below $\max z + 1$. -/
theorem oddSymbolOfDiag_supported {m : ℕ} (z : Fin m → ℕ) (u : Fin m → ℚ_[p]) :
    (oddSymbolOfDiag p z u).SupportedBelow (univ.sup z + 1) := by
  intro k hk
  have hne : IsEmpty {i // z i = k} := ⟨fun ⟨i, hi⟩ => by
    have := Finset.le_sup (f := z) (mem_univ i); omega⟩
  exact oddFactor_eq_trivial (oddSymbolOfDiag_exists z u k) (Fintype.card_eq_zero_iff.2 hne)

end OddHelpers

/-! ### Two-adic helpers -/

theorem dyBlock_dim_pos (b : DyBlock) : 0 < b.dim := by
  cases b <;> simp [DyBlock.dim]

/-- A scale with no block has dimension zero. -/
theorem exp_ne_of_dim_zero : ∀ (D : List DyBlock) (k : ℕ), (blockSymbol D k).dim = 0 →
    ∀ b ∈ D, blockExp b ≠ (k : ℤ)
  | [], _, _ => by simp
  | b :: D, k, h => by
    rw [blockSymbol_cons_dim] at h
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · intro he
      rw [if_pos he] at h
      have := dyBlock_dim_pos c
      omega
    · exact exp_ne_of_dim_zero D k (Nat.add_eq_zero_iff.1 h).2 c hc

/-- If the symbol of a block decomposition is supported below $N$, all exponents are $< N$. -/
theorem blockExp_lt_of_supportedBelow {D : List DyBlock} {N : ℕ} (h : (blockSymbol D).SupportedBelow N)
    (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) : ∀ b ∈ D, blockExp b < N := by
  intro b hb
  by_contra hN
  have h0 := hD0 b hb
  have hk : N ≤ (blockExp b).toNat := by omega
  have h1 := h _ hk
  have h2 : (blockSymbol D (blockExp b).toNat).dim = 0 := congrArg TwoFactor.dim h1
  exact exp_ne_of_dim_zero D _ h2 b hb (by omega)

/-- The dimensions of the symbol of a block decomposition add up to its dimension. -/
theorem sum_dim_blockSymbol {N : ℕ} : ∀ (D : List DyBlock), (∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < N) →
    ∑ k ∈ range N, (blockSymbol D k).dim = dyDim D
  | [], _ => by simp [blockSymbol, dyDim]
  | b :: D, he => by
    obtain ⟨he0, heN⟩ := he b (List.mem_cons_self ..)
    have ih := sum_dim_blockSymbol D fun c hc => he c (List.mem_cons_of_mem _ hc)
    simp only [blockSymbol_cons_dim, blockExp_eq_iff he0, sum_add_distrib, ih]
    rw [Finset.sum_ite_eq, if_pos (mem_range.mpr (by omega))]
    simp [dyDim]

namespace GenusSymbolData.IsGenusSymbolOf

theorem det_ne_zero (hG : G.IsGenusSymbolOf A) : G.det ≠ 0 := by
  obtain ⟨-, -, -, hAd, hAR, -, -⟩ := (G.isGenusSymbolOf_iff A).1 hG
  rw [← hAd]
  exact det_ne_zero_of_congrIn_realVec hAR

/-- (29) at $p = -1$: $\det A < 0$ iff $s$ is odd. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (29), pp. 382–383"]
theorem real_sign (hG : G.IsGenusSymbolOf A) : G.det < 0 ↔ Odd G.real.neg := by
  obtain ⟨-, hr, -, hAd, hAR, -, -⟩ := (G.isGenusSymbolOf_iff A).1 hG
  obtain ⟨c, hc, hcd⟩ := det_congrIn hAR
  rw [det_diagonal, det_map_intCast, hAd] at hcd
  have hprod : ∏ i, ((realVec n G.real.pos i : ℤ) : ℝ) = (-1) ^ G.real.neg := by
    have h := prod_realVec (n := n) (r := G.real.pos) (by omega)
    have h2 : n - G.real.pos = G.real.neg := by omega
    rw [h2] at h
    rw [← Int.cast_prod, h]
    push_cast; rfl
  rw [hprod] at hcd
  have hc0 : c ≠ 0 := hc.ne_zero
  have hcpos : 0 < c ^ 2 := by positivity
  constructor
  · intro h
    by_contra ho
    rw [Nat.not_odd_iff_even.mp ho |>.neg_one_pow] at hcd
    have : (G.det : ℝ) < 0 := by exact_mod_cast h
    nlinarith
  · intro ho
    rw [ho.neg_one_pow] at hcd
    by_contra h
    have : (0 : ℝ) ≤ G.det := by exact_mod_cast not_lt.mp h
    nlinarith

/-- The integer diagonal data of an odd $p$-adic symbol, with the $\mathbb Z_p$-equivalence to $A$. -/
theorem odd_data (hG : G.IsGenusSymbolOf A) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {N : ℕ}
    (hN : (G.odd p).SupportedBelow N) :
    ∃ (z : Fin n → ℕ) (w : Fin n → ℤ), (∀ i, z i < N) ∧ (∀ i, ¬ (p : ℤ) ∣ w i) ∧
      oddSymbolOfDiag p z (fun i => (w i : ℚ_[p])) = G.odd p ∧
      ZpEquiv (A.map (Int.castRingHom ℚ_[p]))
        ((Matrix.diagonal fun i => (p : ℤ) ^ (z i) * w i).map (Int.castRingHom ℚ_[p])) := by
  have hp : p.Prime := Fact.out
  obtain ⟨-, -, -, -, -, hAo, -⟩ := (G.isGenusSymbolOf_iff A).1 hG
  have hA := hAo p hp2
  obtain ⟨z0, u0, hu0, hE0, hs0⟩ := hA
  have hN' : (oddSymbolOfDiag p z0 u0).SupportedBelow N := by rw [← hs0]; exact hN
  have hdim : ∑ k ∈ range N, (G.odd p k).dim = n := by
    rw [hs0]; exact sum_dim_oddSymbolOfDiag z0 u0 (lt_of_supportedBelow_oddSymbolOfDiag hN')
  have hex : ∀ k, (G.odd p k).Exists := by rw [hs0]; exact oddSymbolOfDiag_exists z0 u0
  obtain ⟨z, w, hz, hw, hs⟩ := exists_int_diag_dim hp2 hN hex hdim
  refine ⟨z, w, hz, hw, hs, ?_⟩
  have hB : IsOddSymbolOf p ((Matrix.diagonal fun i => (p : ℤ) ^ (z i) * w i).map (Int.castRingHom ℚ_[p]))
      (G.odd p) := by
    refine ⟨z, fun i => (w i : ℚ_[p]), fun i => ?_, ?_, hs.symm⟩
    · show ‖(w i : ℚ_[p])‖ = 1
      obtain ⟨u, hu⟩ := exists_unit_of_not_dvd (p := p) (w i) (hw i)
      have h1 : ((u : ℤ_[p]) : ℚ_[p]) = (w i : ℚ_[p]) := by rw [hu]; simp
      rw [← h1, PadicInt.norm_coe]
      exact PadicInt.isUnit_iff.mp u.isUnit
    · have e : (Matrix.diagonal fun i => (p : ℤ) ^ (z i) * w i).map (Int.castRingHom ℚ_[p]) =
          Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * (w i : ℚ_[p]) := by
        rw [Matrix.diagonal_map (map_zero _)]
        simp
      rw [e]
      exact ZpEquiv.refl _
  exact zpEquiv_of_oddSymbol_eq hp2 ⟨z0, u0, hu0, hE0, hs0⟩ hB

/-- `odd_data`, with the valuation of $\det A$ and the Jacobi symbol of its unit part. -/
theorem odd_data' (hG : G.IsGenusSymbolOf A) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {N : ℕ}
    (hN : (G.odd p).SupportedBelow N) :
    ∃ (z : Fin n → ℕ) (w : Fin n → ℤ), (∀ i, z i < N) ∧ (∀ i, ¬ (p : ℤ) ∣ w i) ∧
      oddSymbolOfDiag p z (fun i => (w i : ℚ_[p])) = G.odd p ∧ ∑ i, z i = padicValInt p G.det ∧
      jacobiSym (∏ i, w i) p = jacobiSym (unitPart p G.det) p := by
  have hp : p.Prime := Fact.out
  obtain ⟨z, w, hz, hw, hs, hE⟩ := odd_data hG hp2 hN
  have hAd : A.det = G.det := ((G.isGenusSymbolOf_iff A).1 hG).2.2.2.1
  have hd0 : G.det ≠ 0 := hG.det_ne_zero
  obtain ⟨c, hc, hcd⟩ := det_sq_of_zpEquiv hE
  have hWnd : ¬ (p : ℤ) ∣ ∏ i, w i := fun h => by
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)) _).mp h
    exact hw i hi
  have hdet : (Matrix.diagonal fun i => (p : ℤ) ^ (z i) * w i).det = (p : ℤ) ^ (∑ i, z i) * ∏ i, w i := by
    rw [det_diagonal, prod_pow_mul]
  rw [hdet, hAd] at hcd
  have hB0 : (p : ℤ) ^ (∑ i, z i) * ∏ i, w i ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) (fun h => hWnd (h ▸ dvd_zero _))
  have hv : padicValInt p G.det = ∑ i, z i := by
    have := padicValInt_eq_of_unit_mul hB0 hd0 (hc.pow 2) hcd
    rw [← this, padicValInt_pow_mul hWnd]
  refine ⟨z, w, hz, hw, hs, hv.symm, ?_⟩
  have hua := not_dvd_unitPart (p := p) hd0
  have hdz : G.det = (p : ℤ) ^ (∑ i, z i) * unitPart p G.det := by
    rw [← hv]; exact eq_pow_mul_unitPart G.det
  have hpne : ((p : ℤ_[p]) ^ (∑ i, z i)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hW : ((∏ i, w i : ℤ) : ℤ_[p]) = c ^ 2 * (unitPart p G.det : ℤ) := by
    refine mul_left_cancel₀ hpne ?_
    have hcd' := hcd
    conv_rhs at hcd' => rw [hdz]
    push_cast at hcd' ⊢
    linear_combination hcd'
  exact jacobiSym_eq_of_sq hp2 hWnd hua c hW

/-- The $p$-adic symbol of $A$ ($p$ odd) vanishes from the scale $p^{|\det A| + 1}$ on. -/
theorem odd_supportedBelow (hG : G.IsGenusSymbolOf A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (G.odd p).SupportedBelow (G.det.natAbs + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, -, hAo, -⟩ := (G.isGenusSymbolOf_iff A).1 hG
  obtain ⟨z0, u0, -, -, hs0⟩ := hAo p hp2
  have hN0 : (G.odd p).SupportedBelow (univ.sup z0 + 1) := by
    rw [hs0]; exact oddSymbolOfDiag_supported z0 u0
  obtain ⟨z, w, hz, hw, hs, hv, -⟩ := odd_data' hG hp2 hN0
  have hd0 := hG.det_ne_zero
  have hvle : padicValInt p G.det < G.det.natAbs + 1 := by
    have h1 : (p : ℤ) ^ (padicValInt p G.det) ∣ G.det := padicValInt_dvd _
    have h2 : p ^ padicValInt p G.det ∣ G.det.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 h1
      simpa [Int.natAbs_pow] using this
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.2 hd0) h2
    have h4 : padicValInt p G.det < p ^ padicValInt p G.det := Nat.lt_pow_self hp.one_lt
    omega
  intro k hk
  rw [← hs]
  by_cases hne : ∃ i, z i = k
  · exfalso
    obtain ⟨i, rfl⟩ := hne
    have : z i ≤ ∑ j, z j := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  · push_neg at hne
    have hempty : IsEmpty {i // z i = k} := ⟨fun ⟨i, hi⟩ => hne i hi⟩
    exact oddFactor_eq_trivial (oddSymbolOfDiag_exists z _ k) (Fintype.card_eq_zero_iff.2 hempty)

theorem odd_dim (hG : G.IsGenusSymbolOf A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : ℕ}
    (hN : (G.odd p).SupportedBelow N) : ∑ k ∈ range N, (G.odd p k).dim = G.n := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hn, -, -, -, -, hAo, -⟩ := (G.isGenusSymbolOf_iff A).1 hG
  obtain ⟨z0, u0, -, -, hs0⟩ := hAo p hp2
  have hN' : (oddSymbolOfDiag p z0 u0).SupportedBelow N := by rw [← hs0]; exact hN
  rw [hs0, sum_dim_oddSymbolOfDiag z0 u0 (lt_of_supportedBelow_oddSymbolOfDiag hN'), hn]

theorem two_dim (hG : G.IsGenusSymbolOf A) {N : ℕ} (hN : G.two.SupportedBelow N) :
    ∑ k ∈ range N, (G.two k).dim = G.n := by
  obtain ⟨hn, -, -, -, -, -, D, hD, hD0, hdD, -, hσ⟩ := (G.isGenusSymbolOf_iff A).1 hG
  rw [hσ] at hN ⊢
  rw [sum_dim_blockSymbol D fun b hb => ⟨hD0 b hb, blockExp_lt_of_supportedBelow hN hD0 b hb⟩, hdD, hn]

/-- (29) at an odd prime. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (29), pp. 382–383"]
theorem odd_det (hG : G.IsGenusSymbolOf A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : ℕ}
    (hN : (G.odd p).SupportedBelow N) : (G.odd p).DetCond p N G.det := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, w, hz, hw, hs, hv, hJ⟩ := odd_data' hG hp2 hN
  unfold OddSymbol.DetCond
  refine ⟨?_, ?_⟩
  · rw [← hs, ← sum_z_eq z (fun i => (w i : ℚ_[p])) hz]; exact hv
  · rw [← hs, signProd_oddSymbolOfDiag hp2 z w hw hz]
    exact congrArg Sign.ofInt hJ

/-- (29) at $p = 2$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (29), pp. 382–383"]
theorem two_det (hG : G.IsGenusSymbolOf A) {N : ℕ} (hN : G.two.SupportedBelow N) : G.two.DetCond N G.det := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, -, -, hAd, -, -, D, hD, hD0, hdD, hE, hσ⟩ := (G.isGenusSymbolOf_iff A).1 hG
  have hd0 := hG.det_ne_zero
  have hexp : ∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < N := by
    rw [hσ] at hN
    exact fun b hb => ⟨hD0 b hb, blockExp_lt_of_supportedBelow hN hD0 b hb⟩
  have hF2map : ((dyMatInt D).submatrix (Fin.cast hdD.symm) (Fin.cast hdD.symm)).map (Int.castRingHom ℚ_[2]) =
      (dyMat D).submatrix (Fin.cast hdD.symm) (Fin.cast hdD.symm) := by
    rw [← Matrix.submatrix_map, map_dyMatInt D hD0]
  rw [← hF2map] at hE
  obtain ⟨c, hc, hcd⟩ := det_sq_of_zpEquiv hE
  have hdetF : ((dyMatInt D).submatrix (Fin.cast hdD.symm) (Fin.cast hdD.symm)).det =
      2 ^ valSum D * unitProd D := by
    rw [show (Fin.cast hdD.symm : Fin n → Fin (dyDim D)) = ⇑(finCongr hdD.symm) from rfl,
      Matrix.det_submatrix_equiv_self, det_dyMatInt D hD0]
  have hU := odd_unitProd D hD
  rw [hdetF, hAd] at hcd
  have hB0 : (2 : ℤ) ^ valSum D * unitProd D ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ two_ne_zero) (fun h => hU (h ▸ dvd_zero _))
  have hv : padicValInt 2 G.det = valSum D := by
    have := padicValInt_eq_of_unit_mul hB0 hd0 (hc.pow 2) hcd
    rw [← this, padicValInt_two_pow_mul hU]
  unfold TwoSymbol.DetCond
  refine ⟨?_, ?_⟩
  · rw [hσ, hv]; exact (valSum_eq D hexp).symm
  · rw [hσ, signProd_blockSymbol D hD hexp, jacobiTwo_eq_unitPart]
    have hua := not_dvd_unitPart (p := 2) hd0
    have hdz : G.det = (2 : ℤ) ^ (valSum D) * unitPart 2 G.det := by
      rw [← hv]; exact_mod_cast eq_pow_mul_unitPart (p := 2) G.det
    have hpne : ((2 : ℤ_[2]) ^ (valSum D)) ≠ 0 := pow_ne_zero _ two_ne_zero
    have hW : ((unitProd D : ℤ) : ℤ_[2]) = c ^ 2 * (unitPart 2 G.det : ℤ) := by
      refine mul_left_cancel₀ hpne ?_
      have hcd' := hcd
      conv_rhs at hcd' => rw [hdz]
      push_cast at hcd' ⊢
      linear_combination hcd'
    have h8 := mod_eight_eq_of_sq_mul hc hW
    unfold jacobiTwo
    rw [h8]

/-- (31) at an odd prime. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (31), p. 383"]
theorem odd_exists (hG : G.IsGenusSymbolOf A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    (G.odd p k).Exists := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, -, hAo, -⟩ := (G.isGenusSymbolOf_iff A).1 hG
  obtain ⟨z0, u0, -, -, hs0⟩ := hAo p hp2
  rw [hs0]
  exact oddSymbolOfDiag_exists z0 u0 k

/-- (32)–(35) at $p = 2$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (32)–(35), p. 383"]
theorem two_exists (hG : G.IsGenusSymbolOf A) (k : ℕ) : (G.two k).Exists := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact TwoAdic.exists_of_isTwoSymbolOf ((G.isGenusSymbolOf_iff A).1 hG).2.2.2.2.2.2 k

end GenusSymbolData.IsGenusSymbolOf

/-- **A symbol system with a common support bound**: every nondegenerate symmetric $A \in M_n(\mathbb Z)$ has a system
of symbols $G$ all of whose symbols (including the unused entries `G.odd p` for $p$ not an odd prime, taken trivial)
vanish from the scale $p^{G.N}$ on. -/
theorem exists_isGenusSymbolOf_supported (A : Matrix (Fin n) (Fin n) ℤ) (hA : Aᵀ = A) (hdet : A.det ≠ 0) :
    ∃ G : GenusSymbolData, G.IsGenusSymbolOf A ∧ (∀ p, (G.odd p).SupportedBelow G.N) ∧
      G.two.SupportedBelow G.N := by
  classical
  obtain ⟨G, hG⟩ := exists_isGenusSymbolOf A hA hdet
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, hr, hAs, hAd, hAR, hAo, hAt⟩ := (G.isGenusSymbolOf_iff A).1 hG
  obtain ⟨N2, hN2⟩ := TwoAdic.supported_of_isTwoSymbolOf hAt
  let G' : GenusSymbolData := ⟨G.n, G.det, G.real,
    fun p => if p.Prime ∧ p ≠ 2 then G.odd p else fun _ => OddFactor.trivial, G.two,
    max N2 (G.det.natAbs + 1)⟩
  have hG' : G'.IsGenusSymbolOf A := by
    rw [isGenusSymbolOf_iff]
    refine ⟨hn, hr, hAs, hAd, hAR, ?_, hAt⟩
    intro p hp hp2
    show IsOddSymbolOf p _ (if p.Prime ∧ p ≠ 2 then G.odd p else fun _ => OddFactor.trivial)
    rw [if_pos ⟨hp.out, hp2⟩]
    exact hAo p hp2
  refine ⟨G', hG', fun p => ?_, ?_⟩
  · by_cases hp : p.Prime ∧ p ≠ 2
    · have := hG'.odd_supportedBelow hp.1 hp.2
      exact fun k hk => this k (le_trans (le_max_right _ _) hk)
    · intro k _
      show (if p.Prime ∧ p ≠ 2 then G.odd p else fun _ => OddFactor.trivial) k = _
      rw [if_neg hp]
  · exact fun k hk => hN2 k (le_trans (le_max_left _ _) hk)

end QuadFormsKB.ConwaySloane
