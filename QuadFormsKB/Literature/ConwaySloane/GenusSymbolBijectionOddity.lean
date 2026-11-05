/-
# Conway–Sloane, Ch. 15, §7.7, (30): the oddity formula for the symbols of an integral form

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.7, (30), p. 383 and
§5.1, (16), p. 371 (`conwaysloane1999`). For the system of symbols $G$ of a nondegenerate integral form $f$,
$$\mathrm{signature}(f) + \sum_{p \ge 3} p\text{-excess}(f) \equiv \mathrm{oddity}(f) \pmod 8,$$
with the $p$-excesses and the oddity read off the Jordan symbols (§7.7, p. 383). The library had the formula for
diagonal forms (`oddity_formula`); this file proves it for every nondegenerate classically integral form.

**Route** (purely local, plus Hilbert reciprocity only through the diagonal formula). Diagonalize $A$ over
$\mathbb Q$: $A \cong_{\mathbb Q} \langle a_0, \dots, a_{n-1}\rangle$ with $a_i \in \mathbb Z \setminus \{0\}$
(`exists_rat_diag`). At every place $v$, $A$ is also $\mathbb Q_v$-equivalent to an integer diagonal model $\alpha_v$
whose invariant is the one read off the symbol: $\operatorname{diag}(p^{z_i}w_i)$ at odd $p$ (Theorem 9 and
`pExcess_diag_eq`), the diagonal model `dyDiag D` of a Jordan decomposition at $2$ (`oddity_dyDiag`), and
$\langle 1^r, (-1)^s\rangle$ at $\infty$. Integer diagonal forms that are equivalent over $\mathbb Q_v$ have the same
$p$-excess, oddity, signature (Conway–Sloane §6.1: `isometric_padic_iff_pExcess`, `isometric_two_adic_iff_oddity`;
Sylvester). So the invariants of the symbols are those of $\langle a\rangle$, for which (16) is `oddity_formula`.
-/
import QuadFormsKB.Literature.ConwaySloane.GenusSymbolBijectionConditions
import QuadFormsKB.Literature.ConwaySloane.LocalInvariants

namespace QuadFormsKB.ConwaySloane

open Matrix Cassels Siegel Finset GenusSymbolData

variable {n : ℕ}

/-! ### Rational diagonalization with integer entries -/

/-- Congruence passes to ring images. -/
theorem CongrIn.map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) {M M' : Matrix (Fin n) (Fin n) K}
    (h : CongrIn K M M') : CongrIn L (M.map f) (M'.map f) := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨Units.map (RingHom.mapMatrix f).toMonoidHom g, ?_⟩
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, RingHom.mapMatrix_apply,
    Matrix.map_mul, Matrix.transpose_map]

/-- **Diagonalization over $\mathbb Q$ with integer entries**: a nondegenerate symmetric $A \in M_n(\mathbb Z)$ is
congruent over $\mathbb Q$ to $\langle a_0, \dots, a_{n-1}\rangle$ with nonzero integers $a_i$. -/
theorem exists_rat_diag (A : Matrix (Fin n) (Fin n) ℤ) (hA : Aᵀ = A) (hdet : A.det ≠ 0) :
    ∃ a : Fin n → ℤ, (∀ i, a i ≠ 0) ∧
      CongrIn ℚ (A.map (Int.castRingHom ℚ)) (Matrix.diagonal fun i => (a i : ℚ)) := by
  classical
  set M := A.map (Int.castRingHom ℚ) with hM
  have hMs : Mᵀ = M := transpose_map_of_symm _ hA
  have hMd : M.det ≠ 0 := by rw [hM, det_map_intCast]; exact_mod_cast hdet
  have : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  have hB : LinearMap.IsSymm (Matrix.toBilin' M) :=
    LinearMap.BilinForm.isSymm_iff.mp (Matrix.isSymm_toBilin'_iff_isSymm.mpr hMs)
  obtain ⟨v₀, hv₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  have hr : Module.finrank ℚ (Fin n → ℚ) = n := by simp
  set v := v₀.reindex (finCongr hr) with hvdef
  have hv : ∀ i j, i ≠ j → Matrix.toBilin' M (v i) (v j) = 0 := by
    intro i j hij
    simp only [hvdef, Module.Basis.reindex_apply]
    exact hv₀ (fun h => hij (by simpa using congrArg (finCongr hr) h))
  -- the basis as a matrix with the basis vectors as columns
  set e := Pi.basisFun ℚ (Fin n)
  set P : Matrix (Fin n) (Fin n) ℚ := e.toMatrix v with hP
  have hPij : ∀ i j, P i j = v j i := fun i j => by simp [hP, e, Module.Basis.toMatrix_apply]
  have hPu : IsUnit P.det :=
    Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip e v)
  set d : Fin n → ℚ := fun i => Matrix.toBilin' M (v i) (v i) with hd
  have hPMP : Pᵀ * M * P = Matrix.diagonal d := by
    ext i j
    have e1 : (Pᵀ * M * P) i j = Matrix.toBilin' M (v i) (v j) := by
      simp only [Matrix.mul_apply, transpose_apply, hPij, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, Matrix.diagonal_apply]
    split_ifs with h
    · rw [h]
    · exact hv i j h
  have hd0 : ∀ i, d i ≠ 0 := by
    have hdet' : (Matrix.diagonal d).det ≠ 0 := by
      rw [← hPMP, det_mul, det_mul, det_transpose]
      exact mul_ne_zero (mul_ne_zero hPu.ne_zero hMd) hPu.ne_zero
    rw [det_diagonal] at hdet'
    exact fun i => (Finset.prod_ne_zero_iff.mp hdet') i (Finset.mem_univ i)
  have hC : CongrIn ℚ M (Matrix.diagonal d) := ⟨((Matrix.isUnit_iff_isUnit_det P).mpr hPu).unit, by rw [IsUnit.unit_spec]; exact hPMP⟩
  -- clear the denominators
  refine ⟨fun i => (d i).num * (d i).den, fun i => mul_ne_zero (Rat.num_ne_zero.mpr (hd0 i))
    (by exact_mod_cast (d i).den_nz), hC.trans ?_⟩
  have hs := congrIn_diagonal_scale d (fun i => ((d i).den : ℚ))
    (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (d i).den_nz))
  convert hs using 3 with i
  push_cast
  rw [sq, mul_assoc, Rat.den_mul_eq_num]
  ring

/-! ### From congruence of diagonal matrices to isometry of diagonal forms -/

theorem evalIn_diag_eq {K : Type*} [Field K] [CharZero K] (c : Fin n → ℚ) (x : Fin n → K) :
    (QuadForm.diag c).evalIn K x = x ⬝ᵥ ((Matrix.diagonal fun i => (c i : K)) *ᵥ x) := by
  have hmap : (QuadForm.diag c).map (algebraMap ℚ K) =
      Cassels.Ch8Ex2.gramForm (Matrix.diagonal fun i => (c i : K)) := by
    rw [diag_eq_gramForm, gramForm_map, Matrix.diagonal_map (map_zero _)]
    simp [eq_ratCast]
  have hev : (QuadForm.diag c).evalIn K x = ((QuadForm.diag c).map (algebraMap ℚ K)).eval x := by
    simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.map, Matrix.map_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  rw [hev, hmap, eval_gramForm]

/-- Congruent rational diagonal matrices over $K$ give isometric diagonal forms over $K$ (converse of
`congrIn_of_isometricIn_diag`). -/
theorem isometricIn_diag_of_congrIn {K : Type*} [Field K] [CharZero K] (a b : Fin n → ℚ)
    (h : CongrIn K (Matrix.diagonal fun i => (a i : K)) (Matrix.diagonal fun i => (b i : K))) :
    (QuadForm.diag a).IsometricIn K (QuadForm.diag b) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, fun x => ?_⟩
  rw [evalIn_diag_eq, evalIn_diag_eq, ← hg, dotProduct_transpose_mul]

/-! ### The invariants of the symbols are those of the rational diagonalization -/

theorem norm_intCast_eq_one {p : ℕ} [Fact p.Prime] {w : ℤ} (hw : ¬ (p : ℤ) ∣ w) : ‖(w : ℚ_[p])‖ = 1 := by
  have h1 := Padic.norm_int_le_one (p := p) w
  have h2 : ‖(w : ℚ_[p])‖ < 1 ↔ (p : ℤ) ∣ w := Padic.norm_intCast_lt_one_iff
  exact le_antisymm h1 (not_lt.1 fun hlt => hw (h2.1 hlt))

theorem map_map_rat {K : Type*} [Field K] [CharZero K] (A : Matrix (Fin n) (Fin n) ℤ) :
    (A.map (Int.castRingHom ℚ)).map (Rat.castHom K) = A.map (Int.castRingHom K) := by
  ext i j; simp

theorem map_diagonal_rat {K : Type*} [Field K] [CharZero K] (a : Fin n → ℤ) :
    (Matrix.diagonal fun i => (a i : ℚ)).map (Rat.castHom K) = Matrix.diagonal fun i => ((a i : ℚ) : K) := by
  rw [Matrix.diagonal_map (map_zero _)]; rfl

/-- The rational diagonalization, over $K$. -/
theorem congrIn_diag_of_rat {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin n) (Fin n) ℤ} {a : Fin n → ℤ}
    (hA : CongrIn ℚ (A.map (Int.castRingHom ℚ)) (Matrix.diagonal fun i => (a i : ℚ))) :
    CongrIn K (A.map (Int.castRingHom K)) (Matrix.diagonal fun i => ((a i : ℚ) : K)) := by
  have := hA.map (Rat.castHom K)
  rwa [map_map_rat, map_diagonal_rat] at this

/-- Two integer diagonal forms, both congruent over $K$ to $A$, are isometric over $K$. -/
theorem isometricIn_of_congrIn_common {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin n) (Fin n) ℤ}
    {a b : Fin n → ℤ} (ha : CongrIn K (A.map (Int.castRingHom K)) (Matrix.diagonal fun i => ((a i : ℚ) : K)))
    (hb : CongrIn K (A.map (Int.castRingHom K)) (Matrix.diagonal fun i => ((b i : ℤ) : K))) :
    (QuadForm.diag fun i => (a i : ℚ)).IsometricIn K (QuadForm.diag fun i => (b i : ℚ)) := by
  refine isometricIn_diag_of_congrIn _ _ (ha.symm.trans ?_)
  convert hb using 3 with i
  simp

theorem signature_eq_negCount (b : Fin n → ℤ) (hb : ∀ i, b i ≠ 0) :
    signature b = n - 2 * (negCount fun i => (b i : ℚ) : ℤ) := by
  have h : ∀ i, Int.sign (b i) = 1 - 2 * (if ((b i : ℤ) : ℚ) < 0 then 1 else 0 : ℤ) := fun i => by
    rcases lt_or_gt_of_ne (hb i) with h | h
    · have h' : ((b i : ℤ) : ℚ) < 0 := by exact_mod_cast h
      rw [Int.sign_eq_neg_one_of_neg h]; simp [h']
    · have h' : ¬ ((b i : ℤ) : ℚ) < 0 := not_lt.mpr (by exact_mod_cast h.le)
      rw [Int.sign_eq_one_of_pos h]; simp [h']
  unfold signature negCount
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, ← Finset.mul_sum]
  push_cast
  simp

/-- **At $\infty$**: the signature of the rational diagonalization is the signature $r - s$ of the symbol. -/
theorem signature_eq_of_isGenusSymbolOf {A : Matrix (Fin n) (Fin n) ℤ} {G : GenusSymbolData}
    (hG : G.IsGenusSymbolOf A) {a : Fin n → ℤ} (ha : ∀ i, a i ≠ 0)
    (hA : CongrIn ℚ (A.map (Int.castRingHom ℚ)) (Matrix.diagonal fun i => (a i : ℚ))) :
    signature a = G.signature := by
  obtain ⟨-, hGr, -, -, hAR, -, -⟩ := (G.isGenusSymbolOf_iff A).1 hG
  have hr : G.real.pos ≤ n := by omega
  have hiso := isometricIn_of_congrIn_common (congrIn_diag_of_rat (K := ℝ) hA) hAR
  have hneg := negCount_eq_of_isometric _ _ hiso
  rw [signature_eq_negCount a ha, hneg, ← signature_eq_negCount _ (realVec_ne_zero n _), signature_realVec hr,
    GenusSymbolData.signature]
  have : n - G.real.pos = G.real.neg := by omega
  rw [this]

/-- **At an odd prime $p$**: the $p$-excess of the rational diagonalization is the $p$-excess read off the $p$-adic
symbol (given the existence conditions (31) and the dimension, which hold for every form). -/
theorem pExcess_eq_of_isGenusSymbolOf {A : Matrix (Fin n) (Fin n) ℤ} {G : GenusSymbolData}
    (hG : G.IsGenusSymbolOf A) {a : Fin n → ℤ} (ha : ∀ i, a i ≠ 0)
    (hA : CongrIn ℚ (A.map (Int.castRingHom ℚ)) (Matrix.diagonal fun i => (a i : ℚ)))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {N : ℕ} (hN : (G.odd p).SupportedBelow N)
    (hex : ∀ k, (G.odd p k).Exists) (hdim : ∑ k ∈ range N, (G.odd p k).dim = n) :
    pExcess p a = (G.odd p).pExcess p N := by
  obtain ⟨-, -, -, -, -, hAo, -⟩ := (G.isGenusSymbolOf_iff A).1 hG
  obtain ⟨z, w, hz, hw, hs⟩ := exists_int_diag_dim hp2 hN hex hdim
  set α : Fin n → ℤ := fun i => (p : ℤ) ^ (z i) * w i with hα
  have hα0 : ∀ i, α i ≠ 0 := fun i => mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
    (fun h => hw i (h ▸ dvd_zero _))
  have hD : IsOddSymbolOf p (Matrix.diagonal fun i => ((α i : ℤ) : ℚ_[p])) (G.odd p) := by
    refine ⟨z, fun i => (w i : ℚ_[p]), fun i => norm_intCast_eq_one (hw i), ?_, hs.symm⟩
    convert ZpEquiv.refl _ using 3 with i
    simp [hα]
  have hZ := zpEquiv_of_oddSymbol_eq hp2 (hAo p hp2) hD
  have hiso := isometricIn_of_congrIn_common (congrIn_diag_of_rat (K := ℚ_[p]) hA) (congrIn_of_zpEquiv hZ)
  rw [((isometric_padic_iff_pExcess hp2 a α ha hα0).1 hiso).2, ← hs]
  exact pExcess_diag_eq hp2 z w hw hz

theorem blockExp_bounds_of_supportedBelow {D : List DyBlock} {N : ℕ} (hD0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hN : (blockSymbol D).SupportedBelow N) : ∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < N := by
  intro b hb
  refine ⟨hD0 b hb, ?_⟩
  by_contra hlt
  rw [not_lt] at hlt
  have hk := hN (blockExp b).toNat (by omega)
  have hdim := congrArg TwoFactor.dim hk
  simp only [blockSymbol, TwoFactor.trivial] at hdim
  have hmem : b ∈ D.filter fun c => blockExp c = ((blockExp b).toNat : ℤ) := by
    rw [List.mem_filter]; exact ⟨hb, by simp; omega⟩
  have h1 := List.le_sum_of_mem (List.mem_map_of_mem (f := DyBlock.dim) hmem)
  have h2 := dyBlock_one_le_dim b
  omega

/-- **At $2$**: the oddity of the rational diagonalization is the oddity read off the 2-adic symbol. -/
theorem oddity_eq_of_isGenusSymbolOf {A : Matrix (Fin n) (Fin n) ℤ} {G : GenusSymbolData}
    (hG : G.IsGenusSymbolOf A) {a : Fin n → ℤ} (ha : ∀ i, a i ≠ 0)
    (hA : CongrIn ℚ (A.map (Int.castRingHom ℚ)) (Matrix.diagonal fun i => (a i : ℚ)))
    {N : ℕ} (hN : G.two.SupportedBelow N) :
    oddity a = G.two.oddity N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, hAt⟩ := (G.isGenusSymbolOf_iff A).1 hG
  obtain ⟨D, hDv, hD0, h, hFD, hσ⟩ := hAt
  rw [hσ] at hN ⊢
  set α : Fin n → ℤ := fun i => dyDiag D (Fin.cast h.symm i) with hα
  obtain ⟨m, hm⟩ := prod_dyDiag D
  have hU : ¬ (2 : ℤ) ∣ unitProd D := odd_unitProd D hDv
  have hα0 : ∀ i, α i ≠ 0 := fun i hi => by
    have h0 : ∏ j, dyDiag D j = 0 := Finset.prod_eq_zero (mem_univ (Fin.cast h.symm i)) hi
    rw [hm] at h0
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero (pow_ne_zero _ two_ne_zero)
      fun h' => hU (by rw [h']; exact dvd_zero _)) h0
  have hQ := qequiv_cast h (qequiv_dyDiag D hD0)
  have hQ' : Ex5.QEquiv ((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm))
      (Matrix.diagonal fun i => ((α i : ℤ) : ℚ_[2])) := by
    convert hQ using 1
    ext i j
    simp [Matrix.diagonal_apply, hα]
  have hC := (congrIn_of_zpEquiv hFD).trans (congrIn_of_qequiv hQ')
  have hiso := isometricIn_of_congrIn_common (congrIn_diag_of_rat (K := ℚ_[2]) hA) hC
  rw [((isometric_two_adic_iff_oddity a α ha hα0).1 hiso).2, hα, oddity_comp_cast h (dyDiag D),
    oddity_dyDiag D hDv (blockExp_bounds_of_supportedBelow hD0 hN)]

/-! ### The oddity formula (30) and the conditions (29)–(35) for the symbols of a form -/

/-- At an odd prime $p \nmid \det$ the $p$-excess of the symbol vanishes (its only constituent is $1^{\pm n}$). -/
theorem GenusSymbolData.IsGenusSymbolOf.pExcess_eq_zero {A : Matrix (Fin n) (Fin n) ℤ} {G : GenusSymbolData}
    (hG : G.IsGenusSymbolOf A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : ℕ} (hN : (G.odd p).SupportedBelow N)
    (hpd : ¬ (p : ℤ) ∣ G.det) : (G.odd p).pExcess p N = 0 := by
  have h1 := (hG.odd_det hp hp2 hN).1
  rw [padicValInt.eq_zero_of_not_dvd hpd] at h1
  unfold OddSymbol.pExcess
  refine Finset.sum_eq_zero fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [ind8]
  · have hd : (G.odd p k).dim = 0 := by
      have := (Finset.sum_eq_zero_iff.mp (by exact_mod_cast h1)) k hk
      rcases Nat.mul_eq_zero.mp this with h | h
      · omega
      · exact h
    have hs := hG.odd_exists hp hp2 k hd
    simp [hd, hs, ind8]

theorem not_dvd_of_not_mem_primeFactors {x : ℤ} {p : ℕ} (hx : x ≠ 0) (hp : p.Prime)
    (h : p ∉ x.natAbs.primeFactors) : ¬ (p : ℤ) ∣ x := fun hd =>
  h (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hd, Int.natAbs_ne_zero.mpr hx⟩)

/-- **The oddity formula (30) for the symbols of an integral form** (Conway–Sloane, §7.7, (30), p. 383; §5.1, (16),
p. 371): for a system of symbols $G$ of a nondegenerate symmetric $A \in M_n(\mathbb Z)$, all supported below $N$,
$$\mathrm{signature} + \sum_{p \mid d,\, p \ge 3} p\text{-excess} \equiv \mathrm{oddity} \pmod 8,$$
with the $p$-excesses and the oddity read off the Jordan symbols (§7.7, p. 383). The library had (16) for diagonal
forms (`oddity_formula`); here for every form. *Proof:* the invariants of the symbols are those of a rational
diagonalization $\langle a\rangle$ of $A$ at every place (`signature_eq_of_isGenusSymbolOf`,
`pExcess_eq_of_isGenusSymbolOf`, `oddity_eq_of_isGenusSymbolOf`), and (16) holds for $\langle a\rangle$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (30), p. 383; §5.1, (16), p. 371"]
theorem GenusSymbolData.IsGenusSymbolOf.oddity_formula {A : Matrix (Fin n) (Fin n) ℤ} {G : GenusSymbolData}
    (hG : G.IsGenusSymbolOf A) (hodd : ∀ p, (G.odd p).SupportedBelow G.N) (htwo : G.two.SupportedBelow G.N) :
    (G.signature : ZMod 8) + ∑ p ∈ (G.det.natAbs.primeFactors.filter (· ≠ 2)), (G.odd p).pExcess p G.N =
      G.two.oddity G.N := by
  classical
  obtain ⟨hGn, -, hAs, hAd, -, -, -⟩ := (G.isGenusSymbolOf_iff A).1 hG
  have hd0 := hG.det_ne_zero
  obtain ⟨a, ha, hA⟩ := exists_rat_diag A hAs (hAd ▸ hd0)
  have hF := QuadFormsKB.ConwaySloane.oddity_formula a ha
  rw [signature_eq_of_isGenusSymbolOf hG ha hA, oddity_eq_of_isGenusSymbolOf hG ha hA htwo] at hF
  rw [← hF]
  congr 1
  have hPa : (∏ i, a i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  have hconv : ∑ q ∈ oddPrimeSet a, pExcess q.1 a =
      ∑ p ∈ (∏ i, a i).natAbs.primeFactors.filter (· ≠ 2), pExcess p a :=
    (sum_filter_ne_two ((∏ i, a i).natAbs.primeFactors) (fun p hp => Nat.prime_of_mem_primeFactors hp)
      (fun p => pExcess p a)).symm
  rw [hconv]
  symm
  have hmul : ((∏ i, a i) * G.det).natAbs.primeFactors =
      (∏ i, a i).natAbs.primeFactors ∪ G.det.natAbs.primeFactors := by
    rw [Int.natAbs_mul, Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr hPa) (Int.natAbs_ne_zero.mpr hd0)]
  set T := ((∏ i, a i) * G.det).natAbs.primeFactors.filter (· ≠ 2) with hT
  have hterm : ∀ p ∈ T, pExcess p a = (G.odd p).pExcess p G.N := fun p hp => by
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    have hp2 : p ≠ 2 := (mem_filter.mp hp).2
    have : Fact p.Prime := ⟨hpp⟩
    exact pExcess_eq_of_isGenusSymbolOf hG ha hA hp2 (hodd p) (hG.odd_exists hpp hp2)
      (by rw [hG.odd_dim hpp hp2 (hodd p), hGn])
  calc ∑ p ∈ (∏ i, a i).natAbs.primeFactors.filter (· ≠ 2), pExcess p a
      = ∑ p ∈ T, pExcess p a := by
        refine Finset.sum_subset (fun p hp => ?_) (fun p hp hpn => ?_)
        · rw [hT, hmul, filter_union]; exact mem_union_left _ hp
        · have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
          have hp2 : p ≠ 2 := (mem_filter.mp hp).2
          have hnd : ¬ (p : ℤ) ∣ ∏ i, a i :=
            not_dvd_of_not_mem_primeFactors hPa hpp fun h => hpn (mem_filter.mpr ⟨h, hp2⟩)
          refine Finset.sum_eq_zero fun i _ => pExcessEntry_of_not_dvd fun h => hnd ?_
          exact h.trans (Finset.dvd_prod_of_mem _ (mem_univ i))
    _ = ∑ p ∈ T, (G.odd p).pExcess p G.N := Finset.sum_congr rfl hterm
    _ = ∑ p ∈ G.det.natAbs.primeFactors.filter (· ≠ 2), (G.odd p).pExcess p G.N := by
        refine (Finset.sum_subset (fun p hp => ?_) (fun p hp hpn => ?_)).symm
        · rw [hT, hmul, filter_union]; exact mem_union_right _ hp
        · have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
          have hp2 : p ≠ 2 := (mem_filter.mp hp).2
          exact hG.pExcess_eq_zero hpp hp2 (hodd p)
            (not_dvd_of_not_mem_primeFactors hd0 hpp fun h => hpn (mem_filter.mpr ⟨h, hp2⟩))

/-- **The symbols of an integral form satisfy (29)–(35)** (Conway–Sloane, §7.7, pp. 382–383; the necessity of the
conditions of Theorem 11): a system of symbols of a nondegenerate symmetric $A \in M_n(\mathbb Z)$ with a common
support bound `G.N` satisfies `Conditions`. Unconditional: the local conditions are in
`GenusSymbolBijectionConditions.lean`, the oddity formula (30) is `IsGenusSymbolOf.oddity_formula`. (Every form has
such a system: `exists_isGenusSymbolOf_supported`.) -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (29)–(35), pp. 382–383"]
theorem GenusSymbolData.IsGenusSymbolOf.conditions {A : Matrix (Fin n) (Fin n) ℤ} {G : GenusSymbolData}
    (hG : G.IsGenusSymbolOf A) (hodd : ∀ p, (G.odd p).SupportedBelow G.N) (htwo : G.two.SupportedBelow G.N) :
    G.Conditions where
  ne_zero := hG.det_ne_zero
  real_dim := hG.2.2
  real_sign := hG.real_sign
  odd_supp := hodd
  two_supp := htwo
  odd_dim := fun p hp hp2 => hG.odd_dim hp hp2 (hodd p)
  two_dim := hG.two_dim htwo
  odd_det := fun p hp hp2 => hG.odd_det hp hp2 (hodd p)
  two_det := hG.two_det htwo
  odd_exists := fun p hp hp2 k => hG.odd_exists hp hp2 k
  two_exists := hG.two_exists
  oddity_formula := hG.oddity_formula hodd htwo

end QuadFormsKB.ConwaySloane
