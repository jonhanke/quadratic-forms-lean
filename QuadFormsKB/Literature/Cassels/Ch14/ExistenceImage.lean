/-
# Cassels, Chapter 14, §5: Theorem 5.1 (which families of local classes come from a global form)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §5, p. 343, Theorem 5.1 and the first lines of the proof of its
Corollary, p. 344.

Cassels' Theorem 5.1: *if $D$ is a perfect square, the image of $\mathcal G \to \prod_{p \le \infty} \mathcal G_p$ is the
entire group; otherwise the image is a subgroup of index $2$.* The local groups $\mathcal G_p$ of $\mathbb Z_p$-classes
are not formalized, so the theorem is stated here through the character that cuts out the image, the product
$\prod_{p \le \infty} c_p$ of Hasse–Minkowski invariants (Cassels, proof of the Corollary, p. 344: "the condition (5.4)
determines a subgroup of (5.3) which is of index 2 if $D$ is not a square, otherwise the whole group. This subgroup
contains the image of (5.2) and so must coincide with it"):

* `thm_5_1`: a family $(f_p)_{p \le \infty}$ of primitive $\mathbb Z_p$-integral binary forms of discriminant $D$
  comes from one primitive integral form of discriminant $D$ (is its family of localizations up to
  $\mathbb Z_p$-equivalence) if and only if $\prod_{p \le \infty} c_p(f_p) = 1$;
* `prod_hasse_eq_one_of_isSquare`: if $D$ is a square, every family satisfies $\prod_p c_p(f_p) = 1$ (indeed every
  $c_p(f_p) = 1$), so every family comes from a global form ("the image is the entire group");
* `exists_prod_hasse_eq_neg_one`: if $D$ is not a square, some family of primitive local forms of discriminant $D$ has
  $\prod_p c_p(f_p) = -1$, so the condition is a non-trivial character and the image is the kernel of a
  surjective character onto $\{\pm 1\}$ ("a subgroup of index $2$").

The necessity of $\prod_p c_p = 1$ for a global form is Hilbert's product formula (`hilbert_product_formula`); its
sufficiency is the Corollary to Theorem 5.1 (`exists_int_form_of_local`). Lemma 3.4 (the order of
$\prod_p \mathcal G_p$) is not formalized.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Existence
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity

namespace QuadFormsKB.Composition

open QuadForm Siegel
open scoped Matrix

/-! ### Helpers -/

/-- Over `ℝ`, `hasseC` can be computed from any diagonalization. -/
theorem hasseC_eq_of_isometric_real {g : QuadForm ℝ 2} (hg : g.Nondegenerate) {a : Fin 2 → ℝ}
    (ha : ∀ i, a i ≠ 0) (h : g.IsometricIn ℝ (QuadForm.diag a)) : hasseC g = PadicClass.hasseVec a := by
  classical
  have hex := FieldGen.exists_isometric_diag g hg
  unfold hasseC
  simp only [hg, ↓reduceDIte]
  obtain ⟨hb0, hbiso⟩ := Classical.choose_spec hex
  exact real_hasse_eq hb0 ha (QuadForm.isometricIn_trans _ (QuadForm.isometricIn_symm _ hbiso) h)

/-- Base change of a rational isometry to a field extension, as an isometry of the base-changed forms. -/
theorem isometricIn_map_base (K : Type*) [Field K] [Algebra ℚ K] {n : ℕ} {Q Q' : QuadForm ℚ n}
    (h : Q.IsometricIn ℚ Q') : (Q.map (algebraMap ℚ K)).IsometricIn K (Q'.map (algebraMap ℚ K)) := by
  obtain ⟨P, hP, hx⟩ := FieldGen.isometricIn_of_base K h
  refine ⟨P, hP, fun x => ?_⟩
  have e : ∀ (R : QuadForm ℚ n) (y : Fin n → K), R.evalIn K y = (R.map (algebraMap ℚ K)).eval y := by
    intro R y
    simp [QuadForm.evalIn, QuadForm.map]
  have := hx x
  rw [e, e] at this
  exact this

/-- Products over all places: if `ε` is `±1` valued with finitely many `-1`, an even number of them, then
`∏_p ε_p * ε_∞ = 1`. -/
theorem finprod_places_eq_one (ε : RatPlace → ℤ) (hε : ∀ v, ε v = 1 ∨ ε v = -1)
    (hfin : {v | ε v = -1}.Finite) (hev : Even {v | ε v = -1}.ncard) :
    (∏ᶠ p : Nat.Primes, ε (.finite p)) * ε .infinite = 1 := by
  classical
  have hinj : Function.Injective RatPlace.finite := fun a b h => by injection h
  set T : Set Nat.Primes := {p | ε (.finite p) = -1} with hT
  have hTfin : T.Finite := hfin.preimage hinj.injOn
  have hprod : ∏ᶠ p : Nat.Primes, ε (.finite p) = (-1) ^ T.ncard := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hTfin.toFinset) (by
      intro p hp
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      rcases hε (.finite p) with h | h
      · exact absurd h hp
      · exact h)]
    rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℤ)) (by
      intro p hp
      rw [Set.Finite.mem_toFinset] at hp
      exact hp)]
    rw [Finset.prod_const, Set.ncard_eq_toFinset_card T hTfin]
  rw [hprod]
  rcases hε .infinite with hc | hc
  · have hset : {v | ε v = -1} = RatPlace.finite '' T := by
      ext v
      cases v with
      | infinite => simp [hc]
      | finite p => simp [hT]
    rw [hset, Set.ncard_image_of_injective _ hinj] at hev
    rw [hc, hev.neg_one_pow, one_mul]
  · have hset : {v | ε v = -1} = insert RatPlace.infinite (RatPlace.finite '' T) := by
      ext v
      cases v with
      | infinite => simp [hc]
      | finite p => simp [hT]
    rw [hset, Set.ncard_insert_of_notMem (by simp) (hTfin.image _),
      Set.ncard_image_of_injective _ hinj] at hev
    have : Odd T.ncard := by
      rcases Nat.even_or_odd T.ncard with h | h
      · exact absurd hev (by rw [Nat.even_add_one]; exact not_not.mpr h)
      · exact h
    rw [hc, this.neg_one_pow]; norm_num

/-- **Key lemma.** If binary forms `g_p` over `ℚ_p` and `gInf` over `ℝ` are all isometric to the localizations of one
rational form `G` of discriminant `D ≠ 0`, then `∏_{p ≤ ∞} c_p = 1`. -/
theorem prod_hasse_of_rat_iso {D : ℚ} (hD : D ≠ 0) (G : QuadForm ℚ 2) (hG : -G.hessian.det = D)
    (g : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℚ_[p] 2) (hg : ∀ (p : ℕ) [Fact p.Prime], (g p).Nondegenerate)
    (gInf : QuadForm ℝ 2) (hgInf : gInf.Nondegenerate)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], (g p).IsometricIn ℚ_[p] (G.map (algebraMap ℚ ℚ_[p])))
    (hinf : gInf.IsometricIn ℝ (G.map (algebraMap ℚ ℝ))) :
    (∏ᶠ p : Nat.Primes, hasseAt g p) * hasseC gInf = 1 := by
  obtain ⟨α, hα, hiso⟩ := exists_normal_form (nondeg_of_det hD hG) hG
  have hβ : (-D / (4 * α)) ≠ 0 := hne_diag_two hD hα 1
  have hp : ∀ p : Nat.Primes, hasseAt g p = RatPlace.hilbert (.finite p) α (-D / (4 * α)) := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    have h1 := isometricIn_map_base ℚ_[p] hiso
    rw [map_diag] at h1
    have h2 := QuadForm.isometricIn_trans _ (hloc p) h1
    show hasseC (g p) = _
    have e : (algebraMap ℚ ℚ_[p]) ∘ (![α, -D / (4 * α)] : Fin 2 → ℚ) =
        ![(α : ℚ_[p]), ((-D / (4 * α) : ℚ) : ℚ_[p])] := by
      funext i; fin_cases i <;> rfl
    rw [e] at h2
    rw [hasseC_eq_of_isometric (p : ℕ) (hg p) (a := ![(α : ℚ_[p]), ((-D / (4 * α) : ℚ) : ℚ_[p])]) ?_ h2,
      PadicClass.hasseVec_two]
    · rfl
    · intro i; fin_cases i
      · simpa using hα
      · simpa using hβ
  have hi : hasseC gInf = RatPlace.hilbert .infinite α (-D / (4 * α)) := by
    have h1 := isometricIn_map_base ℝ hiso
    rw [map_diag] at h1
    have h2 := QuadForm.isometricIn_trans _ hinf h1
    have e : (algebraMap ℚ ℝ) ∘ (![α, -D / (4 * α)] : Fin 2 → ℚ) =
        ![(α : ℝ), ((-D / (4 * α) : ℚ) : ℝ)] := by
      funext i; fin_cases i <;> rfl
    rw [e] at h2
    rw [hasseC_eq_of_isometric_real hgInf (a := ![(α : ℝ), ((-D / (4 * α) : ℚ) : ℝ)]) ?_ h2,
      PadicClass.hasseVec_two]
    · rfl
    · intro i; fin_cases i
      · simpa using hα
      · simpa using hβ
  rw [finprod_congr hp, hi]
  obtain ⟨hfin, hev⟩ := hilbert_product_formula α (-D / (4 * α)) hα hβ
  refine finprod_places_eq_one (fun v => v.hilbert α (-D / (4 * α))) ?_ hfin hev
  intro v
  cases v <;> simp only [RatPlace.hilbert, hilbertSymbol] <;> split_ifs <;> simp

/-- The Hessian determinant of the base change of an integral binary form: `-det H = disc`. -/
theorem neg_det_map_int {K : Type*} [CommRing K] (F : BinQF) (φ : ℤ →+* K) :
    -(F.map φ).hessian.det = φ F.disc := by
  rw [Binary.hessian_det_two]
  simp [QuadForm.map, BinQF.disc, BinQF.a, BinQF.b, BinQF.c]

/-- `2 Q(x) = xᵀ H x` over a field. -/
theorem two_mul_eval' {K : Type*} [Field K] {n : ℕ} (Q : QuadForm K n) (x : Fin n → K) :
    2 * Q.eval x = x ⬝ᵥ (Q.hessian *ᵥ x) := by
  have h := QuadForm.evalIn_eq_dotProduct K Q x
  have h' : Q.eval x = x ⬝ᵥ (Q.coeff *ᵥ x) := by
    rw [show Q.eval x = Q.evalIn K x from rfl, h]
    simp
  rw [h', QuadForm.hessian, Matrix.add_mulVec, dotProduct_add]
  have : x ⬝ᵥ (Q.coeffᵀ *ᵥ x) = x ⬝ᵥ (Q.coeff *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [this]; ring

/-- Forms over a field of characteristic `0` with congruent Hessians are isometric. -/
theorem isometricIn_of_hessian {K : Type*} [Field K] [CharZero K] {n : ℕ} {Q Q' : QuadForm K n}
    (P : Matrix (Fin n) (Fin n) K) (hP : IsUnit P.det) (h : Pᵀ * Q.hessian * P = Q'.hessian) :
    Q.IsometricIn K Q' := by
  refine ⟨P, hP, fun x => ?_⟩
  apply mul_left_cancel₀ (two_ne_zero : (2 : K) ≠ 0)
  show 2 * Q.eval (P *ᵥ x) = 2 * Q'.eval x
  rw [two_mul_eval', two_mul_eval', ← h]
  symm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- The `p`-adic localization of an integral form is the base change of its rationalization. -/
theorem map_padic_eq (p : ℕ) [Fact p.Prime] (F : BinQF) :
    (F.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom =
      (F.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[p]) := by
  rw [Siegel.map_map_int, Siegel.map_map_int]

/-- The real localization of an integral form is the base change of its rationalization. -/
theorem map_real_eq (F : BinQF) :
    F.map (Int.castRingHom ℝ) = (F.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) := by
  rw [Siegel.map_map_int]

/-- A `ℤ_p`-equivalence gives an equivalence over `ℚ_p`. -/
theorem isometricIn_padic_of_gl (p : ℕ) [Fact p.Prime] {A B : QuadForm ℤ_[p] 2} (h : IsometricGL A B) :
    (B.map PadicInt.Coe.ringHom).IsometricIn ℚ_[p] (A.map PadicInt.Coe.ringHom) := by
  obtain ⟨g, hg⟩ := (IsometricGL.symm h).hessian_eq
  refine isometricIn_of_hessian (g.val.map PadicInt.Coe.ringHom) ?_ ?_
  · have := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact this.map _
  · rw [Siegel.hessian_map, Siegel.hessian_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg]

/-- If a nondegenerate binary form over `ℚ_p` of discriminant `D` represents `u ≠ 0`, then `c = (u, D)_p`. -/
theorem hasseC_eq_of_represents (p : ℕ) [Fact p.Prime] {g : QuadForm ℚ_[p] 2} {D : ℚ_[p]} (hD : D ≠ 0)
    (hg : -g.hessian.det = D) {u : ℚ_[p]} (hu0 : u ≠ 0) (hrep : g.RepresentsIn ℚ_[p] u) :
    hasseC g = hilbertSymbol ℚ_[p] u D := by
  have hnd : g.Nondegenerate := nondeg_of_det hD hg
  obtain ⟨α, hα, hiso⟩ := QuadForm.exists_isometric_diag_cons hnd hu0 hrep
  have hiso2 : g.IsometricIn ℚ_[p] (QuadForm.diag ![u, -D / (4 * u)]) := by
    have := normal_form_of_diag hg (a := Fin.cons u α) (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hu0
      · simpa using hα j) hiso
    simpa using this
  have hK := PadicClass.localHilbertField_padic p
  rw [hasseC_eq_of_isometric p hnd (hne_diag_two hD hu0) hiso2, PadicClass.hasseVec_two,
    hs_normal_form hK.mul_left hu0 hD]

/-- A `ℤ_p`-unit from an integer prime to `p`. -/
theorem isUnit_intCast_of_not_dvd (p : ℕ) [Fact p.Prime] {n : ℤ} (h : ¬ (p : ℤ) ∣ n) : IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h' => h ?_)
  exact (PadicInt.norm_int_lt_one_iff_dvd n).mp h'

/-- A primitive form over `ℤ_p` of discriminant `D` and Hasse invariant `1` (the principal form). -/
theorem principal_exists (p : ℕ) [Fact p.Prime] {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ g : QuadForm ℤ_[p] 2, IsPrimitiveZp g ∧ -g.hessian.det = (D : ℤ_[p]) ∧
      hasseC (g.map PadicInt.Coe.ringHom) = 1 := by
  obtain ⟨F, hFa, hFd⟩ : ∃ F : BinQF, F.a = 1 ∧ F.disc = D := by
    rcases hD4 with h | h
    · exact ⟨BinQF.mk 1 0 (-(D / 4)), by simp, by simp [BinQF.disc]; omega⟩
    · exact ⟨BinQF.mk 1 1 ((1 - D) / 4), by simp, by simp [BinQF.disc]; omega⟩
  refine ⟨F.map (Int.castRingHom ℤ_[p]), Or.inl ?_, ?_, ?_⟩
  · have : (F.map (Int.castRingHom ℤ_[p])).coeff 0 0 = ((F.a : ℤ) : ℤ_[p]) := rfl
    rw [this, hFa]; simp
  · rw [neg_det_map_int, hFd]; simp
  · have hDp : (D : ℚ_[p]) ≠ 0 := by exact_mod_cast hD
    rw [Siegel.map_map_int]
    have hg : -(F.map (Int.castRingHom ℚ_[p])).hessian.det = (D : ℚ_[p]) := by
      rw [neg_det_map_int, hFd]; simp
    rw [hasseC_eq_of_represents p hDp hg one_ne_zero ?_, hilbertSymbol_comm, hilbertSymbol_one_right]
    refine ⟨![1, 0], ?_⟩
    have := eval_two (F.map (Int.castRingHom ℚ_[p])) 1 0
    simp only [mul_zero, add_zero, one_pow, mul_one] at this
    have h00 : (F.map (Int.castRingHom ℚ_[p])).coeff 0 0 = ((F.a : ℤ) : ℚ_[p]) := rfl
    show (F.map (Int.castRingHom ℚ_[p])).eval ![1, 0] = _
    rw [this, h00, hFa]; simp

/-- For `x ≠ 0` with `x < 0` and `y < 0`, `(x, y)_ℝ = -1`; otherwise `1`. Specialised: the real invariants of the
two diagonal forms used below. -/
theorem hasseC_diag_real {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hasseC (QuadForm.diag ![a, b]) = hilbertSymbol ℝ a b := by
  have hnd : (QuadForm.diag ![a, b]).Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [Binary.hessian_det_two]; simp [QuadForm.diag]; exact ⟨ha, hb⟩
  rw [hasseC_eq_of_isometric_real hnd (a := ![a, b]) ?_ (QuadForm.isometricIn_refl _ _), PadicClass.hasseVec_two]
  intro i; fin_cases i
  · simpa using ha
  · simpa using hb

/-- `(r, D)_p = -1` for odd `p`, `r` a non-residue unit and `D = p^e m` with `e` odd, `p ∤ m`. -/
theorem symbol_odd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (r : ℤ_[p]ˣ) (hr : HilbertLocal.unitChar r = -1)
    {e : ℕ} (hodd : Odd e) {m D : ℤ} (hm : ¬ (p : ℤ) ∣ m) (hDe : D = (p : ℤ) ^ e * m) :
    hilbertSymbol ℚ_[p] ((r : ℤ_[p]) : ℚ_[p]) (D : ℚ_[p]) = -1 := by
  obtain ⟨v, hv⟩ := isUnit_intCast_of_not_dvd p hm
  have h := HilbertLocal.hilbertSymbol_odd_formula hp2 0 e r v
  rw [pow_zero, one_mul] at h
  have hD' : (D : ℚ_[p]) = (p : ℚ_[p]) ^ e * ((v : ℤ_[p]) : ℚ_[p]) := by
    rw [hv, hDe]; push_cast; rfl
  rw [hD', h, hr]
  simp [hodd.neg_one_pow]

/-- `(5, D)_2 = -1` for `D = 2^e m` with `e` odd, `m` odd. -/
theorem symbol_two (u : ℤ_[2]ˣ) (hu : (u : ℤ_[2]) = ((5 : ℤ) : ℤ_[2])) {e : ℕ} (hodd : Odd e) {m D : ℤ}
    (hm : ¬ ((2 : ℕ) : ℤ) ∣ m) (hDe : D = ((2 : ℕ) : ℤ) ^ e * m) :
    hilbertSymbol ℚ_[2] ((u : ℤ_[2]) : ℚ_[2]) (D : ℚ_[2]) = -1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := isUnit_intCast_of_not_dvd 2 hm
  have h := HilbertLocal.hilbertSymbol_two_formula 0 e u v
  rw [pow_zero, one_mul] at h
  have hD' : (D : ℚ_[2]) = (2 : ℚ_[2]) ^ e * ((v : ℤ_[2]) : ℚ_[2]) := by
    rw [hv, hDe]; push_cast; rfl
  have h5 : PadicInt.toZModPow 3 (u : ℤ_[2]) = 5 := by rw [hu, map_intCast]; simp
  rw [hD', h, h5]
  have e1 : HilbertLocal.twoEps (5 : ZMod (2 ^ 3)) = 0 := by decide
  have e2 : HilbertLocal.twoOmega (5 : ZMod (2 ^ 3)) = 1 := by decide
  rw [e1, e2]
  simp [hodd.neg_one_pow]

/-- The local form with `c_p = -1`: for `D = p^e m` with `e` odd, `p ∤ m` (and `4 ∣ D` if `p = 2`) there is a primitive
`ℤ_p`-form `r x² + c y²` of discriminant `D` with Hasse invariant `-1`. -/
theorem exists_local_neg (p : ℕ) [Fact p.Prime] (D : ℤ) (hD : D ≠ 0) (e : ℕ) (m : ℤ) (hodd : Odd e)
    (hm : ¬ (p : ℤ) ∣ m) (hDe : D = (p : ℤ) ^ e * m) (h2 : p = 2 → D % 4 = 0) :
    ∃ g : QuadForm ℤ_[p] 2, IsPrimitiveZp g ∧ -g.hessian.det = (D : ℤ_[p]) ∧
      hasseC (g.map PadicInt.Coe.ringHom) = -1 := by
  have key : ∃ (r c : ℤ_[p]), IsUnit r ∧ 4 * r * c = -(D : ℤ_[p]) ∧
      hilbertSymbol ℚ_[p] (r : ℚ_[p]) (D : ℚ_[p]) = -1 := by
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨u, hu⟩ := isUnit_intCast_of_not_dvd 2 (n := 5) (by decide)
      have h4 : (D : ℤ_[2]) = 4 * ((D / 4 : ℤ) : ℤ_[2]) := by
        have : D = 4 * (D / 4) := by have := h2 rfl; omega
        conv_lhs => rw [this]
        push_cast; ring
      refine ⟨u, -((D / 4 : ℤ) : ℤ_[2]) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), u.isUnit, ?_, ?_⟩
      · rw [h4]
        have : (u : ℤ_[2]) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := u.mul_inv
        linear_combination (-4 * ((D / 4 : ℤ) : ℤ_[2])) * this
      · exact symbol_two u hu hodd (by simpa using hm) (by simpa using hDe)
    · have hp := (Fact.out : p.Prime)
      have hp2' : (p : ℤ) ≠ 2 := by exact_mod_cast hp2
      obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
      have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
      have hnd : ¬ (p : ℤ) ∣ (a.val : ℤ) := by
        intro h
        apply ha0
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a.val : ℤ) p).mpr h
        simpa using this
      obtain ⟨ur, hur⟩ := isUnit_intCast_of_not_dvd p hnd
      have hchar : HilbertLocal.unitChar ur = -1 := by
        unfold HilbertLocal.unitChar
        rw [hur, map_intCast]
        have : ((a.val : ℤ) : ZMod p) = a := by simp
        rw [this]
        exact quadraticChar_neg_one_iff_not_isSquare.mpr ha
      have hn4 : ¬ (p : ℤ) ∣ 4 := by
        intro h
        have h' : p ∣ 2 ^ 2 := by exact_mod_cast h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))
      obtain ⟨u4, hu4⟩ := isUnit_intCast_of_not_dvd p hn4
      refine ⟨ur, -(D : ℤ_[p]) * ((u4⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((ur⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ur.isUnit, ?_, ?_⟩
      · have h1 : (u4 : ℤ_[p]) * ((u4⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := u4.mul_inv
        have h3 : (ur : ℤ_[p]) * ((ur⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := ur.mul_inv
        have h4' : (4 : ℤ_[p]) = u4 := by rw [hu4]; norm_num
        rw [h4']
        linear_combination (-(D : ℤ_[p]) * ((ur : ℤ_[p]) * ((ur⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))) * h1 + (-(D : ℤ_[p])) * h3
      · exact symbol_odd p hp2 ur hchar hodd hm hDe
  obtain ⟨r, c, hr, hrc, hsym⟩ := key
  refine ⟨QuadForm.diag ![r, c], Or.inl (by simpa [QuadForm.diag] using hr), ?_, ?_⟩
  · rw [Binary.hessian_det_two]
    simp [QuadForm.diag]
    linear_combination (-1 : ℤ_[p]) * hrc
  · have hr0 : (r : ℚ_[p]) ≠ 0 := fun h => hr.ne_zero (PadicInt.coe_eq_zero.mp h)
    have hDp : (D : ℚ_[p]) ≠ 0 := by exact_mod_cast hD
    have hc : ((c : ℤ_[p]) : ℚ_[p]) = -(D : ℚ_[p]) / (4 * (r : ℚ_[p])) := by
      have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hrc
      have this' : (4 : ℚ_[p]) * (r : ℚ_[p]) * (c : ℚ_[p]) = -(D : ℚ_[p]) := by exact_mod_cast this
      field_simp
      linear_combination this'
    have hg : -(QuadForm.diag ![r, c]).hessian.det = (D : ℤ_[p]) := by
      rw [Binary.hessian_det_two]
      simp [QuadForm.diag]
      linear_combination (-1 : ℤ_[p]) * hrc
    have hgq := neg_det_map hg
    have hnd := nondeg_of_det hDp hgq
    rw [map_diag] at hnd ⊢
    have e : PadicInt.Coe.ringHom ∘ (![r, c] : Fin 2 → ℤ_[p]) = ![(r : ℚ_[p]), (c : ℚ_[p])] := by
      funext i; fin_cases i <;> rfl
    rw [e] at hnd ⊢
    rw [hasseC_eq_of_isometric p hnd (a := ![(r : ℚ_[p]), (c : ℚ_[p])]) ?_ (QuadForm.isometricIn_refl _ _),
      PadicClass.hasseVec_two, hc, hs_normal_form (PadicClass.localHilbertField_padic p).mul_left hr0 hDp, hsym]
    intro i; fin_cases i
    · simpa using hr0
    · have : (c : ℚ_[p]) ≠ 0 := by rw [hc]; exact div_ne_zero (neg_ne_zero.mpr hDp) (mul_ne_zero (by norm_num) hr0)
      simpa using this

/-- A positive non-square integer has a prime with odd exponent: `D = p^e m`, `e` odd, `p ∤ m`. -/
theorem exists_odd_exponent {D : ℤ} (hpos : 0 < D) (hsq : ¬ IsSquare D) :
    ∃ (p : ℕ), p.Prime ∧ ∃ (e : ℕ) (m : ℤ), Odd e ∧ ¬ (p : ℤ) ∣ m ∧ D = (p : ℤ) ^ e * m := by
  by_contra h
  push Not at h
  apply hsq
  rw [Int.isSquare_iff_nonneg_even_factorization]
  refine ⟨hpos.le, fun p hp => ?_⟩
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hn : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hpos.ne'
  refine h p hp _ ((D.natAbs / p ^ D.natAbs.factorization p : ℕ) : ℤ) hodd ?_ ?_
  · rw [Int.natCast_dvd_natCast]
    exact Nat.not_dvd_ordCompl hp hn
  · have := Nat.ordProj_mul_ordCompl_eq_self D.natAbs p
    have h2 : (D.natAbs : ℤ) = D := Int.natAbs_of_nonneg hpos.le
    rw [← h2]
    exact_mod_cast this.symm

/-- **The product formula for a global form** (Cassels, Ch. 14, proof of the Corollary to Theorem 5.1, p. 344: "we know
that (5.4) is necessary"): for a binary form $F$ over $\mathbb Z$ of discriminant $D \ne 0$,
$\prod_{p \le \infty} c_p(F) = 1$ (Hilbert's product formula, Cassels, Ch. 3, Thm. 2.1). -/
theorem prod_hasse_eq_one_of_global {D : ℤ} (hD : D ≠ 0) (F : BinQF) (hF : F.disc = D) :
    (∏ᶠ p : Nat.Primes, hasseAt (fun q _ => (F.map (Int.castRingHom ℤ_[q])).map PadicInt.Coe.ringHom) p) *
      hasseC (F.map (Int.castRingHom ℝ)) = 1 := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hG : -(F.map (Int.castRingHom ℚ)).hessian.det = (D : ℚ) := by
    rw [neg_det_map_int, hF]; simp
  refine prod_hasse_of_rat_iso hDq (F.map (Int.castRingHom ℚ)) hG
    (fun q _ => (F.map (Int.castRingHom ℤ_[q])).map PadicInt.Coe.ringHom) ?_ _ ?_ ?_ ?_
  · intro p _
    refine nondeg_of_det (D := (D : ℚ_[p])) (by exact_mod_cast hD) ?_
    rw [Siegel.map_map_int, neg_det_map_int, hF]; simp
  · refine nondeg_of_det (D := (D : ℝ)) (by exact_mod_cast hD) ?_
    rw [neg_det_map_int, hF]; simp
  · intro p _
    rw [map_padic_eq]
    exact QuadForm.isometricIn_refl _ _
  · rw [map_real_eq]
    exact QuadForm.isometricIn_refl _ _

/-- **Cassels, Ch. 14, Theorem 5.1** (p. 343), in the form of the proof of its Corollary (p. 344): *a family of
primitive integral $p$-adic forms $f_p$ of discriminant $D$ ($p \le \infty$) is the family of localizations of a
global form if and only if $\prod_{p \le \infty} c_p(f_p) = 1$.* Here $D \ne 0$, $f_p$ (`f p`) is a primitive form over
$\mathbb Z_p$ for each prime $p$, $f_\infty$ (`fInf`) a form over $\mathbb R$, and "the localizations of $F$" means
$F \cong f_p$ over $\mathbb Z_p$ for every $p$ and $F \cong f_\infty$ over $\mathbb R$. The image of
$\mathcal G \to \prod_p \mathcal G_p$ is thus the kernel of $\prod_p c_p$, which is everything when $D$ is a square
(`prod_hasse_eq_one_of_isSquare`) and of index $2$ otherwise (`exists_prod_hasse_eq_neg_one`). -/
@[kb "cassels1978" "Ch. 14, Thm. 5.1, p. 343; proof of the Cor., p. 344 (the image is cut out by ∏ c_p = 1)"]
theorem thm_5_1 {D : ℤ} (hD : D ≠ 0) (f : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] 2)
    (hprim : ∀ (p : ℕ) [Fact p.Prime], IsPrimitiveZp (f p))
    (hf : ∀ (p : ℕ) [Fact p.Prime], -(f p).hessian.det = (D : ℤ_[p])) (fInf : QuadForm ℝ 2)
    (hfInf : -fInf.hessian.det = (D : ℝ)) :
    (∃ F : BinQF, F.IsPrimitive ∧ F.disc = D ∧
      (∀ (p : ℕ) [Fact p.Prime], IsometricGL (F.map (Int.castRingHom ℤ_[p])) (f p)) ∧
      IsometricGL (F.map (Int.castRingHom ℝ)) fInf) ↔
    (∏ᶠ p : Nat.Primes, hasseAt (fun q _ => (f q).map PadicInt.Coe.ringHom) p) * hasseC fInf = 1 := by
  constructor
  · rintro ⟨F, -, hFd, hF, hFInf⟩
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    have hG : -(F.map (Int.castRingHom ℚ)).hessian.det = (D : ℚ) := by
      rw [neg_det_map_int, hFd]; simp
    refine prod_hasse_of_rat_iso hDq (F.map (Int.castRingHom ℚ)) hG
      (fun q _ => (f q).map PadicInt.Coe.ringHom) ?_ fInf ?_ ?_ ?_
    · intro p _
      exact nondeg_of_det (D := (D : ℚ_[p])) (by exact_mod_cast hD) (neg_det_map (hf p))
    · exact nondeg_of_det (D := (D : ℝ)) (by exact_mod_cast hD) hfInf
    · intro p _
      rw [← map_padic_eq]
      exact isometricIn_padic_of_gl p (hF p)
    · rw [← map_real_eq]
      exact (isometricGL_iff_isometricIn _ _).mp (hFInf.symm)
  · intro h
    exact exists_int_form_of_local hD f hprim hf fInf hfInf h

/-- **Cassels, Ch. 14, Theorem 5.1, the square case** (p. 343): *if $D$ is a perfect square the image is the entire
group*: a nondegenerate binary form over a field $K$ of characteristic $0$ whose discriminant is a non-zero square has
Hasse–Minkowski invariant $1$ (it is a hyperbolic plane), so every family of local forms of discriminant $D = k^2$
satisfies $\prod_p c_p = 1$ and comes from a global form by `thm_5_1`. -/
@[kb "cassels1978" "Ch. 14, Thm. 5.1, p. 343 (D a perfect square: the image is the entire group)"]
theorem hasseC_eq_one_of_isSquare {K : Type*} [Field K] [CharZero K] (g : QuadForm K 2) {k : K} (hk : k ≠ 0)
    (hg : -g.hessian.det = k ^ 2) : hasseC g = 1 := by
  classical
  have hnd : g.Nondegenerate := nondeg_of_det (pow_ne_zero 2 hk) hg
  have hex := FieldGen.exists_isometric_diag g hnd
  unfold hasseC
  simp only [hnd, ↓reduceDIte]
  obtain ⟨hb0, P, hP, hPe⟩ := Classical.choose_spec hex
  set a := Classical.choose hex with ha
  have hdet := congrArg Matrix.det (PadicClass.transpose_mul_hessian_mul hPe)
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hdiag : (QuadForm.diag a).hessian.det = 4 * a 0 * a 1 := by
    rw [Binary.hessian_det_two]; simp [QuadForm.diag]
  rw [hdiag] at hdet
  have hgd : g.hessian.det = -k ^ 2 := by linear_combination -hg
  rw [hgd] at hdet
  have hd : P.det ≠ 0 := hP.ne_zero
  have h0 := hb0 0
  have h1 := hb0 1
  have key : a 1 = (P.det * k / (2 * a 0)) ^ 2 * (-a 0) := by
    field_simp
    linear_combination (-1 : K) * hdet
  rw [PadicClass.eq_vec_two a, PadicClass.hasseVec_two, key,
    PadicClass.hs_sq_right _ _ _ (div_ne_zero (mul_ne_zero hd hk) (mul_ne_zero two_ne_zero h0)),
    hilbertSymbol_self_neg]

/-- **Cassels, Ch. 14, Theorem 5.1, the square case, for families** (p. 343): if $D = k^2$, every family of primitive
local forms of discriminant $D$ comes from a primitive integral form of discriminant $D$. -/
@[kb "cassels1978" "Ch. 14, Thm. 5.1, p. 343 (D a perfect square: the image is the entire group)"]
theorem prod_hasse_eq_one_of_isSquare {k : ℤ} (hk : k ≠ 0) (f : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] 2)
    (hprim : ∀ (p : ℕ) [Fact p.Prime], IsPrimitiveZp (f p))
    (hf : ∀ (p : ℕ) [Fact p.Prime], -(f p).hessian.det = ((k ^ 2 : ℤ) : ℤ_[p])) (fInf : QuadForm ℝ 2)
    (hfInf : -fInf.hessian.det = ((k ^ 2 : ℤ) : ℝ)) :
    ∃ F : BinQF, F.IsPrimitive ∧ F.disc = k ^ 2 ∧
      (∀ (p : ℕ) [Fact p.Prime], IsometricGL (F.map (Int.castRingHom ℤ_[p])) (f p)) ∧
      IsometricGL (F.map (Int.castRingHom ℝ)) fInf := by
  have h1 : ∀ p : Nat.Primes, hasseAt (fun q _ => (f q).map PadicInt.Coe.ringHom) p = 1 := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    show hasseC ((f p).map PadicInt.Coe.ringHom) = 1
    refine hasseC_eq_one_of_isSquare _ (k := (k : ℚ_[p])) (by exact_mod_cast hk) ?_
    have := neg_det_map (hf p)
    simpa using this
  have h2 : hasseC fInf = 1 :=
    hasseC_eq_one_of_isSquare _ (k := (k : ℝ)) (by exact_mod_cast hk) (by simpa using hfInf)
  exact (thm_5_1 (pow_ne_zero 2 hk) f hprim hf fInf hfInf).mpr (by rw [finprod_eq_one_of_forall_eq_one h1, h2]; norm_num)

/-- **Cassels, Ch. 14, Theorem 5.1, the non-square case** (p. 343): *if $D$ is not a perfect square the image has
index $2$*: for $D \ne 0$, $D \equiv 0, 1 \pmod 4$ not a square there is a family of primitive local forms of
discriminant $D$ with $\prod_{p \le \infty} c_p(f_p) = -1$, which by `thm_5_1` does not come from a global form (so
$\prod_p c_p$ is a surjective character onto $\{\pm 1\}$ and the image is its kernel). -/
@[kb "cassels1978" "Ch. 14, Thm. 5.1, p. 343 (D not a square: the image has index 2)"]
theorem exists_prod_hasse_eq_neg_one {D : ℤ} (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) (hsq : ¬ IsSquare D) :
    ∃ (f : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] 2) (fInf : QuadForm ℝ 2),
      (∀ (p : ℕ) [Fact p.Prime], IsPrimitiveZp (f p)) ∧
      (∀ (p : ℕ) [Fact p.Prime], -(f p).hessian.det = (D : ℤ_[p])) ∧ -fInf.hessian.det = (D : ℝ) ∧
      (∏ᶠ p : Nat.Primes, hasseAt (fun q _ => (f q).map PadicInt.Coe.ringHom) p) * hasseC fInf = -1 := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · have hprin : ∀ (p : ℕ) [Fact p.Prime], ∃ g : QuadForm ℤ_[p] 2, IsPrimitiveZp g ∧
        -g.hessian.det = (D : ℤ_[p]) ∧ hasseC (g.map PadicInt.Coe.ringHom) = 1 :=
      fun p _ => principal_exists p hD hD4
    choose f hf1 hf2 hf3 using hprin
    have hDneg : (D : ℝ) < 0 := by exact_mod_cast hneg
    refine ⟨f, QuadForm.diag ![-1, (D : ℝ) / 4], hf1, hf2, ?_, ?_⟩
    · rw [Binary.hessian_det_two]; simp [QuadForm.diag]; ring
    · have h1 : ∀ p : Nat.Primes, hasseAt (fun q _ => (f q).map PadicInt.Coe.ringHom) p = 1 := by
        intro p
        have : Fact (p : ℕ).Prime := ⟨p.2⟩
        exact hf3 p
      have hq : (D : ℝ) / 4 ≠ 0 := div_ne_zero hDr (by norm_num)
      rw [finprod_eq_one_of_forall_eq_one h1, hasseC_diag_real (by norm_num) hq]
      have := (hilbertSymbol_real (-1) ((D : ℝ) / 4) (by norm_num) hq).mpr ⟨by norm_num, by linarith⟩
      rw [this]; norm_num
  · obtain ⟨p0, hp0, e, m, hodd, hm, hDe⟩ := exists_odd_exponent hpos hsq
    have h2 : p0 = 2 → D % 4 = 0 := by
      intro h
      subst h
      have he : e ≠ 0 := by rintro rfl; simp at hodd
      have : (2 : ℤ) ∣ D := by
        rw [hDe]; exact Dvd.dvd.mul_right (dvd_pow (by norm_num) he) _
      omega
    have hall : ∀ (p : ℕ) [Fact p.Prime], ∃ g : QuadForm ℤ_[p] 2, IsPrimitiveZp g ∧
        -g.hessian.det = (D : ℤ_[p]) ∧ hasseC (g.map PadicInt.Coe.ringHom) = if p = p0 then -1 else 1 := by
      intro p _
      by_cases hp : p = p0
      · subst hp
        obtain ⟨g, a, b, c⟩ := exists_local_neg p D hD e m hodd hm hDe h2
        exact ⟨g, a, b, by rw [if_pos rfl]; exact c⟩
      · obtain ⟨g, a, b, c⟩ := principal_exists p hD hD4
        exact ⟨g, a, b, by rw [if_neg hp]; exact c⟩
    choose f hf1 hf2 hf3 using hall
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hpos
    refine ⟨f, QuadForm.diag ![1, -(D : ℝ) / 4], hf1, hf2, ?_, ?_⟩
    · rw [Binary.hessian_det_two]; simp [QuadForm.diag]; ring
    · have hq : -(D : ℝ) / 4 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hDr) (by norm_num)
      rw [hasseC_diag_real one_ne_zero hq, hilbertSymbol_comm, hilbertSymbol_one_right, mul_one]
      rw [finprod_eq_single (fun p : Nat.Primes => hasseAt (fun q _ => (f q).map PadicInt.Coe.ringHom) p)
        (⟨p0, hp0⟩ : Nat.Primes) ?_]
      · have : Fact p0.Prime := ⟨hp0⟩
        show hasseC ((f p0).map PadicInt.Coe.ringHom) = -1
        rw [hf3 p0, if_pos rfl]
      · intro q hq'
        have : Fact (q : ℕ).Prime := ⟨q.2⟩
        show hasseC ((f q).map PadicInt.Coe.ringHom) = 1
        rw [hf3 q, if_neg]
        intro h
        exact hq' (Subtype.ext h)

end QuadFormsKB.Composition
