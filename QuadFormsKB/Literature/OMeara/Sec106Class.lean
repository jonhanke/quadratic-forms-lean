/-
# O'Meara §106B, §106D–F: adjacency chains and the unimodular lattices of rank at most 9

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^n$ with $Q = x_0^2 + \dots + x_{n-1}^2$ (`sumSqForm n`, O'Meara's $V = I_n$), lattices
`Lat ℚ n` (finitely generated $\mathbb Z$-submodules spanning $V$), O'Meara's $B = \tfrac12$ `bil Q`, unimodular lattices
`IsUnimodularZ`, the set $\mathcal G(L)$ = `omearaG`, adjacency = `Nbr.IsNbrL Q 2` (Kneser's $2$-neighbours, equivalent to
O'Meara's invariant factors $\tfrac12\mathbb Z, \mathbb Z, \dots, \mathbb Z, 2\mathbb Z$), $D = \mathbb Z^n$ = `intVec`, the lattice
$E$ = `omearaE n` of §106E.

**Defines**
* `OMeara106_2` (named statement, Proposition 106:2, p. 325): for $n \ge 5$ every proper unimodular class meets
  $\mathcal G(L)$. O'Meara's proof uses Theorem 104:10 over $\mathbb Z[\tfrac12]$ (strong approximation with the
  exceptional spot $2$). It is proved in `Sec106Two.lean` (`omeara106_2_holds`, by strong approximation away from
  $2$); the conditional statements below are made unconditional in `Sec106Rank9.lean`.
* `OMeara106_3` (named statement, Proposition 106:3, p. 326): for $8 \mid n$ every unimodular lattice has even and odd
  unimodular neighbours. O'Meara's proof uses the dyadic classification (93:18); proved in `Sec106Three.lean`.

**Proves**
* Proposition 106:4 (`omeara106_4`), unconditionally and by a different proof (see its docstring): a chain of
  unimodular lattices from $L$ to any $K \in \mathcal G(L)$, $K \ne L$, by strong induction on $[L : L \cap K]$, for an
  arbitrary quadratic form $Q$ over $\mathbb Q$ (O'Meara: $V = I_n$, $n \ge 2$).
* Proposition 106:10 (p. 330), a unimodular lattice on $V = I_n$ has matrix $I_n$ (is isometric to $D = \mathbb Z^n$):
  `omeara106_10_of_le_five` for $1 \le n \le 5$, unconditionally, by a different proof (Hermite's bound, via
  `Siegel.Hermite.unimodular_posDef_equiv_one`); `omeara106_10` for $1 \le n \le 7$, conditional on `OMeara106_2` and
  following O'Meara (106:2, 106:4 and 106:9 with the vector $w = \tfrac12(\pm x_{i_1} \pm \dots \pm x_{i_4})$).
-/
import QuadFormsKB.Literature.OMeara.Sec106Adj
import QuadFormsKB.Siegel.FourSquaresClassNumber

open Matrix NumberField IsDedekindDomain QuadFormsKB.HilbertModular

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### Named statements -/

/-- **Proposition 106:2 — named statement** (O'Meara 1973, §106B, p. 325). Let $n \ge 5$ and let $K, L$ be unimodular
lattices on $V = I_n$ over $\mathbb Q$. Then there is a lattice $J \in \operatorname{cls}^+K$ with $J \in \mathcal G(L)$,
i.e. $J_p = L_p$ at every odd prime $p$.

O'Meara's proof passes to the ring $\mathbb Z' = \mathbb Z[\tfrac12]$, where $V$ is indefinite at the spot $2$ ($n \ge 5$), and
applies Theorem 104:10 (class = genus for modular lattices of the same norm). It is the only
input of the classification theorems below, and it is PROVED in `Sec106Two.lean` (`omeara106_2_holds`, by strong
approximation away from the spot $2$ instead of 104:10); `Sec106Rank9.lean` records `omeara106_2 : OMeara106_2`. -/
@[kb "omeara1963" "§106B, 106:2, p. 325"]
structure OMeara106_2 : Prop where
  /-- Every proper class of unimodular lattices on $I_n$ ($n \ge 5$) meets $\mathcal G(L)$. -/
  holds : ∀ (n : ℕ), 5 ≤ n → ∀ K L : Lat ℚ n, IsUnimodularZ (sumSqForm n) K.1 → IsUnimodularZ (sumSqForm n) L.1 →
    ∃ J : Lat ℚ n, IsProperIsometric (sumSqForm n) K.1 J.1 ∧ J ∈ omearaG (sumSqForm n) L

/-- **Proposition 106:3 — named statement** (O'Meara 1973, §106B, p. 326). Let $n \equiv 0 \bmod 8$ ($n \ge 8$, $V$ is
non-zero) and let $L$ be a unimodular lattice on $V = I_n$. Then there are an even and an odd unimodular lattice on $V$
adjacent to $L$.

O'Meara's proof: $V_2$ is an orthogonal sum of hyperbolic planes, the local classification (Example 93:18) gives the
shape of $L_2$, a suitable local lattice $K_2$ is chosen and glued with $L_p$ ($p$ odd) by 81:14. It is not used below
(Proposition 106:4 is proved without it). PROVED in `Sec106Three.lean` (`omeara106_3_holds`, through 93:29 at $2$ and
explicit global neighbours instead of 93:18). -/
@[kb "omeara1963" "§106B, 106:3, p. 326"]
structure OMeara106_3 : Prop where
  /-- Even and odd unimodular neighbours exist when $8 \mid n$. -/
  holds : ∀ (n : ℕ), 0 < n → 8 ∣ n → ∀ L : Lat ℚ n, IsUnimodularZ (sumSqForm n) L.1 →
    (∃ K : Lat ℚ n, IsUnimodularZ (sumSqForm n) K.1 ∧ IsEvenLat (sumSqForm n) K.1 ∧
      Nbr.IsNbrL (sumSqForm n) 2 L.1 K.1) ∧
    (∃ K : Lat ℚ n, IsUnimodularZ (sumSqForm n) K.1 ∧ ¬ IsEvenLat (sumSqForm n) K.1 ∧
      Nbr.IsNbrL (sumSqForm n) 2 L.1 K.1)

variable {n : ℕ} (Q : QuadForm ℚ n)

/-! ### Helpers for 106:4 -/

private lemma cls_int_of (c : 𝓞 ℚ) : ∃ k : ℤ, ((k : ℤ) : 𝓞 ℚ) = c :=
  ⟨Rat.ringOfIntegersEquiv c, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
    (Rat.ringOfIntegersEquiv.symm_apply_apply c)⟩

private lemma cls_nm_two : nm (2 : 𝓞 ℚ) = 2 := by
  have h : (2 : 𝓞 ℚ) = ((2 : ℕ) : 𝓞 ℚ) := by norm_num
  rw [h, nm_natCast, NumberField.RingOfIntegers.rank]
  simp

/-- The index $[B : A \cap B]$ (Mathlib's `relIndex A B`) of submodules, as a natural number. -/
private def cls_ri (A B : Submodule (𝓞 ℚ) (Fin n → ℚ)) : ℕ :=
  A.toAddSubgroup.relIndex B.toAddSubgroup

private lemma cls_ri_mul {A B C : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h1 : A ≤ B) (h2 : B ≤ C) :
    cls_ri A B * cls_ri B C = cls_ri A C :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ (fun _ hx => h1 hx) (fun _ hx => h2 hx)

private lemma cls_ri_two {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : Nbr.IsNbrL Q 2 L K) :
    cls_ri (L ⊓ K) L = 2 := by
  have h1 := h.index_left
  rw [cls_nm_two] at h1
  have e : (L ⊓ K).toAddSubgroup = L.toAddSubgroup ⊓ K.toAddSubgroup := rfl
  unfold cls_ri
  rw [e, AddSubgroup.inf_relIndex_left, h1]

/-- For two lattices $L, K$ the index $[L : L \cap K]$ is finite: some $c \ne 0$ has $cL \subseteq K$, and
$L / cL$ is finite. -/
private lemma cls_ri_ne_zero {L K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ)
    (hK : K.IsLattice ℚ) : cls_ri (L ⊓ K) L ≠ 0 := by
  classical
  obtain ⟨dL, hdL0, -, hdL2⟩ := exists_global_bounds hL
  obtain ⟨dK, hdK0, hdK1, -⟩ := exists_global_bounds hK
  have hc0 : dK * dL ≠ 0 := mul_ne_zero hdK0 hdL0
  have hcK : ∀ x ∈ L, (dK * dL) • x ∈ K := fun x hx => by
    rw [mul_smul]; exact hdK1 _ (hdL2 x hx)
  have hfg : Module.Finite (𝓞 ℚ) L := Module.Finite.of_fg hL.fg
  set I : Ideal (𝓞 ℚ) := Ideal.span {dK * dL} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact hc0
  have hRI : Finite (𝓞 ℚ ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  have htop : Finite (↥L ⧸ (⊤ : Submodule (𝓞 ℚ) L)) := inferInstance
  have hfin : Finite (↥L ⧸ I • (⊤ : Submodule (𝓞 ℚ) L)) :=
    Submodule.finite_quotient_smul I (Module.Finite.fg_top)
  set N' : Submodule (𝓞 ℚ) L := (L ⊓ K).comap L.subtype with hN'
  have hle : I • (⊤ : Submodule (𝓞 ℚ) L) ≤ N' := by
    rw [Submodule.smul_le]
    intro r hr x _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    show ((a * (dK * dL)) • x : L).1 ∈ L ⊓ K
    rw [mul_smul]
    refine (L ⊓ K).smul_mem a ?_
    exact Submodule.mem_inf.mpr ⟨L.smul_mem _ x.2, hcK x x.2⟩
  have hfin' : Finite (↥L ⧸ N') :=
    Finite.of_surjective (Submodule.mapQ (I • (⊤ : Submodule (𝓞 ℚ) L)) N' LinearMap.id hle)
      (fun q => Quotient.inductionOn' q fun x => ⟨Submodule.Quotient.mk x, rfl⟩)
  have hfin'' : Finite (↥L.toAddSubgroup ⧸ (L ⊓ K).toAddSubgroup.addSubgroupOf L.toAddSubgroup) :=
    hfin'
  exact AddSubgroup.index_ne_zero_of_finite

private lemma cls_dual_anti {M N : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : M ≤ N) :
    omearaDual Q N ≤ omearaDual Q M :=
  fun _ hx y hy => hx y (h hy)

private lemma cls_uni_mem {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : IsUnimodularZ Q L) {x y : Fin n → ℚ}
    (hx : x ∈ L) (hy : y ∈ L) : ∃ m : ℤ, bil Q x y / 2 = m := by
  have : x ∈ omearaDual Q L := by rw [hL]; exact hx
  exact this y hy

private lemma cls_uni_eq {M N : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : IsUnimodularZ Q M)
    (hN : IsUnimodularZ Q N) (h : M ≤ N) : M = N := by
  refine le_antisymm h ?_
  have := cls_dual_anti Q h
  rw [hM, hN] at this
  exact this

private lemma cls_bil_add_r (x y y' : Fin n → ℚ) : bil Q x (y + y') = bil Q x y + bil Q x y' := by
  simp [bil, Matrix.mulVec_add, dotProduct_add]

private lemma cls_bil_smul_r (c : ℚ) (x y : Fin n → ℚ) : bil Q x (c • y) = c * bil Q x y := by
  simp [bil, Matrix.mulVec_smul, dotProduct_smul]

private lemma cls_smul_int (c : 𝓞 ℚ) (y : Fin n → ℚ) : ∃ k : ℤ, c • y = (k : ℚ) • y := by
  obtain ⟨k, hk⟩ := cls_int_of c
  subst hk
  refine ⟨k, ?_⟩
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

private lemma cls_eval_of_bil {x : Fin n → ℚ} {m : ℤ} (h : bil Q x x / 2 = m) : Q.eval x = m := by
  have := bil_self Q x
  linarith

private lemma cls_two_smul_eq (y : Fin n → ℚ) : (2 : 𝓞 ℚ) • y = (2 : ℚ) • y := by
  rw [← algebraMap_smul ℚ (2 : 𝓞 ℚ) y]
  have e : algebraMap (𝓞 ℚ) ℚ 2 = 2 := map_ofNat _ 2
  rw [e]

/-- At a place `v` where `m` is a unit, `m x ∈ M` gives `x ∈ M_v`. -/
private lemma cls_unit_loc {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
    {m : 𝓞 F} (hm : m ∉ v.asIdeal)
    {M : Submodule (𝓞 F) (Fin n → F)} {x : Fin n → F} (h : m • x ∈ M) : locVec v x ∈ loc v M := by
  have h1 : locVec v (m • x) ∈ loc v M := locVec_mem_loc v h
  have hv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) m) = 1 := by
    rw [valued_algebraMap_int v m]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hm
  have hne : algebraMap (𝓞 F) (v.adicCompletion F) m ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have ht : Valued.v ((algebraMap (𝓞 F) (v.adicCompletion F) m)⁻¹) ≤ 1 := by
    rw [map_inv₀, hv]; simp
  have e : locVec v x = (toO v _ ht) • locVec v (m • x) := by
    funext i
    rw [locVec_smul_int]
    change locVec v x i = ((toO v _ ht : v.adicCompletionIntegers F) : v.adicCompletion F) *
      (((algebraMap (𝓞 F) (v.adicCompletionIntegers F) m : v.adicCompletionIntegers F) :
        v.adicCompletion F) * locVec v x i)
    rw [← mul_assoc, algebraMap_int_coe]
    change locVec v x i = (algebraMap (𝓞 F) (v.adicCompletion F) m)⁻¹ *
      (algebraMap (𝓞 F) (v.adicCompletion F) m) * locVec v x i
    rw [inv_mul_cancel₀ hne, one_mul]
  rw [e]
  exact (loc v M).smul_mem _ h1

/-- Adjacent lattices have the same localization at every odd place. -/
private lemma cls_nbr_loc {A B : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : Nbr.IsNbrL Q 2 A B)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) : loc v A = loc v B := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 := h.smul_right x hx
    rw [algebraMap_smul] at h1
    exact cls_unit_loc v hv h1
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 := h.smul_left x hx
    rw [algebraMap_smul] at h1
    exact cls_unit_loc v hv h1

private lemma cls_lattice_of_nbr {J L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (h : Nbr.IsNbrL Q 2 J L)
    (hL : L.IsLattice ℚ) : J.IsLattice ℚ := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hL
  refine isLattice_of_global_bounds (d := 2 * d) (mul_ne_zero two_ne_zero hd) (fun x hx => ?_) (fun x hx => ?_)
  · have := h.smul_left _ (h1 x hx)
    rw [algebraMap_smul] at this
    rwa [mul_smul]
  · have := h.smul_right x hx
    rw [algebraMap_smul] at this
    rw [mul_comm, mul_smul]
    exact h2 _ this

/-- If $K_v = L_v$ at all odd places, $x \in K$ and $m x \in L$ for an odd $m$, then $x \in L$. -/
private lemma cls_mem_of_odd {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ)
    (hKL : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ v.asIdeal → loc v K = loc v L)
    {x : Fin n → ℚ} (hx : x ∈ K) {m : ℕ} (hm : Odd m) (h : m • x ∈ L) : x ∈ L := by
  rw [mem_iff_forall_loc hL]
  intro v
  by_cases hmv : (m : 𝓞 ℚ) ∈ v.asIdeal
  · have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h2 => by
      obtain ⟨k, hk⟩ := hm
      have e : (1 : 𝓞 ℚ) = (m : 𝓞 ℚ) - 2 * (k : 𝓞 ℚ) := by rw [hk]; push_cast; ring
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
        (e ▸ v.asIdeal.sub_mem hmv (Ideal.mul_mem_right _ _ h2)))
    rw [← hKL v h2]
    exact locVec_mem_loc v hx
  · refine cls_unit_loc v hmv ?_
    rwa [Nat.cast_smul_eq_nsmul]

/-- A vector $y \in K - L$ with $2y \in L$, from any $x \in K - L$ (when $K_p = L_p$ at odd $p$). -/
private lemma cls_exists_half {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ)
    (hKL : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ v.asIdeal → loc v K = loc v L)
    {x : Fin n → ℚ} (hx : x ∈ K) (hxL : x ∉ L) :
    ∃ y ∈ K, y ∉ L ∧ (2 : ℚ) • y ∈ L := by
  obtain ⟨d, hd, h1, -⟩ := exists_global_bounds hL
  obtain ⟨c, hc, hcx⟩ := exists_smul_mem_intVec x
  have hdc : (d * c) • x ∈ L := by rw [mul_smul]; exact h1 _ hcx
  obtain ⟨k, hk⟩ := cls_int_of (d * c)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hd hc (by rw [← hk]; simp)
  have hkx : k • x ∈ L := by
    rw [← Int.cast_smul_eq_zsmul (𝓞 ℚ), hk]; exact hdc
  have hN : k.natAbs • x ∈ L := by
    rcases Int.natAbs_eq k with h | h
    · rw [h, natCast_zsmul] at hkx; exact hkx
    · rw [h, neg_smul, natCast_zsmul] at hkx
      simpa using L.neg_mem hkx
  have hN0 : k.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hk0
  obtain ⟨a, m, hm, hNe⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  have hP : ∃ a : ℕ, (2 ^ a) • x ∈ L := by
    refine ⟨a, cls_mem_of_odd hL hKL (K.nsmul_mem hx _) hm ?_⟩
    rw [smul_smul, mul_comm, ← hNe]; exact hN
  classical
  set a0 := Nat.find hP with ha0
  have hP0 : (2 ^ a0) • x ∈ L := Nat.find_spec hP
  have ha0pos : a0 ≠ 0 := by
    intro h0
    rw [h0] at hP0
    simp at hP0
    exact hxL hP0
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero ha0pos
  have hmin : ¬ (2 ^ b) • x ∈ L := Nat.find_min hP (by omega)
  refine ⟨(2 ^ b) • x, K.nsmul_mem hx _, hmin, ?_⟩
  have : (2 : ℚ) • ((2 ^ b) • x) = (2 ^ a0) • x := by
    rw [hb, pow_succ, mul_comm, mul_smul, ← Nat.cast_smul_eq_nsmul ℚ 2]
    simp
  rw [this]
  exact hP0

/-- One step of the chain: from `L` towards `K ∈ 𝒢(L)`, `K ≠ L`, to a unimodular `J` adjacent to `L`
with `K ∈ 𝒢(J)` and strictly smaller index. -/
private lemma cls_step (L K : Lat ℚ n) (hL : IsUnimodularZ Q L.1) (hKG : K ∈ omearaG Q L) (hne : K ≠ L) :
    ∃ J : Lat ℚ n, IsUnimodularZ Q J.1 ∧ Nbr.IsNbrL Q 2 L.1 J.1 ∧ K ∈ omearaG Q J ∧
      cls_ri (J.1 ⊓ K.1) J.1 < cls_ri (L.1 ⊓ K.1) L.1 := by
  obtain ⟨hKu, hKloc⟩ := hKG
  have hnle : ¬ K.1 ≤ L.1 := fun h => hne (Lat.ext (cls_uni_eq Q hKu hL h))
  obtain ⟨x, hxK, hxL⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  obtain ⟨y, hyK, hyL, h2y⟩ := cls_exists_half L.2 hKloc hxK hxL
  have hQy : ∃ m : ℤ, Q.eval y = m := by
    obtain ⟨m, hm⟩ := cls_uni_mem Q hKu hyK hyK
    exact ⟨m, cls_eval_of_bil Q hm⟩
  obtain ⟨hJu, hyJ, hJadj, -⟩ := omeara106_7 Q hL h2y hyL hQy
  set J0 := Submodule.span (𝓞 ℚ) {y} ⊔ omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ L.1) with hJ0
  have hJL : Nbr.IsNbrL Q 2 L.1 J0 := hJadj.symm
  refine ⟨⟨J0, cls_lattice_of_nbr Q hJadj L.2⟩, hJu, hJL, ⟨hKu, fun v hv => ?_⟩, ?_⟩
  · rw [hKloc v hv]
    exact (cls_nbr_loc Q hJadj v hv).symm
  · have hMN : ∀ x ∈ L.1 ⊓ K.1, x ∈ omearaDual Q (Submodule.span (𝓞 ℚ) {y} ⊔ L.1) := by
      intro x hx z hz
      obtain ⟨hxL, hxK⟩ := Submodule.mem_inf.mp hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      obtain ⟨k, hk⟩ := cls_smul_int c y
      obtain ⟨m1, hm1⟩ := cls_uni_mem Q hKu hxK hyK
      obtain ⟨m2, hm2⟩ := cls_uni_mem Q hL hxL hb
      refine ⟨k * m1 + m2, ?_⟩
      rw [hk, cls_bil_add_r, cls_bil_smul_r, add_div, mul_div_assoc, hm1, hm2]
      push_cast
      ring
    have hMJ : L.1 ⊓ K.1 ≤ J0 := fun x hx => Submodule.mem_sup_right (hMN x hx)
    have hMN' : L.1 ⊓ K.1 ≤ L.1 ⊓ J0 := le_inf inf_le_left hMJ
    have e1 := cls_ri_mul hMN' (inf_le_left : L.1 ⊓ J0 ≤ L.1)
    have e2 := cls_ri_mul hMN' (inf_le_right : L.1 ⊓ J0 ≤ J0)
    have r1 : cls_ri (L.1 ⊓ J0) L.1 = 2 := cls_ri_two Q hJL
    have r2 : cls_ri (L.1 ⊓ J0) J0 = 2 := by
      have := cls_ri_two Q hJadj
      rwa [inf_comm] at this
    have hJK : L.1 ⊓ K.1 ≤ J0 ⊓ K.1 := le_inf hMJ inf_le_right
    have e3 := cls_ri_mul hJK (inf_le_left : J0 ⊓ K.1 ≤ J0)
    have hne0 : cls_ri (L.1 ⊓ K.1) L.1 ≠ 0 := cls_ri_ne_zero L.2 K.2
    have hy1 : cls_ri (L.1 ⊓ K.1) (J0 ⊓ K.1) ≠ 1 := by
      intro h1
      have h3 := AddSubgroup.relIndex_eq_one.mp h1
      have hy : y ∈ (J0 ⊓ K.1).toAddSubgroup := Submodule.mem_inf.mpr ⟨hyJ, hyK⟩
      exact hyL (Submodule.mem_inf.mp (h3 hy)).1
    show cls_ri (J0 ⊓ K.1) J0 < cls_ri (L.1 ⊓ K.1) L.1
    rw [r1] at e1
    rw [r2] at e2
    have ha0 : cls_ri (L.1 ⊓ K.1) (J0 ⊓ K.1) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at e3
      omega
    have ha2 : 2 ≤ cls_ri (L.1 ⊓ K.1) (J0 ⊓ K.1) := by omega
    have hb0 : cls_ri (J0 ⊓ K.1) J0 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e3
      omega
    have hb1 : 1 ≤ cls_ri (J0 ⊓ K.1) J0 := Nat.one_le_iff_ne_zero.mpr hb0
    nlinarith

private lemma cls_chain (m : ℕ) : ∀ (L K : Lat ℚ n), IsUnimodularZ Q L.1 → K ∈ omearaG Q L → K ≠ L →
    cls_ri (L.1 ⊓ K.1) L.1 = m →
    Relation.TransGen (fun A B => IsUnimodularZ Q A ∧ IsUnimodularZ Q B ∧ Nbr.IsNbrL Q 2 A B) L.1 K.1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro L K hL hKG hne hm
    obtain ⟨J, hJu, hJadj, hKJ, hlt⟩ := cls_step Q L K hL hKG hne
    by_cases hJK : J = K
    · subst hJK
      exact Relation.TransGen.single ⟨hL, hJu, hJadj⟩
    · have := ih _ (hm ▸ hlt) J K hJu hKJ (Ne.symm hJK) rfl
      exact Relation.TransGen.head ⟨hL, hJu, hJadj⟩ this

/-- **Proposition 106:4** (O'Meara 1973, §106B, p. 326). Let $Q$ be a quadratic form over $\mathbb Q$ on $\mathbb Q^n$,
let $L$ be a unimodular lattice (`hL : IsUnimodularZ Q L.1`), and let $K \in \mathcal G(L)$ (`hK : K ∈ omearaG Q L`: $K$
unimodular with $K_p = L_p$ at every odd prime $p$), $K \ne L$ (`hne`). Then there is a chain of unimodular lattices
$L = J_0, J_1, \dots, J_t = K$ ($t \ge 1$), each adjacent (`Nbr.IsNbrL Q 2`, Kneser's $2$-neighbour) to the previous one;
stated as `Relation.TransGen` of "both unimodular and adjacent" from `L.1` to `K.1`.

*Deviations from the book.* (i) Generalization: the book takes $V = I_n$ with $n \ge 2$ (the space of §106); here $Q$ is
an arbitrary quadratic form over $\mathbb Q$ on $\mathbb Q^n$, $n \ge 0$ (a lattice is finitely generated and spans, with
$\mathcal G(L)$ as in `omearaG`). (ii) *A different proof.* O'Meara reduces to the local statement at $2$, using the odd
lattice case (106:3) and the dyadic classification (93:29). Here the proof is elementary and global: strong induction on
the index $[L : L \cap K]$ (finite, both being lattices). Since $K \not\le L$ (else $L = L^\# \le K^\# = K$), the odd
spots give a vector $y \in K - L$ with $2y \in L$ (if $x \in K - L$, then $m x \in L$ with $m$ odd forces $x \in L$,
because $K_p = L_p$ for odd $p$; take $y = 2^{a-1}x$ for the least $a$ with $2^ax \in L$). As $Q(y) \in \mathbb Z$, 106:7 gives
a unimodular $J = \mathbb Zy + (\mathbb Zy + L)^\#$ adjacent to $L$ and containing $y$; $K \in \mathcal G(J)$; and
$[J : J \cap K] < [L : L \cap K]$ by multiplicativity of indices ($[J : M] = [L : M]$ for $M = L \cap K$ and
$[J \cap K : M] \ge 2$ since $y \in (J \cap K) - M$). -/
@[kb "omeara1963" "§106B, 106:4, p. 326"]
theorem omeara106_4 {L K : Lat ℚ n} (hL : IsUnimodularZ Q L.1) (hK : K ∈ omearaG Q L) (hne : K ≠ L) :
    Relation.TransGen (fun A B => IsUnimodularZ Q A ∧ IsUnimodularZ Q B ∧ Nbr.IsNbrL Q 2 A B) L.1 K.1 :=
  cls_chain Q _ L K hL hK hne rfl

/-! ### 106:10 for $n \le 5$ by Hermite's bound -/

private lemma cls_sumSq_eval (x : Fin n → ℚ) : (sumSqForm n).eval x = ∑ i, x i ^ 2 := by
  rw [sumSqForm, QuadForm.eval, QuadForm.evalIn_diag]; simp

private lemma cls_sumSq_hess : (sumSqForm n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
  · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]

private lemma cls_sumSq_bil (x y : Fin n → ℚ) :
    bil (sumSqForm n) x y = 2 * ∑ i, x i * y i := by
  rw [bil, cls_sumSq_hess, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, dotProduct, smul_eq_mul]

private lemma cls_mem_range {q : ℚ} : q ∈ (algebraMap (𝓞 ℚ) ℚ).range ↔ ∃ m : ℤ, q = m := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨m, rfl⟩ := cls_int_of a
    exact ⟨m, by simp⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(m : 𝓞 ℚ), by simp⟩

private lemma cls_D_coord {x : Fin n → ℚ} :
    x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ ∀ i, ∃ m : ℤ, x i = m := by
  rw [mem_intVec]
  exact forall_congr' fun i => cls_mem_range

/-- A lattice has a $\mathbb Z$-basis, given as the columns of an invertible rational matrix `P`:
$L = \{P z : z \in \mathbb Z^n\}$. -/
private lemma cls_exists_matrix {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hL : L.IsLattice ℚ) :
    ∃ P : Matrix (Fin n) (Fin n) ℚ, IsUnit P ∧
      (∀ c : Fin n → ℤ, P *ᵥ (fun i => (c i : ℚ)) ∈ L) ∧
      (∀ x ∈ L, ∃ c : Fin n → ℤ, x = P *ᵥ (fun i => (c i : ℚ))) := by
  have := hL
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom
      Rat.ringOfIntegersEquiv.symm.surjective
  have hrank : Module.finrank (𝓞 ℚ) L = n := by
    simpa using Submodule.IsLattice.finrank_of_pi ℚ L
  let b0 : Module.Basis (Fin n) (𝓞 ℚ) L := Module.finBasisOfFinrankEq (𝓞 ℚ) L hrank
  let bq : Module.Basis (Fin n) ℚ (Fin n → ℚ) := b0.extendOfIsLattice ℚ
  have hbq : ∀ i, bq i = (b0 i : Fin n → ℚ) := fun i => Module.Basis.extendOfIsLattice_apply ℚ b0 i
  let P : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun r c => (b0 c : Fin n → ℚ) r
  have hmv : ∀ c : Fin n → ℚ, P *ᵥ c = ∑ i, c i • (b0 i : Fin n → ℚ) := by
    intro c
    funext r
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    refine ⟨fun i => bq.repr v i, ?_⟩
    rw [hmv]
    have := bq.sum_repr v
    simpa [hbq] using this
  · intro c
    rw [hmv]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : ((c i : ℤ) : ℚ) • (b0 i : Fin n → ℚ) = (c i : 𝓞 ℚ) • (b0 i : Fin n → ℚ) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    rw [this]
    exact L.smul_mem _ (b0 i).2
  · intro x hx
    have h := b0.sum_repr ⟨x, hx⟩
    have hx' : x = ∑ i, (b0.repr ⟨x, hx⟩ i) • (b0 i : Fin n → ℚ) := by
      have := congrArg Subtype.val h
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
      exact this.symm
    choose k hk using fun i => cls_int_of (b0.repr ⟨x, hx⟩ i)
    refine ⟨k, ?_⟩
    rw [hmv]
    conv_lhs => rw [hx']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hk i, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

private lemma cls_castMulVec (M : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℤ) :
    M.map (Int.castRingHom ℚ) *ᵥ (fun i => (c i : ℚ)) = fun i => (((M *ᵥ c) i : ℤ) : ℚ) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- **Proposition 106:10 for $1 \le n \le 5$** (O'Meara 1973, §106D, p. 330), unconditional. Let $n$ be a natural number
with $1 \le n \le 5$ (`h1`, `h5`; the hypothesis `h1` is not needed by the proof, the statement is trivial for $n = 0$)
and let $L$ be a unimodular lattice on $V = I_n$ over $\mathbb Q$ (`hL : IsUnimodularZ (sumSqForm n) L.1`). Then $L$ has
matrix $I_n$, i.e. $L$ is isometric to $D = \mathbb Z^n$ (`IsIsometric (sumSqForm n) intVec L.1`): there is
$\gamma \in O(V)(\mathbb Q)$ with $\gamma\mathbb Z^n = L$, equivalently $L$ has an orthonormal $\mathbb Z$-basis.

*A different proof from the book.* O'Meara derives this from 106:2 and 106:4 (the conditional `omeara106_10`, which covers
$n \le 7$). Here, for $n \le 5$, the proof is by Hermite's bound, with no hypothesis: a $\mathbb Z$-basis of $L$ has Gram
matrix $G = (B(b_i, b_j)) \in M_n(\mathbb Z)$, positive definite with $\det G = 1$ ($\det G = \pm1$ because the dual of $L$
is $L$, and $\det G = (\det P)^2 > 0$ for the matrix $P$ of the basis), so
`Siegel.Hermite.unimodular_posDef_equiv_one` gives $g \in \mathrm{GL}_n(\mathbb Z)$ with $g^{\mathsf T}Gg = I$; the columns
of $Pg$ are an orthonormal basis of $L$. -/
@[kb "omeara1963" "§106D, 106:10, p. 330 (n ≤ 5, by Hermite's bound)"]
theorem omeara106_10_of_le_five (_h1 : 1 ≤ n) (h5 : n ≤ 5) {L : Lat ℚ n}
    (hL : IsUnimodularZ (sumSqForm n) L.1) :
    IsIsometric (sumSqForm n) intVec L.1 := by
  obtain ⟨P, hPu, hP1, hP2⟩ := cls_exists_matrix L.2
  have hPinj : Function.Injective (fun c : Fin n → ℚ => P *ᵥ c) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hPu
  have hcol : ∀ i, (fun r => P r i) ∈ L.1 := by
    intro i
    have := hP1 (Pi.single i 1)
    convert this using 1
    funext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hGint : ∀ i j, ∃ m : ℤ, (Pᵀ * P) i j = m := by
    intro i j
    obtain ⟨m, hm⟩ := cls_uni_mem (sumSqForm n) hL (hcol i) (hcol j)
    rw [cls_sumSq_bil] at hm
    exact ⟨m, by simp only [Matrix.mul_apply, Matrix.transpose_apply]; linarith⟩
  choose G hG using hGint
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  let Gm : Matrix (Fin n) (Fin n) ℤ := Matrix.of G
  have hGq : Gm.map φ = Pᵀ * P := by
    ext i j
    simp [Gm, hG i j]
  have hGsymm : Gm.IsSymm := by
    apply Matrix.map_injective (f := φ) (RingHom.injective_int φ)
    show Gmᵀ.map φ = Gm.map φ
    rw [Matrix.transpose_map, hGq, transpose_mul, transpose_transpose]
  have hpd : Siegel.Hermite.IsPosDefInt Gm := by
    refine ⟨hGsymm, fun x hx => ?_⟩
    set xq : Fin n → ℚ := fun i => (x i : ℚ) with hxq
    have hcast : ((x ⬝ᵥ (Gm *ᵥ x) : ℤ) : ℚ) = (P *ᵥ xq) ⬝ᵥ (P *ᵥ xq) := by
      have e1 : Gm.map φ *ᵥ xq = fun i => (((Gm *ᵥ x) i : ℤ) : ℚ) := cls_castMulVec Gm x
      calc ((x ⬝ᵥ (Gm *ᵥ x) : ℤ) : ℚ) = xq ⬝ᵥ (Gm.map φ *ᵥ xq) := by
            rw [e1]; simp [dotProduct, xq]
        _ = xq ⬝ᵥ (Pᵀ *ᵥ (P *ᵥ xq)) := by rw [hGq, ← mulVec_mulVec]
        _ = (P *ᵥ xq) ⬝ᵥ (P *ᵥ xq) := by rw [dotProduct_mulVec, vecMul_transpose]
    have hne : P *ᵥ xq ≠ 0 := by
      intro h
      apply hx
      have := hPinj (h.trans (mulVec_zero P).symm)
      funext i
      have := congrFun this i
      simpa [xq] using this
    have hpos : 0 < (P *ᵥ xq) ⬝ᵥ (P *ᵥ xq) :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
        (Ne.symm fun h => hne (dotProduct_self_eq_zero.mp h))
    have : (0 : ℚ) < ((x ⬝ᵥ (Gm *ᵥ x) : ℤ) : ℚ) := by rw [hcast]; exact hpos
    exact_mod_cast this
  have hdetP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hdetG : (Pᵀ * P).det = P.det ^ 2 := by rw [det_mul, det_transpose, sq]
  have hGu : IsUnit (Pᵀ * P).det := by rw [hdetG]; exact hdetP.pow 2
  have hGsymmQ : (Pᵀ * P)ᵀ = Pᵀ * P := by rw [transpose_mul, transpose_transpose]
  have hGi : ∀ j, ∃ d : Fin n → ℤ, ∀ i, (Pᵀ * P)⁻¹ i j = (d i : ℚ) := by
    intro j
    set c : Fin n → ℚ := fun r => (Pᵀ * P)⁻¹ r j with hc
    have hcv : c = (Pᵀ * P)⁻¹ *ᵥ (Pi.single j 1) := by
      funext r; simp [hc, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hGc : (Pᵀ * P) *ᵥ c = Pi.single j 1 := by
      rw [hcv, mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, one_mulVec]
    have hvL : P *ᵥ c ∈ L.1 := by
      have : P *ᵥ c ∈ omearaDual (sumSqForm n) L.1 := by
        intro w hw
        obtain ⟨a, rfl⟩ := hP2 w hw
        set aq : Fin n → ℚ := fun i => (a i : ℚ) with haq
        refine ⟨a j, ?_⟩
        rw [cls_sumSq_bil]
        have e1 : ∑ i, (P *ᵥ c) i * (P *ᵥ aq) i = (P *ᵥ c) ⬝ᵥ (P *ᵥ aq) := rfl
        rw [e1]
        have e2 : (P *ᵥ c) ⬝ᵥ (P *ᵥ aq) = c ⬝ᵥ ((Pᵀ * P) *ᵥ aq) := by
          rw [dotProduct_comm (P *ᵥ c), dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
            mulVec_mulVec]
        have e3 : c ᵥ* (Pᵀ * P) = (Pᵀ * P) *ᵥ c := by rw [← vecMul_transpose, hGsymmQ]
        have hfin : (P *ᵥ c) ⬝ᵥ (P *ᵥ aq) = (a j : ℚ) := by
          rw [e2, dotProduct_mulVec, e3, hGc, single_dotProduct]
          simp [haq]
        rw [hfin]
        ring
      rwa [hL] at this
    obtain ⟨d, hd⟩ := hP2 _ hvL
    refine ⟨d, fun i => ?_⟩
    have := hPinj hd
    have := congrFun this i
    simpa [hc] using this
  choose d hd using hGi
  let N : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => d j i
  have hNq : N.map φ = (Pᵀ * P)⁻¹ := by
    ext i j
    simp [N, hd j i]
  have hGN : Gm * N = 1 := by
    apply Matrix.map_injective (f := φ) (RingHom.injective_int φ)
    show (Gm * N).map φ = (1 : Matrix (Fin n) (Fin n) ℤ).map φ
    rw [Matrix.map_mul, hNq, hGq, Matrix.map_one φ (by simp) (by simp)]
    exact Matrix.mul_nonsing_inv _ hGu
  have hdet1 : Gm.det = 1 := by
    have h := congrArg Matrix.det hGN
    rw [det_mul, det_one] at h
    have hnn : (0 : ℚ) ≤ (Gm.det : ℚ) := by
      have := RingHom.map_det φ Gm
      have e : φ.mapMatrix Gm = Pᵀ * P := hGq
      rw [e, hdetG] at this
      have h2 : (Gm.det : ℚ) = P.det ^ 2 := by simpa [φ] using this
      rw [h2]
      exact sq_nonneg _
    have hnn' : 0 ≤ Gm.det := by exact_mod_cast hnn
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h with h1 | h1
    · exact h1
    · omega
  obtain ⟨g, hg⟩ := Siegel.Hermite.unimodular_posDef_equiv_one n h5 Gm hpd hdet1
  let gq : Matrix (Fin n) (Fin n) ℚ := g.val.map φ
  have hgqu : IsUnit gq := g.isUnit.map φ.mapMatrix
  have hγu : IsUnit (P * gq) := hPu.mul hgqu
  let γ : GL (Fin n) ℚ := Matrix.nonsingInvUnit (P * gq) ((Matrix.isUnit_iff_isUnit_det _).mp hγu)
  have hγv : γ.val = P * gq := rfl
  have hortho : (P * gq)ᵀ * (P * gq) = 1 := by
    have e : (g.val)ᵀ * Gm * g.val = 1 := hg
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M.map φ) e
    simp only [Matrix.map_mul, Matrix.transpose_map, hGq, Matrix.map_one φ (by simp) (by simp)] at this
    calc (P * gq)ᵀ * (P * gq) = gqᵀ * (Pᵀ * P) * gq := by simp [transpose_mul, Matrix.mul_assoc]
      _ = 1 := this
  refine ⟨γ, ?_, ?_⟩
  · rw [mem_orthGroup, hγv, cls_sumSq_hess]
    have hm : ((2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℚ) = (2 : ℚ) • 1 := by
      ext i j
      simp [Matrix.one_apply]
    rw [hm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hortho]
  · ext x
    rw [mem_glImage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      choose m hm using cls_D_coord.mp hy
      have hy' : y = fun i => (m i : ℚ) := funext hm
      rw [hγv, ← mulVec_mulVec, hy']
      have := cls_castMulVec g.val m
      change P *ᵥ (g.val.map φ *ᵥ (fun i => (m i : ℚ))) ∈ _
      rw [this]
      exact hP1 _
    · intro hx
      obtain ⟨c, rfl⟩ := hP2 x hx
      refine ⟨fun i => ((((g⁻¹ : GL (Fin n) ℤ).val *ᵥ c) i : ℤ) : ℚ),
        cls_D_coord.mpr fun i => ⟨_, rfl⟩, ?_⟩
      rw [hγv, ← mulVec_mulVec]
      have h1 := cls_castMulVec g.val ((g⁻¹ : GL (Fin n) ℤ).val *ᵥ c)
      have e : g.val *ᵥ ((g⁻¹ : GL (Fin n) ℤ).val *ᵥ c) = c := by
        rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      change P *ᵥ (g.val.map φ *ᵥ _) = _
      rw [h1, e]

/-! ### 106:10 for $n \le 7$ -/

private lemma cls_bil_orth {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup Q ℚ) (x y : Fin n → ℚ) :
    bil Q (γ.val *ᵥ x) (γ.val *ᵥ y) = bil Q x y := by
  have h := (mem_orthGroup Q).mp hγ
  have hm : Q.hessian.map (algebraMap ℚ ℚ) = Q.hessian := by ext i j; simp
  rw [hm] at h
  have key : bil Q (γ.val *ᵥ x) (γ.val *ᵥ y) = x ⬝ᵥ ((γ.valᵀ * Q.hessian * γ.val) *ᵥ y) := by
    rw [bil, dotProduct_comm (γ.val *ᵥ x), dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
      mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  rw [key, h]
  rfl

/-- Isometries preserve unimodularity. -/
private lemma cls_unimod_glImage {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup Q ℚ)
    {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : IsUnimodularZ Q M) : IsUnimodularZ Q (glImage γ M) := by
  have hγi : γ⁻¹ ∈ orthGroup Q ℚ := (orthGroup Q ℚ).inv_mem hγ
  have h1 : ∀ x, γ.val *ᵥ ((γ⁻¹).val *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have h2 : ∀ x, (γ⁻¹).val *ᵥ (γ.val *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  unfold IsUnimodularZ
  apply le_antisymm
  · intro x hx
    have hx' : (γ⁻¹).val *ᵥ x ∈ omearaDual Q M := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (γ.val *ᵥ y) (mulVec_mem_glImage hy)
      refine ⟨m, ?_⟩
      have := cls_bil_orth Q hγi x (γ.val *ᵥ y)
      rw [h2] at this
      rw [this]
      exact hm
    rw [hM] at hx'
    exact mem_glImage.mpr ⟨_, hx', h1 x⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_glImage.mp hx
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_glImage.mp hz
    have hy' : y ∈ omearaDual Q M := by rw [hM]; exact hy
    obtain ⟨m, hm⟩ := hy' w hw
    exact ⟨m, by rw [cls_bil_orth Q hγ]; exact hm⟩

private lemma cls_sq_mod (a : ℤ) : a ^ 2 % 4 = if Odd a then 1 else 0 := by
  rcases Int.even_or_odd' a with ⟨k, rfl | rfl⟩
  · have ho : ¬ Odd (2 * k) := by rw [Int.odd_iff]; omega
    simp only [ho, ↓reduceIte]
    rw [show (2 * k) ^ 2 = 4 * k ^ 2 by ring]
    exact Int.mul_emod_right 4 _
  · have ho : Odd (2 * k + 1) := ⟨k, rfl⟩
    simp only [ho, ↓reduceIte]
    rw [show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring]
    omega

/-- If $\sum a_i^2 \equiv 0 \bmod 4$, some $a_i$ is odd and $n \le 7$, then exactly four $a_i$ are odd. -/
private lemma cls_four_odd (hn : n ≤ 7) (a : Fin n → ℤ) (h4 : (4 : ℤ) ∣ ∑ i, a i ^ 2)
    (hodd : ∃ i, Odd (a i)) : (Finset.univ.filter fun i => Odd (a i)).card = 4 := by
  classical
  set S := Finset.univ.filter fun i => Odd (a i) with hS
  have hmod : (∑ i, a i ^ 2) % 4 = (S.card : ℤ) % 4 := by
    rw [Finset.sum_int_mod]
    have : ∀ i ∈ (Finset.univ : Finset (Fin n)), a i ^ 2 % 4 = if Odd (a i) then 1 else 0 :=
      fun i _ => cls_sq_mod (a i)
    rw [Finset.sum_congr rfl this, Finset.sum_boole]
  have hpos : 1 ≤ S.card := Finset.card_pos.mpr (by
    obtain ⟨i, hi⟩ := hodd
    exact ⟨i, by simp [hS, hi]⟩)
  have hle : S.card ≤ 7 := (Finset.card_le_univ S).trans (by simpa using hn)
  obtain ⟨c, hc⟩ := h4
  omega

/-- Signs $\varepsilon_i = \pm1$ with $\sum_{i \in S} \varepsilon_i a_i \equiv 2 \bmod 4$, for four odd $a_i$. -/
private lemma cls_signs (a : Fin n → ℤ) (S : Finset (Fin n)) (hS : ∀ i ∈ S, Odd (a i))
    (hc : S.card = 4) :
    ∃ ε : Fin n → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∑ i ∈ S, ε i * a i) % 4 = 2 := by
  classical
  obtain ⟨i0, hi0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hpar : (∑ i ∈ S, a i) % 2 = 0 := by
    rw [Finset.sum_int_mod]
    have : ∀ i ∈ S, a i % 2 = 1 := fun i hi => Int.odd_iff.mp (hS i hi)
    rw [Finset.sum_congr rfl this]
    simp [hc]
  by_cases h2 : (∑ i ∈ S, a i) % 4 = 2
  · exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simpa using h2⟩
  · refine ⟨fun i => if i = i0 then -1 else 1, fun i => by by_cases h : i = i0 <;> simp [h], ?_⟩
    have e : ∀ i, (if i = i0 then (-1 : ℤ) else 1) * a i = a i - 2 * (if i = i0 then a i else 0) := by
      intro i
      by_cases h : i = i0
      · subst h
        simp
        ring
      · simp [h]
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' S i0 a]
    obtain ⟨k, hk⟩ := hS i0 hi0
    simp only [hi0, ↓reduceIte]
    omega

/-- **Key lemma of 106:10** (O'Meara 1973, p. 330): for $n \le 7$ every unimodular lattice $A$ adjacent to $D = \mathbb Z^n$
is isometric to $D$. Proof as in the book: for $y \in A - D$ one has $2y = (a_i) \in \mathbb Z^n$ with $\sum a_i^2 \equiv 0
\bmod 4$ ($Q(y) \in \mathbb Z$), so exactly four $a_i$ are odd; with signs chosen as in `cls_signs`,
$w = \tfrac12\sum_{a_i \text{ odd}}\varepsilon_ix_i$ has $Q(w) = 1$, $y - w \in D$ and $B(y, w) \in \tfrac12 + \mathbb Z$, and
106:9 gives $\tau_wA = D$. -/
private lemma cls_key (hn : n ≤ 7) {A : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hA : IsUnimodularZ (sumSqForm n) A) (hadj : Nbr.IsNbrL (sumSqForm n) 2 A intVec) :
    IsIsometric (sumSqForm n) intVec A := by
  classical
  obtain ⟨y, hyA, hyD⟩ : ∃ y ∈ A, y ∉ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ intVec := fun x hx => hcon x hx
    have h1 := cls_ri_two (sumSqForm n) hadj
    rw [inf_eq_left.mpr hle] at h1
    simp [cls_ri] at h1
  have h2y : (2 : ℚ) • y ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
    have := hadj.smul_right y hyA
    rwa [algebraMap_smul, cls_two_smul_eq] at this
  choose a ha using fun i => cls_D_coord.mp h2y i
  have hy : ∀ i, y i = (a i : ℚ) / 2 := fun i => by
    have := ha i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    linarith
  obtain ⟨m, hm⟩ := cls_uni_mem _ hA hyA hyA
  rw [cls_sumSq_bil] at hm
  have hsumQ : (∑ i, (a i : ℚ) ^ 2) = 4 * m := by
    have h0 : ∑ i, y i * y i = m := by linarith
    calc (∑ i, (a i : ℚ) ^ 2) = ∑ i, 4 * (y i * y i) :=
          Finset.sum_congr rfl fun i _ => by rw [hy i]; ring
      _ = 4 * m := by rw [← Finset.mul_sum, h0]
  have hsumZ : ∑ i, a i ^ 2 = 4 * m := by exact_mod_cast hsumQ
  have hodd : ∃ i, Odd (a i) := by
    by_contra hcon
    push Not at hcon
    apply hyD
    refine cls_D_coord.mpr fun i => ?_
    obtain ⟨r, hr⟩ := Int.not_odd_iff_even.mp (hcon i)
    exact ⟨r, by rw [hy i, hr]; push_cast; ring⟩
  have hcard := cls_four_odd hn a ⟨m, hsumZ⟩ hodd
  set S := Finset.univ.filter fun i => Odd (a i) with hS
  have hSodd : ∀ i, i ∈ S ↔ Odd (a i) := fun i => by simp [hS]
  obtain ⟨ε, hε, hεs⟩ := cls_signs a S (fun i hi => (hSodd i).mp hi) hcard
  set w : Fin n → ℚ := fun i => if i ∈ S then (ε i : ℚ) / 2 else 0 with hw
  have hwQ : (sumSqForm n).eval w = 1 := by
    rw [cls_sumSq_eval]
    have : ∀ i, w i ^ 2 = if i ∈ S then (1 / 4 : ℚ) else 0 := by
      intro i
      by_cases h : i ∈ S
      · rcases hε i with h1 | h1 <;> simp [hw, h, h1] <;> norm_num
      · simp [hw, h]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hcard]
    norm_num
  have hz : y - w ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
    refine cls_D_coord.mpr fun i => ?_
    by_cases hi : i ∈ S
    · obtain ⟨k, hk⟩ := (hSodd i).mp hi
      rcases hε i with h1 | h1
      · exact ⟨k, by simp [hw, hi, hy i, hk, h1]; ring⟩
      · exact ⟨k + 1, by simp [hw, hi, hy i, hk, h1]; ring⟩
    · obtain ⟨r, hr⟩ := Int.not_odd_iff_even.mp (fun h => hi ((hSodd i).mpr h))
      exact ⟨r, by simp [hw, hi, hy i, hr]⟩
  have hB : ∃ m : ℤ, bil (sumSqForm n) y w / 2 = m + 1 / 2 := by
    have hterm : ∀ i, y i * w i = if i ∈ S then ((ε i * a i : ℤ) : ℚ) / 4 else 0 := by
      intro i
      by_cases h : i ∈ S
      · simp [hw, h, hy i]; ring
      · simp [hw, h]
    have hs : ∑ i, y i * w i = ((∑ i ∈ S, ε i * a i : ℤ) : ℚ) / 4 := by
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_mem, Finset.univ_inter]
      push_cast
      rw [Finset.sum_div]
    refine ⟨(∑ i ∈ S, ε i * a i) / 4, ?_⟩
    rw [cls_sumSq_bil, mul_div_cancel_left₀ _ (two_ne_zero), hs]
    have e : (∑ i ∈ S, ε i * a i) = 4 * ((∑ i ∈ S, ε i * a i) / 4) + 2 := by omega
    have e' : ((∑ i ∈ S, ε i * a i : ℤ) : ℚ) = 4 * (((∑ i ∈ S, ε i * a i) / 4 : ℤ) : ℚ) + 2 := by
      exact_mod_cast e
    rw [e']
    ring
  obtain ⟨-, hiso⟩ := omeara106_9 (sumSqForm n) adj_D_unimodular hA hadj hyA hyD
    (show y = w + (y - w) by abel) hwQ hz hB
  exact hiso.symm

/-- Transport of the key lemma along an isometry: if $X = \sigma D$ and the unimodular $Y$ is adjacent to $X$, then
$\sigma^{-1}Y$ is a unimodular lattice adjacent to $D$, hence isometric to $D$. -/
private lemma cls_step_iso (hn : n ≤ 7) {X Y : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hX : IsIsometric (sumSqForm n) intVec X) (hY : IsUnimodularZ (sumSqForm n) Y)
    (hadj : Nbr.IsNbrL (sumSqForm n) 2 X Y) : IsIsometric (sumSqForm n) intVec Y := by
  obtain ⟨σ, hσ, hσX⟩ := hX
  have hσi : σ⁻¹ ∈ orthGroup (sumSqForm n) ℚ := (orthGroup _ ℚ).inv_mem hσ
  have hX' : glImage (σ⁻¹ : GL (Fin n) ℚ) X = intVec := by
    rw [← hσX, ← glImage_mul, inv_mul_cancel, glImage_one]
  have hadj' : Nbr.IsNbrL (sumSqForm n) 2 (glImage (σ⁻¹ : GL (Fin n) ℚ) Y) intVec := by
    have := (hadj.symm).glImage hσi
    rwa [hX'] at this
  have hY' : IsUnimodularZ (sumSqForm n) (glImage (σ⁻¹ : GL (Fin n) ℚ) Y) :=
    cls_unimod_glImage _ hσi hY
  have hiso := cls_key hn hY' hadj'
  refine IsIsometric.trans _ hiso ⟨σ, hσ, ?_⟩
  rw [← glImage_mul, mul_inv_cancel, glImage_one]

/-- **Proposition 106:10** (O'Meara 1973, §106D, p. 330), conditional on Proposition 106:2. Assume `h2 : OMeara106_2` and
let $1 \le n \le 7$ (`h1`, `h7`) and let $L$ be a unimodular lattice on $V = I_n$ over $\mathbb Q$
(`hL : IsUnimodularZ (sumSqForm n) L.1`). Then $L$ has matrix $I_n$, i.e. $L$ is isometric to $D = \mathbb Z^n$
(`IsIsometric (sumSqForm n) intVec L.1`).

*Proof* (O'Meara's, for $n \in \{6, 7\}$; for $n \le 5$ the unconditional `omeara106_10_of_le_five` is used). By 106:2 (with
$K := L$, $L := D$) there is $J \in \operatorname{cls}^+L$ with $J \in \mathcal G(D)$. If $J = D$ we are done; otherwise
106:4 gives a chain $D = J_0, \dots, J_t = J$ of unimodular lattices, each adjacent to the previous one, and by induction
along the chain each $J_i$ is isometric to $D$, using the key step: a unimodular lattice adjacent to $D$ ($n \le 7$) is
isometric to $D$ (106:9 with the vector $w = \tfrac12(\pm x_{i_1} \pm \dots \pm x_{i_4})$, as in the book; the case $r = 4$
of the book's "exactly $r$ odd coefficients" uses $n \le 7$). Deviation: the book first reduces every $n \le 7$ to $n = 7$
by adjoining a lattice with matrix $I_{7-n}$ (Theorem 105:1); here the argument is run directly for $n \in \{6, 7\}$, so
that $105:1$ is not used. -/
@[kb "omeara1963" "§106D, 106:10, p. 330"]
theorem omeara106_10 (h2 : OMeara106_2) (h1 : 1 ≤ n) (h7 : n ≤ 7) {L : Lat ℚ n}
    (hL : IsUnimodularZ (sumSqForm n) L.1) : IsIsometric (sumSqForm n) intVec L.1 := by
  by_cases h5 : n ≤ 5
  · exact omeara106_10_of_le_five h1 h5 hL
  · let D : Lat ℚ n := ⟨intVec, intVec_isLattice⟩
    obtain ⟨J, hJp, hJG⟩ := h2.holds n (by omega) L D hL adj_D_unimodular
    have hJD : IsIsometric (sumSqForm n) intVec J.1 := by
      by_cases hJ : J = D
      · rw [hJ]
        exact IsIsometric.refl _ _
      · have hchain := omeara106_4 (sumSqForm n) (L := D) adj_D_unimodular hJG hJ
        have hall : ∀ Z, Relation.TransGen (fun A B => IsUnimodularZ (sumSqForm n) A ∧
            IsUnimodularZ (sumSqForm n) B ∧ Nbr.IsNbrL (sumSqForm n) 2 A B) D.1 Z →
            IsIsometric (sumSqForm n) intVec Z := by
          intro Z hZ
          induction hZ with
          | single hR =>
            obtain ⟨-, hZu, hadj⟩ := hR
            exact cls_key h7 hZu hadj.symm
          | tail _ hR ih =>
            obtain ⟨-, hZu, hadj⟩ := hR
            exact cls_step_iso h7 ih hZu hadj
        exact hall _ hchain
    exact IsIsometric.trans _ hJD hJp.symm.isIsometric

end QuadFormsKB.Lattices
