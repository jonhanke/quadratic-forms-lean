/-
# $\mathbb Z$-maximal lattices for the sum of nine squares contain a copy of $\mathbb Z^9$

Proof of `SumSqMaxContainsIntVec 9`. A $\mathbb Z$-maximal lattice $M$ on $V = \mathbb Q^9$ contains a unimodular
lattice (`exists_unimodular_le`), which is isometric to $\mathbb Z^9$ or to $E_8 \perp \mathbb Z$ (O'Meara 106:13,
`unimodular_rank9`). In the second case move $M$ so that it contains $E = E_8 \perp \mathbb Z$ (`omearaEZ 9`, the last
coordinate $x_8$ being the $\mathbb Z$ part). Then:

1. $M \ne E$, since $E + \mathbb Z e_0$ has integral norm;
2. a vector $u \in M \setminus E$ has $2u \in E^\# = E$, and its last coordinate is an integer (a parity argument), so
   $a = u - u_8 e_8 \in M \setminus E$ has $a_8 = 0$;
3. adding a vector of $E_8 \perp 0$ we may take $\varphi[a]$ odd;
4. the $2$-neighbour $J = \mathbb Za + (\mathbb Za + E)^\#$ of $E$ (O'Meara 106:7) is unimodular, lies in $M$, and
   contains $e_8$ and $a$; it is not isometric to $E_8 \perp \mathbb Z$, because there the orthogonal complement of a
   vector of norm $1$ is even, while $a \perp e_8$ has odd norm. So $J \cong \mathbb Z^9$.

Indices are 0-based; $e_i$ is the $i$-th unit vector.
-/
import QuadFormsKB.Literature.Shimura2004.SumSquaresNine

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices

namespace NineE8

/-- $E = E_8 \perp \mathbb Z$ in $\mathbb Q^9$. -/
abbrev EZ : Submodule (𝓞 ℚ) (Fin 9 → ℚ) := omearaEZ 9

/-- The last unit vector $e_8$. -/
abbrev e8 : Fin 9 → ℚ := Pi.single 8 1

/-- The first unit vector $e_0$. -/
abbrev e0 : Fin 9 → ℚ := Pi.single 0 1

theorem EZ_unimodular : IsUnimodularZ (sumSqForm 9) EZ := omearaEZ_unimodular (by norm_num)

theorem EZ_isLattice : EZ.IsLattice ℚ := omearaEZ_isLattice (by norm_num)

theorem dot_self (x : Fin 9 → ℚ) : x ⬝ᵥ x = ∑ i, x i ^ 2 := by
  simp [dotProduct, sq]

theorem sum_sq_add (x y : Fin 9 → ℚ) : ∑ i, (x + y) i ^ 2 = ∑ i, x i ^ 2 + 2 * (x ⬝ᵥ y) + ∑ i, y i ^ 2 := by
  simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, dotProduct, Finset.mul_sum]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Dot products on $E$ are integers. -/
theorem dot_int {x y : Fin 9 → ℚ} (hx : x ∈ EZ) (hy : y ∈ EZ) : IsIntQ (x ⬝ᵥ y) := by
  obtain ⟨m, hm⟩ := uni_mem' (sumSqForm 9) EZ_unimodular hx hy
  refine ⟨m, ?_⟩
  rw [two_sumSq_bil_dot] at hm
  linarith

theorem mem_omearaDual_iff {L : Submodule (𝓞 ℚ) (Fin 9 → ℚ)} {x : Fin 9 → ℚ} :
    x ∈ omearaDual (sumSqForm 9) L ↔ ∀ y ∈ L, IsIntQ (x ⬝ᵥ y) := by
  constructor
  · intro h y hy
    obtain ⟨m, hm⟩ := h y hy
    rw [two_sumSq_bil_dot] at hm
    exact ⟨m, by linarith⟩
  · intro h y hy
    obtain ⟨m, hm⟩ := h y hy
    exact ⟨m, by rw [two_sumSq_bil_dot]; linarith⟩

theorem omearaDual_anti {A B : Submodule (𝓞 ℚ) (Fin 9 → ℚ)} (h : A ≤ B) :
    omearaDual (sumSqForm 9) B ≤ omearaDual (sumSqForm 9) A :=
  fun _ hx y hy => hx y (h hy)

theorem head_apply (x : Fin 9 → ℚ) (j : Fin 8) : omearaEZHead 9 x j = x (Fin.castSucc j) := by
  simp only [omearaEZHead, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos (by omega)]
  rfl

theorem sum_split (f : Fin 9 → ℚ) : ∑ i, f i = ∑ j : Fin 8, f (Fin.castSucc j) + f 8 :=
  Fin.sum_univ_castSucc f

/-- On $E$, $\sum_{i < 8} x_i^2$ is an even integer. -/
theorem head_even {x : Fin 9 → ℚ} (hx : x ∈ EZ) : ∃ m : ℤ, ∑ j : Fin 8, x (Fin.castSucc j) ^ 2 = 2 * m := by
  obtain ⟨m, hm⟩ := omearaE_even (by norm_num : 8 ∣ 8) le_rfl _ ((mem_omearaEZ.mp hx).1)
  refine ⟨m, ?_⟩
  rw [show (sumSqForm 8) = sosQ 8 from rfl, sosQ_eval_eq] at hm
  rw [← hm]
  exact Finset.sum_congr rfl fun j _ => by rw [head_apply]

theorem last_int {x : Fin 9 → ℚ} (hx : x ∈ EZ) : IsIntQ (x 8) := by
  obtain ⟨m, hm⟩ := (mem_omearaEZ.mp hx).2 8 (by decide)
  exact ⟨m, hm⟩

theorem e8_mem : e8 ∈ EZ := by
  rw [mem_omearaEZ]
  refine ⟨?_, fun i hi => ⟨if i = 8 then 1 else 0, ?_⟩⟩
  · have : omearaEZHead 9 e8 = 0 := by
      funext j
      rw [head_apply]
      simp only [Pi.single_apply, Pi.zero_apply]
      rw [if_neg]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    rw [this]; exact Submodule.zero_mem _
  · have : i = 8 := Fin.ext (by omega)
    subst this
    simp

theorem two_e0_mem : (2 : ℚ) • e0 ∈ EZ := by
  rw [mem_omearaEZ]
  refine ⟨?_, fun i hi => ⟨0, ?_⟩⟩
  · have : omearaEZHead 9 ((2 : ℚ) • e0) = Pi.single (0 : Fin 8) 2 := by
      funext j
      rw [head_apply]
      by_cases hj : j = 0
      · subst hj; simp
      · have h1 : Fin.castSucc j ≠ (0 : Fin 9) := by
          intro h; apply hj; exact Fin.ext (by simpa using congrArg Fin.val h)
        simp [Pi.single_apply, h1, hj]
    rw [this]
    exact Submodule.subset_span (Or.inl (Or.inr ⟨0, rfl, rfl⟩))
  · have h1 : i ≠ (0 : Fin 9) := by intro h; subst h; simp at hi
    simp [Pi.single_apply, h1]

theorem e0_not_mem : e0 ∉ EZ := by
  intro h
  have h1 : (sumSqForm 9).eval e0 = 1 := by
    rw [show (sumSqForm 9) = sosQ 9 from rfl, sosQ_eval_eq]
    simp [Pi.single_apply]
  have := norm_one_mem_omearaEZ (by norm_num) h h1 0 (by decide)
  simp at this

/-! ### A maximal lattice over $E$ -/

/-- **Maximality, general form**: if $M$ is $\mathbb Z$-maximal, $2y \in M$ and $\varphi[m + y] \in \mathbb Z$ for every
$m \in M$, then $y \in M$. -/
theorem mem_of_isGMaximal_gen {n : ℕ} {M : Lat ℚ n} (hM : IsGMaximal (sosQ n) M) {y : Fin n → ℚ}
    (h2 : (2 : ℚ) • y ∈ M.1) (hc : ∀ m ∈ M.1, IsIntQ (∑ i, (m + y) i ^ 2)) : y ∈ M.1 := by
  have hN := intNorm_of_isGMaximal hM
  have hK : IntNorm (M.1 ⊔ Submodule.span (𝓞 ℚ) {y}) := by
    intro z hz
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨k, hk⟩ : ∃ k : ℤ, ((k : ℤ) : 𝓞 ℚ) = c :=
      ⟨Rat.ringOfIntegersEquiv c, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply c)⟩
    subst hk
    have hcx : ((k : ℤ) : 𝓞 ℚ) • y = (k : ℚ) • y := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    rw [hcx]
    have heven : ∀ j : ℤ, Even j → (j : ℚ) • y ∈ M.1 := by
      rintro j ⟨t, rfl⟩
      have : ((t + t : ℤ) : ℚ) • y = ((t : 𝓞 ℚ)) • ((2 : ℚ) • y) := by
        rw [show ((t : 𝓞 ℚ)) • ((2 : ℚ) • y) = ((t : ℚ)) • ((2 : ℚ) • y) from by
          rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]]
        rw [smul_smul]; push_cast; ring_nf
      rw [this]; exact M.1.smul_mem _ h2
    rcases Int.even_or_odd k with he | ho
    · exact hN _ (M.1.add_mem hm (heven k he))
    · have he : Even (k - 1) := by rcases ho with ⟨t, ht⟩; exact ⟨t, by omega⟩
      have hm' : m + ((k - 1 : ℤ) : ℚ) • y ∈ M.1 := M.1.add_mem hm (heven _ he)
      have e : m + (k : ℚ) • y = (m + ((k - 1 : ℤ) : ℚ) • y) + y := by
        push_cast; rw [sub_smul, one_smul]; abel
      rw [e]; exact hc _ hm'
  have hlat : (M.1 ⊔ Submodule.span (𝓞 ℚ) {y}).IsLattice ℚ := by
    refine ⟨M.2.fg.sup (Submodule.fg_span_singleton y), ?_⟩
    rw [eq_top_iff, ← M.2.span_eq_top]
    exact Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left)
  have heq := hM.2.2 _ hlat le_sup_left (normIdeal_le_one_of_intNorm hK)
  rw [← heq]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)

/-- Isometries of the sum of squares preserve the dot product. -/
theorem dot_isometry {γ : GL (Fin 9) ℚ} (hγ : γ ∈ orthGroup (sumSqForm 9) ℚ) (x y : Fin 9 → ℚ) :
    (γ.val *ᵥ x) ⬝ᵥ (γ.val *ᵥ y) = x ⬝ᵥ y := by
  have h := bil_isometry (sumSqForm 9) hγ x y
  rw [two_sumSq_bil_dot, two_sumSq_bil_dot] at h
  linarith

/-- A neighbour of a lattice is a lattice. -/
theorem isLattice_of_nbr {n : ℕ} {Q : QuadForm ℚ n} {A B : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hA : A.IsLattice ℚ) (h : Nbr.IsNbrL Q 2 A B) : B.IsLattice ℚ := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hA
  have hπ : (2 : 𝓞 ℚ) ≠ 0 := two_ne_zero
  refine isLattice_of_global_bounds (d := 2 * d) (mul_ne_zero hπ hd) (fun z hz => ?_) (fun z hz => ?_)
  · rw [mul_smul, ← algebraMap_smul ℚ]
    exact h.smul_right _ (h1 z hz)
  · rw [mul_comm, mul_smul, ← algebraMap_smul ℚ (2 : 𝓞 ℚ)]
    exact h2 _ (h.smul_left _ hz)

variable {M : Lat ℚ 9} (hM : IsGMaximal (sosQ 9) M) (hE : EZ ≤ M.1)
include hM hE

/-- **Step 1**: $M \ne E$. -/
theorem exists_not_mem : ∃ u ∈ M.1, u ∉ EZ := by
  by_contra h
  push Not at h
  have hle : M.1 ≤ EZ := h
  have he0 : e0 ∈ M.1 := by
    refine mem_of_isGMaximal_gen hM (hE two_e0_mem) fun m hm => ?_
    have hmE := hle hm
    obtain ⟨a, ha⟩ := (intNorm_of_isGMaximal hM) m hm
    obtain ⟨b, hb⟩ := dot_int hmE two_e0_mem
    rw [sum_sq_add, ha]
    have h1 : ∑ i, e0 i ^ 2 = 1 := by simp [Pi.single_apply]
    have h2 : m ⬝ᵥ ((2 : ℚ) • e0) = 2 * (m ⬝ᵥ e0) := by rw [dotProduct_smul, smul_eq_mul]
    rw [h1]
    exact ⟨a + b + 1, by push_cast; linarith⟩
  exact e0_not_mem (hle he0)

/-- **Step 2**: a vector $a \in M \setminus E$ with $2a \in E$ and $a_8 = 0$. -/
theorem exists_a : ∃ a ∈ M.1, a ∉ EZ ∧ (2 : ℚ) • a ∈ EZ ∧ a 8 = 0 := by
  have hN := intNorm_of_isGMaximal hM
  obtain ⟨u, hu, huE⟩ := exists_not_mem hM hE
  -- `2u ∈ E^# = E`
  have h2u : (2 : ℚ) • u ∈ EZ := by
    rw [← EZ_unimodular, mem_omearaDual_iff]
    intro y hy
    obtain ⟨a, ha⟩ := hN _ (M.1.add_mem hu (hE hy))
    obtain ⟨b, hb⟩ := hN u hu
    obtain ⟨c, hc⟩ := hN y (hE hy)
    rw [sum_sq_add, hb, hc] at ha
    refine ⟨a - b - c, ?_⟩
    rw [smul_dotProduct, smul_eq_mul]; push_cast; linarith
  -- the last coordinate of `u` is an integer
  obtain ⟨k, hk⟩ := last_int h2u
  obtain ⟨m', hm'⟩ := head_even h2u
  obtain ⟨t, ht⟩ := hN u hu
  have hsum : ∑ i, ((2 : ℚ) • u) i ^ 2 = 4 * ∑ i, u i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  rw [sum_split, hm', hk, ht] at hsum
  have hk2 : Even k := by
    by_contra hodd
    rw [Int.not_even_iff_odd] at hodd
    obtain ⟨r, rfl⟩ := hodd
    have : ((2 * m' + (2 * r + 1) ^ 2 : ℤ) : ℚ) = ((4 * t : ℤ) : ℚ) := by push_cast at hsum ⊢; linarith
    have h' : 2 * m' + (2 * r + 1) ^ 2 = 4 * t := by exact_mod_cast this
    have e : 2 * m' + (2 * r + 1) ^ 2 = 2 * (m' + 2 * r ^ 2 + 2 * r) + 1 := by ring
    rw [e] at h'
    omega
  obtain ⟨s, rfl⟩ := hk2
  have hu8 : u 8 = s := by
    have : (2 : ℚ) * u 8 = ((s + s : ℤ) : ℚ) := by rw [← hk]; simp
    push_cast at this; linarith
  have hint : ∀ j : ℤ, (j : ℚ) • e8 ∈ EZ := by
    intro j
    have : (j : ℚ) • e8 = ((j : 𝓞 ℚ)) • e8 := by rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    rw [this]; exact Submodule.smul_mem _ _ e8_mem
  have hse8 := hint s
  refine ⟨u - (s : ℚ) • e8, M.1.sub_mem hu (hE hse8), fun h => huE ?_, ?_, ?_⟩
  · have := EZ.add_mem h hse8; rwa [sub_add_cancel] at this
  · rw [smul_sub, smul_smul, show (2 : ℚ) * (s : ℚ) = ((2 * s : ℤ) : ℚ) by push_cast; ring]
    exact EZ.sub_mem h2u (hint _)
  · simp [hu8]

/-- **Step 3**: such a vector with $\varphi[a]$ odd. -/
theorem exists_a_odd : ∃ a ∈ M.1, a ∉ EZ ∧ (2 : ℚ) • a ∈ EZ ∧ a 8 = 0 ∧ ∃ r : ℤ, ∑ i, a i ^ 2 = 2 * r + 1 := by
  have hN := intNorm_of_isGMaximal hM
  obtain ⟨a, ha, haE, h2a, ha8⟩ := exists_a hM hE
  obtain ⟨t, ht⟩ := hN a ha
  rcases Int.even_or_odd t with ⟨t', rfl⟩ | ⟨t', rfl⟩
  swap
  · exact ⟨a, ha, haE, h2a, ha8, t', by rw [ht]; push_cast; ring⟩
  -- `a ∉ E = E^#`: some `y ∈ E` has `a ⬝ y ∉ ℤ`
  have : ¬ ∀ y ∈ EZ, IsIntQ (a ⬝ᵥ y) := by
    intro h
    apply haE
    rw [← EZ_unimodular, mem_omearaDual_iff]
    exact h
  push Not at this
  obtain ⟨y, hy, hay⟩ := this
  obtain ⟨p, hp⟩ := dot_int h2a hy
  rw [smul_dotProduct, smul_eq_mul] at hp
  have hpodd : Odd p := by
    rcases Int.even_or_odd p with ⟨q, rfl⟩ | h
    · exact absurd ⟨q, by push_cast at hp; linarith⟩ hay
    · exact h
  obtain ⟨j, hj⟩ := last_int hy
  have hje8 : (j : ℚ) • e8 ∈ EZ := by
    have : (j : ℚ) • e8 = ((j : 𝓞 ℚ)) • e8 := by rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    rw [this]; exact Submodule.smul_mem _ _ e8_mem
  set y' := y - (j : ℚ) • e8 with hy'
  have hy'E : y' ∈ EZ := EZ.sub_mem hy hje8
  have hy'8 : y' 8 = 0 := by simp [hy', hj]
  have hay' : a ⬝ᵥ y' = a ⬝ᵥ y := by
    rw [hy', dotProduct_sub, dotProduct_smul]
    have : a ⬝ᵥ e8 = a 8 := by simp [dotProduct, Pi.single_apply]
    rw [this, ha8]; simp
  obtain ⟨m, hm⟩ := head_even hy'E
  have hy'sq : ∑ i, y' i ^ 2 = 2 * m := by rw [sum_split, hm, hy'8]; ring
  obtain ⟨q, hq⟩ := hpodd
  refine ⟨a + y', M.1.add_mem ha (hE hy'E), fun h => haE ?_, ?_, ?_, t' + q + m, ?_⟩
  · have := EZ.sub_mem h hy'E; rwa [add_sub_cancel_right] at this
  · rw [smul_add]
    refine EZ.add_mem h2a ?_
    have h := EZ.smul_mem (2 : 𝓞 ℚ) hy'E
    rwa [← algebraMap_smul ℚ (2 : 𝓞 ℚ) y', map_ofNat] at h
  · simp [ha8, hy'8]
  · rw [sum_sq_add, ht, hay', hy'sq]
    push_cast
    have : 2 * (a ⬝ᵥ y) = p := by linarith
    rw [this, hq]; push_cast; ring

/-- **Step 4**: $M$ contains an isometric copy of $\mathbb Z^9$. -/
theorem exists_intVec_le : ∃ ρ ∈ orthGroup (sosQ 9) ℚ, glImage ρ (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ≤ M.1 := by
  obtain ⟨a, ha, haE, h2a, ha8, r, hr⟩ := exists_a_odd hM hE
  have hQa : ∃ m : ℤ, (sumSqForm 9).eval a = m :=
    ⟨2 * r + 1, by rw [show (sumSqForm 9) = sosQ 9 from rfl, sosQ_eval_eq, hr]; push_cast; ring⟩
  obtain ⟨hJu, haJ, hadj, -⟩ := omeara106_7 (sumSqForm 9) EZ_unimodular h2a haE hQa
  set J := Submodule.span (𝓞 ℚ) {a} ⊔ omearaDual (sumSqForm 9) (Submodule.span (𝓞 ℚ) {a} ⊔ EZ) with hJ
  have hJM : J ≤ M.1 := by
    refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr ha) ?_
    refine (omearaDual_anti le_sup_right).trans ?_
    rw [EZ_unimodular]; exact hE
  have hJlat : J.IsLattice ℚ := isLattice_of_nbr EZ_isLattice hadj.symm
  have he8J : e8 ∈ J := by
    refine Submodule.mem_sup_right ((mem_omearaDual_iff).mpr fun z hz => ?_)
    obtain ⟨w, hw, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨k, hk⟩ := last_int hv
    refine ⟨k, ?_⟩
    have : e8 ⬝ᵥ (c • a + v) = (c • a + v) 8 := by simp [dotProduct, Pi.single_apply]
    rw [this, Pi.add_apply, Pi.smul_apply, ha8, smul_zero, zero_add, hk]
  rcases unimodular_rank9 ⟨J, hJlat⟩ hJu with ⟨ρ, hρ, he⟩ | ⟨ρ, hρ, he⟩
  · exact ⟨ρ, hρ, he ▸ hJM⟩
  · exfalso
    -- `ρ : E ≅ J`; the preimage of `e8` has norm one, hence is `±e8`
    obtain ⟨w, hw, hwe⟩ := mem_glImage.mp (he ▸ he8J : e8 ∈ glImage ρ EZ)
    obtain ⟨b, hb, hba⟩ := mem_glImage.mp (he ▸ haJ : a ∈ glImage ρ EZ)
    have hw1 : (sumSqForm 9).eval w = 1 := by
      have h := dot_isometry hρ w w
      rw [hwe] at h
      rw [show (sumSqForm 9) = sosQ 9 from rfl, sosQ_eval_eq, ← dot_self, ← h]
      simp [dotProduct, Pi.single_apply]
    have hw0 := norm_one_mem_omearaEZ (by norm_num) hw hw1
    have hw8 : w 8 ≠ 0 := by
      intro h0
      have : w = 0 := by
        funext i
        by_cases hi : i.val < 8
        · exact hw0 i hi
        · have : i = 8 := Fin.ext (by omega)
          rw [this, h0]; rfl
      rw [this, show (sumSqForm 9) = sosQ 9 from rfl, sosQ_eval_eq] at hw1
      simp at hw1
    -- `b ⊥ w`, so `b 8 = 0` and `φ[b]` is even
    have hbw : b ⬝ᵥ w = 0 := by
      have h := dot_isometry hρ b w
      rw [hba, hwe] at h
      rw [← h]
      simp [dotProduct, Pi.single_apply, ha8]
    have hb8 : b 8 = 0 := by
      have : b ⬝ᵥ w = b 8 * w 8 := by
        rw [dotProduct, sum_split]
        have : ∀ j : Fin 8, b (Fin.castSucc j) * w (Fin.castSucc j) = 0 := fun j => by
          rw [hw0 (Fin.castSucc j) (by simp)]; ring
        simp [this]
      rw [this] at hbw
      exact (mul_eq_zero.mp hbw).resolve_right hw8
    obtain ⟨m, hm⟩ := head_even hb
    have hbsq : ∑ i, b i ^ 2 = 2 * m := by rw [sum_split, hm, hb8]; ring
    have hab : ∑ i, a i ^ 2 = ∑ i, b i ^ 2 := by
      rw [← dot_self, ← dot_self, ← hba, dot_isometry hρ]
    rw [hr, hbsq] at hab
    have : (2 * r + 1 : ℤ) = 2 * m := by exact_mod_cast hab
    omega

end NineE8

/-- **`SumSqMaxContainsIntVec 9`**: every $\mathbb Z$-maximal lattice for the sum of nine squares contains an
isometric copy of $\mathbb Z^9$. A unimodular sublattice is $\cong \mathbb Z^9$ or $\cong E_8 \perp \mathbb Z$
(O'Meara 106:13); in the second case a $2$-neighbour inside $M$ is $\cong \mathbb Z^9$ (`NineE8.exists_intVec_le`). -/
theorem sumSqMaxContainsIntVec_nine : SumSqMaxContainsIntVec 9 := by
  refine ⟨fun M hM => ?_⟩
  obtain ⟨K, hK, hKM⟩ := exists_unimodular_le (by norm_num) hM
  rcases unimodular_rank9 K hK with ⟨γ, hγ, he⟩ | ⟨γ, hγ, he⟩
  · exact ⟨γ, hγ, he ▸ hKM⟩
  · have hγi : γ⁻¹ ∈ orthGroup (sosQ 9) ℚ := (orthGroup (sosQ 9) ℚ).inv_mem hγ
    have hM' := isGMaximal_image hM hγi
    have hE : NineE8.EZ ≤ (Lat.image γ⁻¹ M).1 := by
      have := glImage_mono γ⁻¹ hKM
      rwa [← he, ← glImage_mul, inv_mul_cancel, glImage_one] at this
    obtain ⟨ρ, hρ, hle⟩ := NineE8.exists_intVec_le hM' hE
    refine ⟨γ * ρ, (orthGroup (sosQ 9) ℚ).mul_mem hγ hρ, ?_⟩
    rw [glImage_mul]
    have := glImage_mono γ hle
    change glImage γ (glImage ρ intVec) ≤ glImage γ (glImage γ⁻¹ M.1) at this
    rwa [← glImage_mul γ γ⁻¹, mul_inv_cancel, glImage_one] at this

/-- **`SumSquaresOneClass` holds** (Shimura 2004, §12.12, p. 122, [S02a, Lemma 1.6], for $n = 5, 7, 9$): the
$SO^\varphi$-genus of a $\mathbb Z$-maximal lattice for the sum of $n$ squares is one $SO^\varphi$-class.
Unconditional: from `sumSquaresOneClass_of` with `SumSqMaxContainsIntVec` ($n \le 7$: O'Meara 106:10; $n = 9$: this
file) and `SumSqMaxOverIntVec` (maximal doubly even codes of length $5$, $7$, $9$). -/
@[kb "shimura2004" "§12.12, p. 122 (one SO^φ-class in the genus of ℤ-maximal lattices, n = 5, 7, 9; proved)"]
theorem sumSquaresOneClass : SumSquaresOneClass := by
  refine sumSquaresOneClass_of (fun n hn => ?_) (fun n hn => ?_)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact sumSqMaxContainsIntVec_of_le_seven (by norm_num) (by norm_num)
    · exact sumSqMaxContainsIntVec_of_le_seven (by norm_num) (by norm_num)
    · exact sumSqMaxContainsIntVec_nine
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact sumSqMaxOverIntVec_five
    · exact sumSqMaxOverIntVec_seven
    · exact sumSqMaxOverIntVec_nine

/-- **Theorem 12.14 (iv)** (Shimura 2004, p. 123), first assertion, *unconditional*: for $n = 5, 7, 9$, $\varphi$ the
sum of $n$ squares, $L$ a $\mathbb Z$-maximal lattice and $h \in L[q, \mathbb Z]$ with $q = \varphi[h] > 0$,
$\#(L[q, \mathbb Z]/\Gamma(L)) = \#(H\backslash H_{\mathbb A}/E)$. This is `theorem_12_14_iv_of_local` with the
one-class input `SumSquaresOneClass` now proved (`sumSquaresOneClass`). -/
@[kb "shimura2004" "Thm. 12.14 (iv), p. 123 (unconditional)"]
theorem theorem_12_14_iv_holds : Theorem12_14_iv :=
  theorem_12_14_iv_of_local sumSquaresOneClass

end QuadFormsKB.Shimura2004
