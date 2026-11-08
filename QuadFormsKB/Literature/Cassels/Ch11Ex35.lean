/-
# Cassels, Chapter 11, Example 3: the genus of $x^2 + 5y^2 - 25z^2$ has one class

Proves `Cassels.Ch11Ex4.Ex3OneClass` (`ex3OneClass_holds`).

**Route (the group $G$ of (3.15) with $P = \{2, 5\}$, not the criterion $U_p \subseteq \theta(\Lambda_p)$).** At $p = 5$
the unit classes are *not* all spinor norms ($\theta(\Lambda_5) = \langle(\mathbb Q_5^\times)^2, 5\rangle$ by Example 4),
so Lemma 3.6, Corollary does not apply. Instead: every spinor genus of the genus contains a lattice $\beta\Lambda$ with
$\theta(\beta_p)$ a unit class for $p \in P = \{2,5\}$ and $\beta_p = 1$ elsewhere (Lemma 3.4, Corollary); its class in
$G = R/ST$ is trivial, because a unit class $u$ at $5$ satisfies $2u \in (\mathbb Q_5^\times)^2 \subseteq \theta(\Lambda_5)$ or
$u \in (\mathbb Q_5^\times)^2$ (so $u \in \theta(\Lambda_5)\cdot\{1,2\}$), and at $2$ the group $\theta(\Lambda_2)$ is all
of $\mathbb Q_2^\times$ (it contains the units, by Lemma 3.8, Corollary, and also $2$: the symmetries in $e_0$ and
$e_0 + e_1$, of values $1$ and $6$, give $6$, and $3$ is a unit); the global element is $t \in \{1, 2\} \subseteq T$.
Hence the genus is one proper spinor genus (Lemma 3.5), and an indefinite proper spinor genus of dimension $\ge 3$ is
one proper class (Theorem 1.4); $f$ has the improper automorph $x_0 \mapsto -x_0$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex4Sub
import QuadFormsKB.Literature.Cassels.Ch11Remarks2
import QuadFormsKB.Literature.Cassels.Ch11Sec3GroupLemma34
import QuadFormsKB.Literature.ConwaySloane.Section9Group
import QuadFormsKB.Literature.Cassels.Ch11Sec4Group

open Matrix NumberField IsDedekindDomain QuadFormsKB.Siegel

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Ex4

open QuadFormsKB

/-- Helper: $x_0^2 + 5x_1^2 - 25x_2^2$ evaluated over a field containing $\mathbb Z$. Argument `x`: the vector. -/
theorem evalIn_ex3f {K : Type*} [Field K] [Algebra ℤ K] (x : Fin 3 → K) :
    ex3f.evalIn K x = x 0 ^ 2 + 5 * x 1 ^ 2 - 25 * x 2 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_three, ex3f, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: the Hessian determinant of $x_0^2 + 5x_1^2 - 25x_2^2$ is $-1000$. -/
theorem hessian_det_ex3f : ex3f.hessian.det = -1000 := by
  rw [ex3f, Ch11Wave6.hessian_diag, det_diagonal, Fin.prod_univ_three]
  simp

/-- Helper: $f = x_0^2 + 5x_1^2 - 25x_2^2$ is indefinite over $\mathbb Q$. -/
theorem isIndefinite_ex3f : Lattices.IsIndefinite (ex3f.map (Int.castRingHom ℚ)) := by
  refine Lattices.isIndefinite_of_neg_pos ex3f ![0, 0, 1] ![1, 0, 0] ?_ ?_
  · rw [evalIn_ex3f]; simp
  · rw [evalIn_ex3f]; simp

/-- Helper: $x_0 \mapsto -x_0$ is an improper automorph of $f = x_0^2 + 5x_1^2 - 25x_2^2$. -/
theorem hasImproperAut_ex3f : HasImproperAut ex3f := by
  refine ⟨reflFirst (n := 3) (by norm_num), fun x => ?_, det_reflFirst _⟩
  rw [eval_ex3f, eval_ex3f]
  simp only [reflFirst, mulVec_diagonal]
  simp

/-- Helper: $f$ is nondegenerate over $\mathbb Q$. -/
theorem nondegenerate_ex3f : (ex3f.map (Int.castRingHom ℚ)).Nondegenerate :=
  Lattices.nondegenerate_map_of_det_ne_zero ex3f (by rw [hessian_det_ex3f]; norm_num)

/-! ### The places $2$ and $5$, and the odd unimodular primes -/

/-- Helper: the place of $\mathbb Q$ above the prime `q` (`hq`). -/
def ratPlace (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

/-- Helper: the prime of `ratPlace q hq` is `q`. -/
theorem natGenerator_ratPlace (q : ℕ) (hq : q.Prime) :
    Rat.HeightOneSpectrum.natGenerator (ratPlace q hq) = q :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨q, hq⟩)

/-! ### The prime $2$: $\theta(\Lambda_2)$ is all of $\mathbb Q_2^\times$ -/

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- Helper: $f$ evaluated over any $\mathbb Q$-algebra field, via the map to $\mathbb Q$. Argument `x`: the vector. -/
theorem evalIn_ex3Q {K : Type*} [Field K] [Algebra ℚ K] (x : Fin 3 → K) :
    (ex3f.map (Int.castRingHom ℚ)).evalIn K x = x 0 ^ 2 + 5 * x 1 ^ 2 - 25 * x 2 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_three, ex3f, QuadForm.map, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: $\theta(\Lambda_v)$ depends only on square classes: if $a \in \theta(\Lambda_v)$ and $b, a$ have the
same square class, then $b \in \theta(\Lambda_v)$. Arguments: `v` the place, `a b` the units. -/
theorem mem_theta_of_class_eq {v : HeightOneSpectrum (𝓞 ℚ)} {a b : (v.adicCompletion ℚ)ˣ}
    (ha : a ∈ Lattices.localSpinorNormGroup (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f v Lattices.stdLat)
    (h : Lattices.SqClass.mk b = Lattices.SqClass.mk a) :
    b ∈ Lattices.localSpinorNormGroup (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f v Lattices.stdLat := by
  unfold Lattices.localSpinorNormGroup at ha ⊢
  simp only [Subgroup.mem_comap, Lattices.sqClassHom_apply] at ha ⊢
  rw [h]; exact ha

/-- Helper: at a place $v$ over $2$, every unit of the completion is in $\theta(\Lambda_v)$ (Cassels, Lemma 3.8,
Corollary, since $2^5 \nmid \det H = -1000$). Arguments: `v` the place (`h2`: it lies over $2$), `u` the unit (`hu`:
of absolute value $1$). -/
theorem units_mem_theta_two (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    u ∈ Lattices.localSpinorNormGroup (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f v Lattices.stdLat := by
  refine Ch11Wave6.units_mem_localSpinorNormGroup_two ex3f nondegenerate_ex3f ?_ v h2 u hu
  rintro ⟨-, hd⟩
  have h5 : (Lattices.casselsExpTwo 3 + ((3 : ℕ) : ℤ)).toNat = 5 := by
    unfold Lattices.casselsExpTwo
    norm_num
  rw [h5, hessian_det_ex3f] at hd
  norm_num at hd

/-- Helper: at a place $v$ over $2$, the element $2$ of the completion is in $\theta(\Lambda_v)$. The symmetries in
$e_0$ (value $1$) and $e_0 + e_1$ (value $6$) both stabilize $\mathbb Z_2^3$, giving $6 \in \theta$, and $3$ is a
unit. Argument `v`: the place (`h2`: over $2$); `h20`: the nonvanishing of $2$ in the completion. -/
theorem two_mem_theta (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (h20 : (2 : v.adicCompletion ℚ) ≠ 0) :
    Units.mk0 (2 : v.adicCompletion ℚ) h20 ∈
      Lattices.localSpinorNormGroup (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f v Lattices.stdLat := by
  have hp2 := (Lattices.two_mem_iff_natGenerator v).mp h2
  have hL : Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1 = Lattices.std v := Lattices.loc_intVec v
  set K := v.adicCompletion ℚ
  have hint : ∀ x ∈ Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1,
      Valued.v ((ex3f.map (Int.castRingHom ℚ)).evalIn K x) ≤ 1 := by
    intro x hx; rw [hL] at hx
    convert Lattices.valued_evalIn_le_one_int v ex3f hx using 3
    exact Subsingleton.elim _ _
  have h3 : Valued.v (3 : K) = 1 := by
    have := Lattices.valued_natCast_eq_one' (v := v) (m := 3) (by
      rw [hp2]; norm_num)
    simpa using this
  have h30 : (3 : K) ≠ 0 := fun h => by rw [h, map_zero] at h3; exact zero_ne_one h3
  have h6 : Units.mk0 (6 : K) (by
      have : (6 : K) = 2 * 3 := by norm_num
      rw [this]; exact mul_ne_zero h20 h30) ∈
      Lattices.localSpinorNormGroup (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f v Lattices.stdLat := by
    have hxv : (ex3f.map (Int.castRingHom ℚ)).evalIn K (Pi.single 0 1) = 1 := by
      rw [evalIn_ex3Q]; simp
    have hyv : (ex3f.map (Int.castRingHom ℚ)).evalIn K ![1, 1, 0] = 6 := by
      rw [evalIn_ex3Q]; simp; norm_num
    have hx0 : (ex3f.map (Int.castRingHom ℚ)).evalIn K (Pi.single 0 1) ≠ 0 := by rw [hxv]; exact one_ne_zero
    have h60 : (6 : K) ≠ 0 := by
      have : (6 : K) = 2 * 3 := by norm_num
      rw [this]; exact mul_ne_zero h20 h30
    have hy0 : (ex3f.map (Int.castRingHom ℚ)).evalIn K ![1, 1, 0] ≠ 0 := by rw [hyv]; exact h60
    have h5 : Valued.v (5 : K) = 1 := by
      have := Lattices.valued_natCast_eq_one' (v := v) (m := 5) (by
        rw [hp2]; norm_num)
      simpa using this
    have hxM : (Pi.single 0 1 : Fin 3 → K) ∈ Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1 := by
      rw [hL]; exact Lattices.single_mem_std 0 (by simp)
    have hyM : (![1, 1, 0] : Fin 3 → K) ∈ Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1 := by
      rw [hL, Lattices.mem_std_iff]
      intro i; fin_cases i <;> simp
    have hxs := Lattices.symm_mem_locStabV_of_unit Lattices.stdLat hint hxM (by rw [hxv, map_one])
    have hys : Lattices.symm (ex3f.map (Int.castRingHom ℚ)) K ![1, 1, 0] ∈
        Lattices.locStabV (ex3f.map (Int.castRingHom ℚ)) v Lattices.stdLat := by
      show Lattices.locAct v (Lattices.symm (ex3f.map (Int.castRingHom ℚ)) K ![1, 1, 0] : GL (Fin 3) K)
        (Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1) = Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1
      refine Lattices.locAct_symm_eq hyM hy0 fun z hz => ?_
      rw [hL, Lattices.mem_std_iff] at hz
      have hq : Lattices.qbil (ex3f.map (Int.castRingHom ℚ)) K ![1, 1, 0] z = 2 * (z 0 + 5 * z 1) := by
        rw [Lattices.qbil_eq_polar, evalIn_ex3Q, evalIn_ex3Q, evalIn_ex3Q]
        simp
        ring
      rw [hq, hyv, map_mul, show (6 : K) = 2 * 3 by norm_num, map_mul, h3, mul_one]
      have hle : Valued.v (z 0 + 5 * z 1) ≤ 1 :=
        Valuation.map_add_le _ (hz 0) (by rw [map_mul, h5, one_mul]; exact hz 1)
      calc Valued.v (2 : K) * Valued.v (z 0 + 5 * z 1) ≤ Valued.v (2 : K) * 1 := mul_le_mul_right hle _
        _ = Valued.v (2 : K) := mul_one _
    refine Lattices.mem_localSpinorNormGroup_of_symm_pair nondegenerate_ex3f Lattices.stdLat hx0 hy0 hxs hys
      (Units.mk0 6 h60) ?_
    rw [hxv, hyv, one_mul, Lattices.sqClassOf_of_ne_zero h60]
  have h3u : Units.mk0 (3 : K) h30 ∈
      Lattices.localSpinorNormGroup (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f v Lattices.stdLat :=
    units_mem_theta_two v h2 _ (by simpa using h3)
  have h60 : (6 : K) ≠ 0 := by
    have : (6 : K) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h20 h30
  have e : Units.mk0 (2 : K) h20 = Units.mk0 (6 : K) h60 * (Units.mk0 (3 : K) h30)⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    simp only [Units.val_mk0]
    rw [eq_mul_inv_iff_mul_eq₀ h30]
    norm_num
  rw [e]
  exact Subgroup.mul_mem _ h6 (Subgroup.inv_mem _ h3u)

/-! ### The prime $5$: unit classes, up to the factor $2$, are squares -/

/-- Helper: if $m = c^2 t$ and $m z^{-1}$ is a square, then $t z$ is a square (in a field, $z, c \ne 0$).
Arguments: `z c t m` the elements, `hz hc` their nonvanishing, `hm` the relation $m = c^2t$, `h` the squareness. -/
theorem isSquare_aux {K : Type*} [Field K] (z c t m : K) (hz : z ≠ 0) (hc : c ≠ 0) (hm : m = c ^ 2 * t)
    (h : IsSquare (m * z⁻¹)) : IsSquare (t * z) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s * z / c, ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hc hc)]
  have h2 : s * s = c ^ 2 * t * z⁻¹ := by rw [← hs, hm]
  calc t * z * (c * c) = (c ^ 2 * t * z⁻¹) * z * z := by field_simp
    _ = s * z * (s * z) := by rw [← h2]; ring

/-- Helper: at the place `v` over $5$, for a unit $z$ of the completion one of $z$, $2z$ is a square. Arguments: `v`
the place (`hv`: its prime is $5$), `z` the unit (`hz`: of absolute value $1$). -/
theorem exists_two_mul_isSquare (v : HeightOneSpectrum (𝓞 ℚ)) (hv : Rat.HeightOneSpectrum.natGenerator v = 5)
    (z : v.adicCompletion ℚ) (hz : Valued.v z = 1) :
    ∃ t : ℕ, (t = 1 ∨ t = 2) ∧ IsSquare ((t : v.adicCompletion ℚ) * z) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, map_zero] at hz; exact zero_ne_one hz
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h => by
    have := (Lattices.two_mem_iff_natGenerator v).mp h
    omega
  have hcm : Lattices.casselsMod v = 5 := by
    unfold Lattices.casselsMod; simp [h2, hv]
  obtain ⟨a, hcop, hsq⟩ := Lattices.exists_res v z hz
  rw [hcm] at hcop hsq
  have hnd : ¬ 5 ∣ a := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mp hcop.symm
  have hr : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
  have h2K : (2 : v.adicCompletion ℚ) ≠ 0 := two_ne_zero
  rcases hr with hr | hr | hr | hr
  · refine ⟨1, Or.inl rfl, ?_⟩
    have := hsq 1 (by simp [Int.ModEq]; omega)
    have := isSquare_aux z 1 1 ((1 : ℤ) : v.adicCompletion ℚ) hz0 one_ne_zero (by simp) this
    simpa using this
  · refine ⟨2, Or.inr rfl, ?_⟩
    have := hsq 2 (by simp [Int.ModEq]; omega)
    have := isSquare_aux z 1 2 ((2 : ℤ) : v.adicCompletion ℚ) hz0 one_ne_zero (by simp) this
    simpa using this
  · refine ⟨2, Or.inr rfl, ?_⟩
    have := hsq 8 (by simp [Int.ModEq]; omega)
    have := isSquare_aux z 2 2 ((8 : ℤ) : v.adicCompletion ℚ) hz0 h2K (by push_cast; ring) this
    simpa using this
  · refine ⟨1, Or.inl rfl, ?_⟩
    have := hsq 4 (by simp [Int.ModEq]; omega)
    have := isSquare_aux z 2 1 ((4 : ℤ) : v.adicCompletion ℚ) hz0 h2K (by push_cast; ring) this
    simpa using this

/-! ### The group $G = R/ST$ is trivial on unit classes -/

/-- Helper: an element with trivial square class is in $\theta(\Lambda_v)$. Arguments: `v` the place, `a` the unit
(`h`: its square class is trivial). -/
theorem mem_theta_of_sq {v : HeightOneSpectrum (𝓞 ℚ)} {a : (v.adicCompletion ℚ)ˣ}
    (h : Lattices.SqClass.mk a = 1) :
    a ∈ Lattices.localSpinorNormGroup (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f v Lattices.stdLat := by
  unfold Lattices.localSpinorNormGroup
  simp only [Subgroup.mem_comap, Lattices.sqClassHom_apply, h]
  exact Subgroup.one_mem _

/-- Helper: the diagonal image of the rational $t' \in \mathbb N$ has the value $t'$ at every place. Arguments: `P`
the finite set of places, `t'` the natural number (`ht`: nonzero), `v` the place. -/
theorem casselsDiag_val (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (t' : ℕ) (ht : (t' : ℚ) ≠ 0) (v : P) :
    ((Lattices.casselsDiag P (Units.mk0 (t' : ℚ) ht) v : (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ) =
      (t' : v.1.adicCompletion ℚ) := by
  rw [Lattices.casselsDiag_apply]
  simp

/-- **The trivial element of $G$ on unit classes** (Cassels, (3.15) with $P = \{2, 5\}$): every family `x` of unit
square classes at the places of `P` (those with prime $2$ or $5$) has the form $x = s\cdot t^{-1}$ with $s \in S$
and $t \in T$; precisely, $x\cdot\mathrm{diag}(t) \in S$ for some $t \in T$ ($t = 1$ or $2$). Arguments: `P` the
places over $2$ and $5$ (`hmem`), `x` the family (`hx`: each component is a unit square class). -/
theorem exists_diag_mem (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hmem : ∀ v, v ∈ P ↔ Rat.HeightOneSpectrum.natGenerator v = 2 ∨ Rat.HeightOneSpectrum.natGenerator v = 5)
    (x : Lattices.CasselsR P)
    (hx : ∀ v : P, Lattices.IsUnitSqClass v.1 (Lattices.SqClass.mk (x v))) :
    ∃ t : ℚˣ, t ∈ Lattices.casselsT (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f P ∧
      x * Lattices.casselsDiag P t ∈
        Lattices.casselsS (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f Lattices.stdLat P := by
  have hp5 : (ratPlace 5 Nat.prime_five) ∈ P :=
    (hmem _).mpr (Or.inr (natGenerator_ratPlace 5 Nat.prime_five))
  set v5 : P := ⟨ratPlace 5 Nat.prime_five, hp5⟩ with hv5def
  have hv5 : Rat.HeightOneSpectrum.natGenerator v5.1 = 5 := natGenerator_ratPlace 5 Nat.prime_five
  obtain ⟨z, hz1, hzc⟩ := hx v5
  have hz0 : z ≠ 0 := fun h => by rw [h, map_zero] at hz1; exact zero_ne_one hz1
  obtain ⟨t', ht', hsq⟩ := exists_two_mul_isSquare v5.1 hv5 z hz1
  have htn : t' ≠ 0 := by rcases ht' with rfl | rfl <;> norm_num
  have ht0 : (t' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htn
  have htK : ∀ v : P, (t' : v.1.adicCompletion ℚ) ≠ 0 := fun v => Nat.cast_ne_zero.mpr htn
  refine ⟨Units.mk0 (t' : ℚ) ht0, ?_, ?_⟩
  · refine (Lattices.mem_casselsT_rat_iff _ nondegenerate_ex3f le_rfl P _).mpr ⟨fun v hv => ?_, fun _ => ?_⟩
    · have h2 : Rat.HeightOneSpectrum.natGenerator v ≠ 2 := fun h => hv ((hmem v).mpr (Or.inl h))
      have hnd : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ t' := by
        intro hd
        rcases ht' with rfl | rfl
        · exact (Rat.HeightOneSpectrum.prime_natGenerator v).one_lt.ne' (Nat.dvd_one.mp hd)
        · exact h2 ((Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) Nat.prime_two).mp hd)
      have := Lattices.valued_natCast_eq_one' (v := v) hnd
      simp only [Units.val_mk0, eq_ratCast]
      exact this
    · simp only [Units.val_mk0]
      positivity
  · rw [Lattices.casselsS, Subgroup.mem_pi]
    intro v _
    show x v * Lattices.casselsDiag P _ v ∈ _
    have hdv : (Lattices.casselsDiag P (Units.mk0 (t' : ℚ) ht0) v) =
        Units.mk0 (t' : v.1.adicCompletion ℚ) (htK v) :=
      Units.ext (casselsDiag_val P t' ht0 v)
    rcases (hmem v.1).mp v.2 with h2 | h5
    · -- the prime 2
      have h2' : (2 : 𝓞 ℚ) ∈ v.1.asIdeal := (Lattices.two_mem_iff_natGenerator v.1).mpr h2
      obtain ⟨w, hw1, hwc⟩ := hx v
      have hw0 : w ≠ 0 := fun h => by rw [h, map_zero] at hw1; exact zero_ne_one hw1
      have hT : Units.mk0 (t' : v.1.adicCompletion ℚ) (htK v) ∈
          Lattices.localSpinorNormGroup (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f v.1 Lattices.stdLat := by
        rcases ht' with rfl | rfl
        · convert Subgroup.one_mem _
          exact Units.ext (by simp)
        · convert two_mem_theta v.1 h2' two_ne_zero using 1
      have hW : Units.mk0 w hw0 ∈
          Lattices.localSpinorNormGroup (ex3f.map (Int.castRingHom ℚ)) nondegenerate_ex3f v.1 Lattices.stdLat :=
        units_mem_theta_two v.1 h2' _ hw1
      refine mem_theta_of_class_eq (Subgroup.mul_mem _ hW hT) ?_
      rw [hdv, Lattices.SqClass.mk_mul, Lattices.SqClass.mk_mul, hwc, Lattices.sqClassOf_of_ne_zero hw0]
    · -- the prime 5: only the place `v5`
      have hvv : v = v5 := Subtype.ext (Lattices.natGenerator_inj' (h5.trans hv5.symm))
      subst hvv
      refine mem_theta_of_sq ?_
      rw [hdv, Lattices.SqClass.mk_mul, hzc, Lattices.sqClassOf_of_ne_zero hz0, ← Lattices.SqClass.mk_mul]
      obtain ⟨y, hy⟩ := hsq
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hy
        exact mul_ne_zero (htK v5) hz0 hy
      refine (Lattices.SqClass.mk_eq_one_iff _).mpr ⟨Units.mk0 y hy0, ?_⟩
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mul]
      rw [sq, ← hy]
      ring

/-! ### The theorem -/

open Classical in
/-- Helper: the places of $\mathbb Q$ over $2$ and $5$, as a finite set. -/
def ex3P : Finset (HeightOneSpectrum (𝓞 ℚ)) := {ratPlace 2 Nat.prime_two, ratPlace 5 Nat.prime_five}

open Classical in
/-- Helper: `ex3P` consists of exactly the places whose prime is $2$ or $5$. Argument `v`: the place. -/
theorem mem_ex3P (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ ex3P ↔ Rat.HeightOneSpectrum.natGenerator v = 2 ∨ Rat.HeightOneSpectrum.natGenerator v = 5 := by
  unfold ex3P
  rw [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl (natGenerator_ratPlace 2 Nat.prime_two)
    · exact Or.inr (natGenerator_ratPlace 5 Nat.prime_five)
  · rintro (h | h)
    · exact Or.inl (Lattices.natGenerator_inj' (h.trans (natGenerator_ratPlace 2 Nat.prime_two).symm))
    · exact Or.inr (Lattices.natGenerator_inj' (h.trans (natGenerator_ratPlace 5 Nat.prime_five).symm))

/-- Helper: the unit families $X$ lie in $ST$ for $f$ and $P = \{2, 5\}$ ($Y = X$ in Cassels' notation: the group
$G = R/ST$ is trivial on unit classes). -/
theorem casselsX_le_ex3 :
    Lattices.casselsX ex3P ≤
      Lattices.casselsST (ex3f.map (Int.castRingHom ℚ))
        (Lattices.nondegenerate_map_of_det_ne_zero ex3f (by rw [hessian_det_ex3f]; norm_num)) Lattices.stdLat ex3P := by
  intro x hx
  have hx' : ∀ v : ex3P, Lattices.IsUnitSqClass v.1 (Lattices.SqClass.mk (x v)) := fun v =>
    ⟨(x v : v.1.adicCompletion ℚ), hx v, by
      rw [Lattices.sqClassOf_of_ne_zero (x v).ne_zero, Units.mk0_val]⟩
  obtain ⟨t, ht, hs⟩ := exists_diag_mem ex3P mem_ex3P x hx'
  have e : x = (x * Lattices.casselsDiag ex3P t) * (Lattices.casselsDiag ex3P t)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs)
    (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)))

/-- **Cassels, Ch. 11, Example 3** (p. 251), the genus of $f = x^2 + 5y^2 - 25z^2$ has one class, in the lattice form:
every form $f'$ in the genus of `ex3f` is integrally equivalent to `ex3f`. *Proof:* the group $G = R/ST$ of (3.15) for
$P = \{2, 5\}$ is trivial on unit classes (`casselsX_le_ex3`), so the genus is one proper spinor genus; $f$ is
indefinite, so the spinor genus is one class (Theorem 1.4); `ConwaySloane.intEquiv_of_sameGenus_of_casselsX_le`.
Argument `f'`: a form of the genus (`h`). -/
theorem ex3_intEquiv_of_sameGenus (f' : QuadForm ℤ 3) (h : SameGenus ex3f f') : IntEquiv ex3f f' := by
  have hf : ex3f.hessian.det ≠ 0 := by rw [hessian_det_ex3f]; norm_num
  refine ConwaySloane.intEquiv_of_sameGenus_of_casselsX_le le_rfl ex3f hf isIndefinite_ex3f ex3P ?_
    casselsX_le_ex3 f' h
  intro v hv hd
  have h2 : Rat.HeightOneSpectrum.natGenerator v ≠ 2 := fun h => hv ((mem_ex3P v).mpr (Or.inl h))
  have h5 : Rat.HeightOneSpectrum.natGenerator v ≠ 5 := fun h => hv ((mem_ex3P v).mpr (Or.inr h))
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  rw [hessian_det_ex3f] at hd
  have hd' : Rat.HeightOneSpectrum.natGenerator v ∣ 2 ^ 4 * 5 ^ 3 := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa using this
  rcases (Nat.Prime.dvd_mul hp).mp hd' with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h))

/-- **Cassels, Ch. 11, Example 3** (p. 251), proved: *$f = x^2 + 5y^2 - 25z^2$ is in a genus of $1$ class.* The set of
classes of the genus of `ex3f` has exactly one element (`ex3_intEquiv_of_sameGenus`). -/
@[kb "cassels1978" "Ch. 11, Ex. 3, p. 251 (proved)"]
theorem ex3OneClass_holds : Ex3OneClass := by
  refine ⟨?_⟩
  have : genusClasses ex3f = {classOf ex3f} := by
    ext c
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨Q', rfl, hQ'⟩
      exact (classOf_eq_classOf_iff.mpr (ex3_intEquiv_of_sameGenus Q' hQ')).symm
    · rintro rfl
      exact classOf_self_mem_genusClasses ex3f
  rw [this, Set.ncard_singleton]

end QuadFormsKB.Cassels.Ch11Ex4
