/-
# Cassels, Chapter 11, Example 5: $x^2 + py^2 - p^2z^2$, $p \equiv 1 \pmod 8$, has two classes

Proves `ex5_two_classes` and, with `ex5_one_class` (`Ch11Ex5.lean`), `ex5Statement_holds : Ex5Statement`.

**Route.** For $P = \{2, p\}$ the group $G = R/ST$ of Cassels (3.15) has order $2$ (`ex5_card_casselsG`), so the genus is two
proper spinor genera, and since $f$ is indefinite in $3$ (odd) variables these are two classes
(`Lattices.ncard_genusClasses_eq_two_of_card`).

* $|G| \ge 2$: let $n_0$ be an integer that is a nonresidue mod $p$ and $x_0 \in R$ the family with $x_{0,p} = n_0$ and
  $x_{0,2} = 1$. It is not in $ST$ (`ConwaySloane.not_mem_casselsST_of_subgroup`) for the subgroup $H$ of square classes of
  $\mathbb Q_p$ of the elements $p^k w^2$: (a) $\theta(\Lambda_p) \subseteq H$, because $p \in \theta(\Lambda_p)$ so the unit part
  of a spinor norm is a spinor norm, hence a square (`nonsquare_unit_not_mem_theta5`); (b) $\mathrm{diag}(2^k)$ at $p$ is a
  square since $2$ is a square mod $p$ for $p \equiv 1 \bmod 8$ (Hensel); (c) Cassels' $j = -1$ is a square at $p$.
* $|G| \le 2$: $\theta(\Lambda_2) = \mathbb Q_2^\times$ (`theta5_two_all`), and at $p$ every $a \in \mathbb Q_p^\times$ is, modulo
  $\theta(\Lambda_p) \ni p$ and squares, $1$ or $n_0$ (units mod squares have order $2$).
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex5
import QuadFormsKB.Literature.Cassels.Ch11ClassesSpinorGenera530
import QuadFormsKB.Literature.ConwaySloane.Section9TwoSpinorGenera

open Matrix NumberField IsDedekindDomain QuadFormsKB.Siegel

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Ex4

open QuadFormsKB

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-! ### Local facts at a place over $p$ -/

/-- Helper: the subgroup $\{p^k w^2\}$ of $(\mathbb Q_v)^\times$, for a place $v$ and a prime `p`. Arguments: `p`, `hp`, `v`. -/
def pSq5 (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (v.adicCompletion ℚ)ˣ where
  carrier := {a | ∃ (k : ℤ) (w : (v.adicCompletion ℚ)ˣ),
    a = (Units.mk0 (p : v.adicCompletion ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)) ^ k * w ^ 2}
  mul_mem' := by
    rintro a b ⟨k, w, rfl⟩ ⟨l, x, rfl⟩
    exact ⟨k + l, w * x, by rw [_root_.zpow_add, mul_pow]; exact mul_mul_mul_comm _ _ _ _⟩
  one_mem' := ⟨0, 1, by simp⟩
  inv_mem' := by
    rintro a ⟨k, w, rfl⟩
    exact ⟨-k, w⁻¹, by rw [mul_inv, _root_.zpow_neg, inv_pow]⟩

/-- Helper: the subgroup of square classes of `pSq5`. Arguments: `p`, `hp`, `v`. -/
def sqH5 (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup (Lattices.SqClass (v.adicCompletion ℚ)) :=
  (pSq5 p hp v).map (Lattices.sqClassHom _)

/-- Helper: a square class lies in `sqH5` iff the element lies in `pSq5` (as `pSq5` contains the squares). -/
theorem mk_mem_sqH5 (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (a : (v.adicCompletion ℚ)ˣ) :
    Lattices.SqClass.mk a ∈ sqH5 p hp v ↔ a ∈ pSq5 p hp v := by
  constructor
  · rintro ⟨b, hb, hba⟩
    rw [Lattices.sqClassHom_apply] at hba
    have h1 : Lattices.sqClassHom _ (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, Lattices.sqClassHom_apply, Lattices.sqClassHom_apply, hba, mul_inv_cancel]
    rw [Lattices.sqClassHom_apply] at h1
    obtain ⟨y, hy⟩ := (Lattices.SqClass.mk_eq_one_iff _).mp h1
    have : a = b * y ^ 2 := by rw [hy, mul_left_comm, mul_inv_cancel, mul_one]
    rw [this]
    exact Subgroup.mul_mem _ hb ⟨0, y, by simp⟩
  · intro h
    exact ⟨a, h, by rw [Lattices.sqClassHom_apply]⟩

/-- Helper: a square (as a unit with given square root) lies in `pSq5`. Arguments: `p`, `hp`, `v`, `e` the unit, `s` a
square root of its value (`hs`). -/
theorem mem_pSq5_of_sq (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (e : (v.adicCompletion ℚ)ˣ)
    (s : v.adicCompletion ℚ) (hs : (e : v.adicCompletion ℚ) = s * s) : e ∈ pSq5 p hp v := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact e.ne_zero (by rw [hs]; simp)
  refine ⟨0, Units.mk0 s hs0, Units.ext ?_⟩
  simp [hs, sq]

/-- Helper: $|p|_v = e^{-1}$ at a place $v$ over $p$. Arguments: `p` (`hp`), `v` (`hv`). -/
theorem valued_p5 (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : Rat.HeightOneSpectrum.natGenerator v = p) :
    Valued.v (p : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  have hpK : (p : v.adicCompletion ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h1 := (Lattices.valued_intCast_le_iff v (p : ℤ) 1).mpr (by rw [hv]; simp)
  have h2' : ¬ Valued.v ((p : ℤ) : v.adicCompletion ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [Lattices.valued_intCast_le_iff, hv]
    intro hd
    have h3 : p ^ 2 ∣ p := by exact_mod_cast hd
    have h4 := Nat.le_of_dvd hp.pos h3
    nlinarith [hp.two_le]
  have hne : Valued.v (p : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hpK
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (p : v.adicCompletion ℚ) = WithZero.exp n :=
    ⟨_, (WithZero.exp_log hne).symm⟩
  simp only [Int.cast_natCast] at h1 h2'
  rw [hn] at h1 h2' ⊢
  rw [WithZero.exp_le_exp] at h1 h2'
  push_cast at h1 h2'
  rw [WithZero.exp_inj]
  omega

/-- Helper: a unit of the completion at a place $v$ over $p$ lying in `pSq5` is a square (if $u = p^k w^2$ then
$k$ is even, by absolute values). Arguments: `p`, `hp`, `v`, `hv`, `u` (`hu`: a unit; `hmem`: in `pSq5`). -/
theorem isSquare_of_mem_pSq5 (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : Rat.HeightOneSpectrum.natGenerator v = p) (u : (v.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) (hmem : u ∈ pSq5 p hp v) :
    IsSquare (u : v.adicCompletion ℚ) := by
  have hpK : (p : v.adicCompletion ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hvp := valued_p5 p hp v hv
  obtain ⟨k, w, huw⟩ := hmem
  have hvw : Valued.v (w : v.adicCompletion ℚ) = WithZero.exp (WithZero.log (Valued.v (w : v.adicCompletion ℚ))) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr w.ne_zero)).symm
  set m := WithZero.log (Valued.v (w : v.adicCompletion ℚ)) with hm
  have hue : (u : v.adicCompletion ℚ) = (p : v.adicCompletion ℚ) ^ k * (w : v.adicCompletion ℚ) ^ 2 := by
    rw [huw]; simp
  have hv1 := hu
  rw [hue, map_mul, map_zpow₀, map_pow, hvp, hvw, sq, ← WithZero.exp_zsmul, ← WithZero.exp_add,
    ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at hv1
  have hk : k = m + m := by simp at hv1; omega
  refine ⟨(p : v.adicCompletion ℚ) ^ m * (w : v.adicCompletion ℚ), ?_⟩
  rw [hue, hk, _root_.zpow_add₀ hpK]
  ring

/-- Helper: every element of $\mathbb Q_v^\times$ is $p^{-m}$ times a unit (the unit part). Arguments: `p`, `hp`, `v`, `hv`,
`a`. The element $a p^m$, $m = \log|a|$, has absolute value $1$. -/
theorem valued_unitPart5 (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : Rat.HeightOneSpectrum.natGenerator v = p) (a : (v.adicCompletion ℚ)ˣ) :
    ∃ m : ℤ, Valued.v (((a * (Units.mk0 (p : v.adicCompletion ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)) ^ m :
      (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
  have hvp := valued_p5 p hp v hv
  have ha : Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (WithZero.log (Valued.v (a : v.adicCompletion ℚ))) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr a.ne_zero)).symm
  refine ⟨WithZero.log (Valued.v (a : v.adicCompletion ℚ)), ?_⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, ha, Units.val_mk0, hvp,
    ← WithZero.exp_zsmul, ← WithZero.exp_add, ← WithZero.exp_zero]
  congr 1
  simp

/-- Helper: $p \in \theta(\Lambda_v)$ for every place $v$ (the symmetries in $e_0$ and $e_1$, of values $1$ and $p$).
Arguments: `p` (`hp`), `v`. -/
theorem p_mem_theta5 (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Units.mk0 (p : v.adicCompletion ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero) ∈
      Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero) v
        Lattices.stdLat := by
  have hp0 := hp.ne_zero
  have hpK : (p : v.adicCompletion ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hv2 : Valued.v (2 : v.adicCompletion ℚ) ≤ 1 := by simpa using valued_nat_le5 v 2
  have hxv : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 0 1) = 1 := by
    rw [evalIn_ex5Q]; simp
  have hx0 : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 0 1) ≠ 0 := by
    rw [hxv]; exact one_ne_zero
  have hyv : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 1 1) = p := by
    rw [evalIn_ex5Q]; simp
  have hy0 : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 1 1) ≠ 0 := by
    rw [hyv]; exact hpK
  have hyM : (Pi.single 1 1 : Fin 3 → v.adicCompletion ℚ) ∈
      Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1 := by
    rw [loc_std5]; exact Lattices.single_mem_std 1 (by simp)
  have hys := symm_stab5 p v hyM hy0 (fun z hz => by
    rw [Lattices.mem_std_iff] at hz
    have hq : Lattices.qbil ((ex5Form p).map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) (Pi.single 1 1) z =
        (p : v.adicCompletion ℚ) * (2 * z 1) := by
      rw [qbil_ex5]; simp
      try ring
    rw [hq, hyv, map_mul, map_mul]
    have h1 : Valued.v (2 : v.adicCompletion ℚ) * Valued.v (z 1) ≤ 1 :=
      (mul_le_mul' hv2 (hz 1)).trans (by simp)
    calc Valued.v (p : v.adicCompletion ℚ) * (Valued.v (2 : v.adicCompletion ℚ) * Valued.v (z 1))
        ≤ Valued.v (p : v.adicCompletion ℚ) * 1 := mul_le_mul_right h1 _
      _ = _ := mul_one _)
  refine Lattices.mem_localSpinorNormGroup_of_symm_pair (nondegenerate_ex5f p hp0) Lattices.stdLat hx0 hy0
    (symm_e0_stab5 p v) hys _ ?_
  rw [hxv, hyv, one_mul, Lattices.sqClassOf_of_ne_zero hpK]

/-- Helper (Hensel): at a place $v$ over an odd prime $p$, an integer $n$ congruent to $c^2$ modulo $p$ with $p \nmid c$
is a square in $\mathbb Q_v$. Arguments: `p` (`hp2`: odd), `v` (`hv`), `n`, `c` (`hc`: $p \nmid c$), `h`: $p \mid n - c^2$. -/
theorem isSquare_intCast5 (p : ℕ) (hp2 : p ≠ 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : Rat.HeightOneSpectrum.natGenerator v = p) (n : ℤ) (c : ℕ) (hc : ¬ p ∣ c)
    (h : (p : ℤ) ∣ n - (c : ℤ) ^ 2) : IsSquare (n : v.adicCompletion ℚ) := by
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h => by
    have := (Lattices.two_mem_iff_natGenerator v).mp h
    omega
  have hcv : Valued.v ((c : ℕ) : v.adicCompletion ℚ) = 1 := valued_nat5 v _ (by rw [hv]; exact hc)
  have hcK : ((c : ℕ) : v.adicCompletion ℚ) ≠ 0 := fun h => by
    rw [h, map_zero] at hcv; exact zero_ne_one hcv
  have hle := (Lattices.valued_intCast_le_iff v (n - (c : ℤ) ^ 2) 1).mpr (by rw [hv]; simpa using h)
  set cK : v.adicCompletion ℚ := ((c : ℕ) : v.adicCompletion ℚ) with hcKdef
  have ht : Valued.v ((n : v.adicCompletion ℚ) * (cK ^ 2)⁻¹ - 1) < 1 := by
    have e : (n : v.adicCompletion ℚ) * (cK ^ 2)⁻¹ - 1 =
        (((n - (c : ℤ) ^ 2 : ℤ)) : v.adicCompletion ℚ) * (cK ^ 2)⁻¹ := by
      push_cast
      rw [← hcKdef]
      field_simp
    rw [e, map_mul, map_inv₀, map_pow, hcv, one_pow, inv_one, mul_one]
    exact lt_of_le_of_lt (by simpa using hle) Lattices.exp_neg_one_lt_one
  obtain ⟨s, hs⟩ := Lattices.isSquare_of_val_sub_one_lt_odd (v := v) h2 ht
  refine ⟨s * cK, ?_⟩
  have : (n : v.adicCompletion ℚ) = ((n : v.adicCompletion ℚ) * (cK ^ 2)⁻¹) * cK ^ 2 := by field_simp
  rw [this, hs]; ring

/-- Helper: $2$ is a square in $\mathbb Q_v$ for a place $v$ over a prime $p \equiv 1 \pmod 8$. Arguments: `p` (`hp`,
`hp8`), `v` (`hv`). -/
theorem isSquare_two5 (p : ℕ) (hp : p.Prime) (hp8 : p % 8 = 1) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : Rat.HeightOneSpectrum.natGenerator v = p) : IsSquare (2 : v.adicCompletion ℚ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨c, hc⟩ : IsSquare (2 : ZMod p) := (ZMod.exists_sq_eq_two_iff hp2).mpr (Or.inl hp8)
  have hcn : ((c.val : ℕ) : ZMod p) = c := ZMod.natCast_zmod_val c
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using hc
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hnd : ¬ p ∣ c.val := fun h => hc0 (by rw [← hcn]; exact (ZMod.natCast_eq_zero_iff _ _).mpr h)
  have := isSquare_intCast5 p hp2 v hv 2 c.val hnd (by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcn]; linear_combination hc)
  simpa using this

/-- Helper: there is a natural number that is a quadratic nonresidue modulo the odd prime `p`. Arguments: `p` (`hp`,
`hp2`). -/
theorem exists_nonres5 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ∃ n₀ : ℕ, ¬ IsSquare ((n₀ : ℕ) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  exact ⟨a.val, by rwa [ZMod.natCast_zmod_val]⟩

/-- Helper: a residue nonsquare modulo $p$ (`h`) is a nonsquare in $\mathbb Q_v$, $v \mid p$. Arguments: `p` (`hp`), `v`
(`hv`), `n₀` (`h`). -/
theorem not_isSquare_nonres5 (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : Rat.HeightOneSpectrum.natGenerator v = p) (n₀ : ℕ) (h : ¬ IsSquare ((n₀ : ℕ) : ZMod p)) :
    ¬ IsSquare ((n₀ : ℕ) : v.adicCompletion ℚ) := by
  have : Fact p.Prime := ⟨hp⟩
  rintro ⟨y, hy⟩
  have hn : ¬ p ∣ n₀ := fun hd => h ⟨0, by rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd]; simp⟩
  have hv1 : Valued.v ((n₀ : ℕ) : v.adicCompletion ℚ) = 1 := valued_nat5 v n₀ (by rw [hv]; exact hn)
  have hyy : Valued.v y * Valued.v y = 1 := by rw [← map_mul, ← hy]; exact hv1
  have hy0 : Valued.v y ≠ 0 := fun h0 => by rw [h0, mul_zero] at hyy; exact zero_ne_one hyy
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hy0).symm⟩
  rw [hm, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at hyy
  have hm0 : m = 0 := by omega
  have hy1 : Valued.v y ≤ 1 := by rw [hm, hm0, WithZero.exp_zero]
  obtain ⟨z, hz⟩ := Lattices.exists_int_approx v y hy1
  have hyz : Valued.v (y + (z : v.adicCompletion ℚ)) ≤ 1 :=
    (Valuation.map_add _ _ _).trans (max_le hy1 (Lattices.valued_intCast_le_one' v z))
  have hdiff : Valued.v ((((n₀ : ℕ) : ℤ) - z ^ 2 : ℤ) : v.adicCompletion ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : ((((n₀ : ℕ) : ℤ) - z ^ 2 : ℤ) : v.adicCompletion ℚ) =
        (y - (z : v.adicCompletion ℚ)) * (y + (z : v.adicCompletion ℚ)) := by
      push_cast
      linear_combination hy
    rw [e, map_mul]
    calc Valued.v (y - (z : v.adicCompletion ℚ)) * Valued.v (y + (z : v.adicCompletion ℚ))
        ≤ WithZero.exp (-((1 : ℕ) : ℤ)) * 1 := mul_le_mul' hz hyz
      _ = _ := mul_one _
  have hd := (Lattices.valued_intCast_le_iff v _ 1).mp hdiff
  rw [hv] at hd
  rw [pow_one] at hd
  apply h
  refine ⟨(z : ZMod p), ?_⟩
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
  push_cast at this
  linear_combination this

/-- Helper: at a place $v$ over an odd prime $p$, with `n₀` a nonresidue, a unit $z$ of $\mathbb Q_v$ has $z$ or $n_0z$ a
square. Arguments: `p` (`hp`, `hp2`), `v` (`hv`), `n₀` (`hn`: nonresidue), `z` (`hz`: absolute value $1$). -/
theorem unit_sq_or5 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : Rat.HeightOneSpectrum.natGenerator v = p) (n₀ : ℕ) (hn : ¬ IsSquare ((n₀ : ℕ) : ZMod p))
    (z : v.adicCompletion ℚ) (hz : Valued.v z = 1) :
    IsSquare z ∨ IsSquare (((n₀ : ℕ) : v.adicCompletion ℚ) * z) := by
  have : Fact p.Prime := ⟨hp⟩
  have hz0 : z ≠ 0 := fun h => by rw [h, map_zero] at hz; exact zero_ne_one hz
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h => by
    have := (Lattices.two_mem_iff_natGenerator v).mp h
    omega
  have hcm : Lattices.casselsMod v = p := by
    unfold Lattices.casselsMod; simp [h2, hv]
  obtain ⟨a, hcop, hsq⟩ := Lattices.exists_res v z hz
  rw [hcm] at hcop hsq
  have hnd : ¬ p ∣ a := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop.symm
  have ha0 : ((a : ℕ) : ZMod p) ≠ 0 := fun h => hnd ((ZMod.natCast_eq_zero_iff a p).mp h)
  have key : ∀ (s : ℤ) (c : ZMod p), ((a : ℕ) : ZMod p) = (s : ZMod p) * c ^ 2 →
      IsSquare ((s : v.adicCompletion ℚ) * z) := by
    intro s c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply ha0
      rw [hc]; simp
    have hcn : ((c.val : ℕ) : ZMod p) = c := ZMod.natCast_zmod_val c
    have hnd' : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ c.val := by
      rw [hv]
      intro h
      exact hc0 (by rw [← hcn]; exact (ZMod.natCast_eq_zero_iff _ _).mpr h)
    have hcK1 := Lattices.valued_natCast_eq_one' (v := v) hnd'
    have hcK : ((c.val : ℕ) : v.adicCompletion ℚ) ≠ 0 := fun h => by
      rw [Rat.cast_natCast, h, map_zero] at hcK1; exact zero_ne_one hcK1
    have hmod : s * ((c.val : ℕ) : ℤ) ^ 2 ≡ (a : ℤ) [ZMOD (p : ℤ)] := by
      refine (ZMod.intCast_eq_intCast_iff _ _ p).mp ?_
      push_cast
      rw [hcn, hc]
    have := hsq _ hmod
    refine isSquare_aux z ((c.val : ℕ) : v.adicCompletion ℚ) (s : v.adicCompletion ℚ) _ hz0 hcK ?_ this
    push_cast; ring
  by_cases hs : IsSquare ((a : ℕ) : ZMod p)
  · left
    obtain ⟨c, hc⟩ := hs
    have := key 1 c (by rw [hc]; push_cast; ring)
    simpa using this
  · right
    have hn0 : ((n₀ : ℕ) : ZMod p) ≠ 0 := fun h => hn ⟨0, by rw [h]; simp⟩
    have hqa : quadraticChar (ZMod p) ((a : ℕ) : ZMod p) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hs
    have hqn : quadraticChar (ZMod p) ((n₀ : ℕ) : ZMod p) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hn
    have hsq2 : IsSquare (((n₀ : ℕ) : ZMod p) * ((a : ℕ) : ZMod p)) := by
      refine (quadraticChar_one_iff_isSquare (mul_ne_zero hn0 ha0)).mp ?_
      rw [map_mul, hqa, hqn]; norm_num
    obtain ⟨d, hd⟩ := hsq2
    have := key (n₀ : ℤ) (d / (n₀ : ZMod p)) (by
      push_cast
      field_simp
      linear_combination hd)
    simpa using this

/-- Helper: the unit of $\mathbb Q_v$ given by a nonzero natural number. Arguments: `v`, `n₀` (`h`: nonzero). -/
def natUnit5 (v : HeightOneSpectrum (𝓞 ℚ)) (n₀ : ℕ) (h : n₀ ≠ 0) : (v.adicCompletion ℚ)ˣ :=
  Units.mk0 (n₀ : v.adicCompletion ℚ) (Nat.cast_ne_zero.mpr h)

/-- Helper: a commutative-group identity. Arguments: `a c n`. -/
theorem aux_comm5 {G : Type*} [CommGroup G] (a c n : G) : a * c * n * n⁻¹ ^ 2 * c⁻¹ = a * n⁻¹ := by
  simp [pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- Helper: modulo $\theta(\Lambda_v)$ every element of $\mathbb Q_v^\times$ ($v \mid p$, `n₀` a nonresidue) is $1$ or $n_0$:
$a \in \theta$ or $a n_0^{-1} \in \theta$ (the unit part of $a$ is a square or $n_0$ times a square, and $p \in \theta$). -/
theorem theta5_cases (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : Rat.HeightOneSpectrum.natGenerator v = p) (n₀ : ℕ) (hn : ¬ IsSquare ((n₀ : ℕ) : ZMod p))
    (hn0 : n₀ ≠ 0) (a : (v.adicCompletion ℚ)ˣ) :
    a ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero) v
        Lattices.stdLat ∨
      a * (natUnit5 v n₀ hn0)⁻¹ ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ))
        (nondegenerate_ex5f p hp.ne_zero) v Lattices.stdLat := by
  obtain ⟨m, hm⟩ := valued_unitPart5 p hp v hv a
  set Pu : (v.adicCompletion ℚ)ˣ := Units.mk0 (p : v.adicCompletion ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero) with hPu
  have hPm : Pu ^ m ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ))
      (nondegenerate_ex5f p hp.ne_zero) v Lattices.stdLat := Subgroup.zpow_mem _ (p_mem_theta5 p hp v) m
  have hPm' := Subgroup.inv_mem _ hPm
  rcases unit_sq_or5 p hp hp2 v hv n₀ hn _ hm with ⟨s, hs⟩ | ⟨s, hs⟩
  · left
    have hsu : (a * Pu ^ m) ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ))
        (nondegenerate_ex5f p hp.ne_zero) v Lattices.stdLat := by
      refine mem_theta5_of_sq p hp.ne_zero ((Lattices.SqClass.mk_eq_one_iff _).mpr ?_)
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact (a * Pu ^ m).ne_zero (by rw [hs]; simp)
      exact ⟨Units.mk0 s hs0, Units.ext (by simp [hs, sq])⟩
    have := Subgroup.mul_mem _ hsu hPm'
    rwa [show a * Pu ^ m * (Pu ^ m)⁻¹ = a by group] at this
  · right
    have hs0 : s ≠ 0 := by
      rintro rfl
      have : ((n₀ : ℕ) : v.adicCompletion ℚ) * ((a * Pu ^ m : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 0 := by
        rw [hs]; simp
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hn0) (a * Pu ^ m).ne_zero this
    have e1 : (a * Pu ^ m) * natUnit5 v n₀ hn0 ∈ Lattices.localSpinorNormGroup
        ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero) v Lattices.stdLat := by
      refine mem_theta5_of_sq p hp.ne_zero ((Lattices.SqClass.mk_eq_one_iff _).mpr ⟨Units.mk0 s hs0, Units.ext ?_⟩)
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
      rw [sq, ← hs, Units.val_mul (a * Pu ^ m) (natUnit5 v n₀ hn0)]
      simp only [natUnit5, Units.val_mk0]
      ring
    have e2 : (natUnit5 v n₀ hn0)⁻¹ ^ 2 ∈ Lattices.localSpinorNormGroup
        ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero) v Lattices.stdLat :=
      mem_theta5_of_sq p hp.ne_zero ((Lattices.SqClass.mk_eq_one_iff _).mpr ⟨_, rfl⟩)
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ e1 e2) hPm'
    rwa [aux_comm5] at this

/-! ### The group $G = R/ST$ has order $2$ -/

/-- **$|G| = 2$ for $p \equiv 1 \pmod 8$** (Cassels, Ch. 11, Example 5, $P = \{2, p\}$): Cassels' group $G = R/ST$ of
(3.15) for $f = x_0^2 + p x_1^2 - p^2x_2^2$ has exactly two elements. Arguments: `p` the prime (`hp`, `hp2`: odd,
`h8`: $p \equiv 1 \bmod 8$). -/
theorem ex5_card_casselsG (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h8 : p % 8 = 1) :
    Nat.card (Lattices.CasselsG ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero)
      Lattices.stdLat (ex5P p hp)) = 2 := by
  classical
  have hp0 := hp.ne_zero
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n₀, hn⟩ := exists_nonres5 p hp hp2
  have hn0 : n₀ ≠ 0 := by rintro rfl; exact hn ⟨0, by simp⟩
  have hnd : ¬ p ∣ n₀ := fun hd => hn ⟨0, by rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd]; simp⟩
  have hpP : ratPlace p hp ∈ ex5P p hp := (mem_ex5P p hp _).mpr (Or.inr (natGenerator_ratPlace p hp))
  let q : ex5P p hp := ⟨ratPlace p hp, hpP⟩
  have hq : Rat.HeightOneSpectrum.natGenerator q.1 = p := natGenerator_ratPlace p hp
  have hcases : ∀ v : ex5P p hp, v = q ∨ Rat.HeightOneSpectrum.natGenerator v.1 = 2 := by
    intro v
    rcases (mem_ex5P p hp v.1).mp v.2 with h | h
    · exact Or.inr h
    · exact Or.inl (Subtype.ext (Lattices.natGenerator_inj' (h.trans hq.symm)))
  let x₀ : Lattices.CasselsR (ex5P p hp) := Pi.mulSingle q (natUnit5 q.1 n₀ hn0)
  have hx₀q : x₀ q = natUnit5 q.1 n₀ hn0 := Pi.mulSingle_eq_same _ _
  have hx₀ne : ∀ v : ex5P p hp, v ≠ q → x₀ v = 1 := fun v hv => Pi.mulSingle_eq_of_ne hv _
  have hnatv : Valued.v ((natUnit5 q.1 n₀ hn0 : (q.1.adicCompletion ℚ)ˣ) : q.1.adicCompletion ℚ) = 1 :=
    valued_nat5 q.1 n₀ (by rw [hq]; exact hnd)
  have hnot : x₀ ∉ Lattices.casselsST ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp0)
      Lattices.stdLat (ex5P p hp) := by
    refine ConwaySloane.not_mem_casselsST_of_subgroup _ (nondegenerate_ex5f p hp0) Lattices.stdLat (ex5P p hp)
      (by norm_num) q (sqH5 p hp q.1) ?_ ?_ ?_ ?_ ?_ ?_
    · -- the class of `p`
      have hpu : ((ConwaySloane.primeUnit (ex5P p hp) q : (q.1.adicCompletion ℚ)ˣ) : q.1.adicCompletion ℚ) =
          (p : q.1.adicCompletion ℚ) := by
        rw [ConwaySloane.primeUnit, Lattices.casselsDiag_apply]
        simp [Lattices.natGenUnit, hq]
      refine (mk_mem_sqH5 p hp q.1 _).mpr ⟨1, 1, Units.ext ?_⟩
      rw [hpu]; simp
    · -- (a) spinor norms at `p`
      intro A hA
      refine (mk_mem_sqH5 p hp q.1 _).mpr ?_
      obtain ⟨m, hm⟩ := valued_unitPart5 p hp q.1 hq A
      set Pu : (q.1.adicCompletion ℚ)ˣ :=
        Units.mk0 (p : q.1.adicCompletion ℚ) (Nat.cast_ne_zero.mpr hp0) with hPu
      have hθ : A * Pu ^ m ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ))
          (nondegenerate_ex5f p hp0) q.1 Lattices.stdLat :=
        Subgroup.mul_mem _ hA (Subgroup.zpow_mem _ (p_mem_theta5 p hp q.1) m)
      have hsq : IsSquare (((A * Pu ^ m : (q.1.adicCompletion ℚ)ˣ)) : q.1.adicCompletion ℚ) := by
        by_contra hns
        exact nonsquare_unit_not_mem_theta5 p hp h8 q.1 hq _ hm hns hθ
      obtain ⟨s, hs⟩ := hsq
      have h1 : A * Pu ^ m ∈ pSq5 p hp q.1 := mem_pSq5_of_sq p hp q.1 _ s hs
      have h2 : Pu ^ m ∈ pSq5 p hp q.1 := ⟨m, 1, by simp [hPu]⟩
      have := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      rwa [show A * Pu ^ m * (Pu ^ m)⁻¹ = A by group] at this
    · -- (b) the place `2`
      intro p' hp'q A _
      refine (mk_mem_sqH5 p hp q.1 _).mpr ?_
      have h2 : Rat.HeightOneSpectrum.natGenerator p'.1 = 2 := (hcases p').resolve_left hp'q
      obtain ⟨s, hs⟩ := isSquare_two5 p hp h8 q.1 hq
      refine mem_pSq5_of_sq p hp q.1 _ (s ^ ConwaySloane.ordP (ex5P p hp) p' A) ?_
      have h2' : ((Lattices.natGenUnit p'.1 : ℚˣ) : ℚ) = 2 := by simp [Lattices.natGenUnit, h2]
      rw [Lattices.casselsDiag_apply, Units.val_zpow_eq_zpow_val, h2', map_zpow₀, map_ofNat, hs, mul_zpow]
    · -- (c) Cassels' `j = -1`
      have hj : Lattices.casselsJ ((ex5Form p).map (Int.castRingHom ℚ)) = -1 := by
        unfold Lattices.casselsJ; rw [if_pos (isIndefinite_ex5f p hp0)]
      obtain ⟨s, hs⟩ := isSquare_neg_one5 p hp (by omega) q.1 hq
      refine (mk_mem_sqH5 p hp q.1 _).mpr (mem_pSq5_of_sq p hp q.1 _ s ?_)
      rw [hj, Lattices.casselsDiag_apply]
      simpa using hs
    · -- `x₀` is a family of units
      intro v
      by_cases hv : v = q
      · subst hv; rw [hx₀q]; exact hnatv
      · rw [hx₀ne v hv]; simp
    · rw [hx₀q, mk_mem_sqH5]
      intro h
      exact not_isSquare_nonres5 p hp q.1 hq n₀ hn (isSquare_of_mem_pSq5 p hp q.1 hq _ hnatv h)
  have hupper : ∀ r : Lattices.CasselsR (ex5P p hp),
      r ∈ Lattices.casselsS ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp0) Lattices.stdLat
          (ex5P p hp) ∨
        r * x₀⁻¹ ∈ Lattices.casselsS ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp0)
          Lattices.stdLat (ex5P p hp) := by
    intro r
    rcases theta5_cases p hp hp2 q.1 hq n₀ hn hn0 (r q) with h | h
    · left
      rw [Lattices.casselsS, Subgroup.mem_pi]
      intro v _
      rcases hcases v with hvq | h2
      · subst hvq; exact h
      · exact theta5_two_all p hp hp2 v.1 ((Lattices.two_mem_iff_natGenerator v.1).mpr h2) (r v)
    · right
      rw [Lattices.casselsS, Subgroup.mem_pi]
      intro v _
      show r v * (x₀ v)⁻¹ ∈ _
      rcases hcases v with hvq | h2
      · subst hvq; rw [hx₀q]; exact h
      · have hne : v ≠ q := fun hvq => by
          subst hvq
          rw [hq] at h2
          exact hp2 h2
        rw [hx₀ne v hne, inv_one, mul_one]
        exact theta5_two_all p hp hp2 v.1 ((Lattices.two_mem_iff_natGenerator v.1).mpr h2) (r v)
  rw [Nat.card_eq_two_iff]
  refine ⟨1, QuotientGroup.mk x₀, ?_, ?_⟩
  · intro h
    exact hnot ((QuotientGroup.eq_one_iff _).mp h.symm)
  · ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    induction g using QuotientGroup.induction_on with
    | H r =>
      rcases hupper r with h | h
      · left
        exact (QuotientGroup.eq_one_iff r).mpr (Subgroup.mem_sup_left h)
      · right
        rw [QuotientGroup.eq]
        have := Subgroup.inv_mem _ (Subgroup.mem_sup_left (T := (Lattices.casselsT _ (nondegenerate_ex5f p hp0)
          (ex5P p hp)).map (Lattices.casselsDiag (ex5P p hp))) h)
        rwa [_root_.mul_inv_rev, inv_inv, mul_comm] at this

/-! ### The theorems -/

/-- **Cassels, Ch. 11, Example 5** (p. 252), two-class case, proved: *for a prime $p \equiv 1 \pmod 8$,
$x^2 + py^2 - p^2z^2$ is in a genus of $2$ classes.* The group $G = R/ST$ for $P = \{2, p\}$ has order $2$
(`ex5_card_casselsG`); `Lattices.ncard_genusClasses_eq_two_of_card` ($f$ indefinite in $3$ variables). Arguments: `p`
the prime (`hp`, `hp2`: $p \ne 2$, `h8`: $p \equiv 1 \bmod 8$). -/
@[kb "cassels1978" "Ch. 11, Ex. 5, p. 252 (p ≡ 1 mod 8: two classes)"]
theorem ex5_two_classes (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h8 : p % 8 = 1) :
    (genusClasses (ex5Form p)).ncard = 2 := by
  have hp0 := hp.ne_zero
  have hf : (ex5Form p).hessian.det ≠ 0 := by
    rw [hessian_det_ex5f]
    have : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
    simpa using this
  refine Lattices.ncard_genusClasses_eq_two_of_card (ex5Form p) (by norm_num) ⟨1, rfl⟩ hf
    (isIndefinite_ex5f p hp0) (ex5P p hp) ?_ (ex5_card_casselsG p hp hp2 h8)
  intro v hv hd
  have h2 : Rat.HeightOneSpectrum.natGenerator v ≠ 2 := fun h => hv ((mem_ex5P p hp v).mpr (Or.inl h))
  have hpp : Rat.HeightOneSpectrum.natGenerator v ≠ p := fun h => hv ((mem_ex5P p hp v).mpr (Or.inr h))
  have hq := Rat.HeightOneSpectrum.prime_natGenerator v
  rw [hessian_det_ex5f] at hd
  have e : (2 * (-8 * (p : ℤ) ^ 3)).natAbs = 2 ^ 4 * p ^ 3 := by
    have : 2 * (-8 * (p : ℤ) ^ 3) = -((2 ^ 4 * p ^ 3 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.natAbs_neg, Int.natAbs_natCast]
  have hd' : Rat.HeightOneSpectrum.natGenerator v ∣ 2 ^ 4 * p ^ 3 := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    rwa [e, Int.natAbs_natCast] at this
  rcases (Nat.Prime.dvd_mul hq).mp hd' with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  · exact hpp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h))

/-- **Cassels, Ch. 11, Example 5** (p. 252), proved: *for a prime $p > 2$, $x^2 + py^2 - p^2z^2$ is in a genus of $2$
classes if $p \equiv 1 \pmod 8$, otherwise in a genus of $1$ class.* The two fields are `ex5_two_classes` and
`ex5_one_class`. Unconditional. -/
@[kb "cassels1978" "Ch. 11, Ex. 5, p. 252 (proved)"]
theorem ex5Statement_holds : Ex5Statement :=
  ⟨fun p hp hp2 h8 => ex5_two_classes p hp hp2 h8, fun p hp hp2 h8 => ex5_one_class p hp hp2 h8⟩

end QuadFormsKB.Cassels.Ch11Ex4
