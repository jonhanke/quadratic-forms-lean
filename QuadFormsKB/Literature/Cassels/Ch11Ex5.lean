/-
# Cassels, Chapter 11, Example 5: $x^2 + py^2 - p^2z^2$, $p \not\equiv 1 \pmod 8$, has one class

Proves `ex5_one_class`: for a prime $p > 2$ with $p \not\equiv 1 \pmod 8$ the genus of
$f = x_0^2 + p\,x_1^2 - p^2x_2^2$ has exactly one class.

**Route (as for Example 3, `Ch11Ex35.lean`).** With $P = \{2, p\}$ one shows $X \le ST$ for the group $G = R/ST$ of
(3.15) (`casselsX_le_ex5`), i.e. the genus is one proper spinor genus, and then
`ConwaySloane.intEquiv_of_sameGenus_of_casselsX_le` (Theorem 1.4 for indefinite $f$ of dimension $3$) gives one class.
The local facts:

* at $2$: $\theta(\Lambda_2) = \mathbb Q_2^\times$ (units by Lemma 3.8, Corollary, as $2^5 \nmid 8p^3$; and $2$ by a pair of
  symmetries: $e_0, e_0 + e_1$ of values $1, 1 + p$ if $p \equiv 1 \pmod 4$, and $e_1, e_1 + e_2$ of values
  $p, p(1-p)$ if $p \equiv 3 \pmod 4$);
* at $p$: every unit $z$ has $s\cdot t'\cdot z$ a square for some $s \in \{1, -1\}$, $t' \in \{1, 2\}$, where $s = -1$
  occurs only for $p \equiv 3 \pmod 4$, in which case $-1 \in \theta(\Lambda_p)$ (the symmetries in $e_0, e_2$, of values
  $1, -p^2$), and $t'=2$ only for $p \equiv 5 \pmod 8$ (then $2$ is a nonsquare modulo $p$).

**Local facts for the two-class case $p \equiv 1 \pmod 8$** (to be used by the count of proper spinor genera, $G = R/ST$):
`theta5_two_all` ($\theta(\Lambda_2) = \mathbb Q_2^\times$, any odd $p$) and `nonsquare_unit_not_mem_theta5`
($p \equiv 1 \bmod 8$, $v \mid p$: a nonsquare unit of $\mathbb Q_v$ is not in $\theta(\Lambda_v)$, from Example 4,
`ex4Statement_holds`, with the standard basis of values $1, p, -p^2$ and the fact that $-1$ is a square in $\mathbb Q_v$,
`isSquare_neg_one5`).
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex35

open Matrix NumberField IsDedekindDomain QuadFormsKB.Siegel

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Ex4

open QuadFormsKB

/-! ### Elementary facts about $f = x_0^2 + p x_1^2 - p^2 x_2^2$ -/

/-- Helper: $x_0^2 + p x_1^2 - p^2 x_2^2$ over a field containing $\mathbb Z$. Arguments: `p` the prime, `x` the vector. -/
theorem evalIn_ex5f {K : Type*} [Field K] [Algebra ℤ K] (p : ℕ) (x : Fin 3 → K) :
    (ex5Form p).evalIn K x = x 0 ^ 2 + (p : K) * x 1 ^ 2 - (p : K) ^ 2 * x 2 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_three, ex5Form, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: the same over a $\mathbb Q$-algebra field, for the rational form. Arguments: `p`, `x`. -/
theorem evalIn_ex5Q {K : Type*} [Field K] [Algebra ℚ K] (p : ℕ) (x : Fin 3 → K) :
    ((ex5Form p).map (Int.castRingHom ℚ)).evalIn K x = x 0 ^ 2 + (p : K) * x 1 ^ 2 - (p : K) ^ 2 * x 2 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_three, ex5Form, QuadForm.map, QuadForm.diag, Matrix.diagonal_apply]
  ring

/-- Helper: $\det H = -8p^3$. Argument `p`. -/
theorem hessian_det_ex5f (p : ℕ) : (ex5Form p).hessian.det = -8 * (p : ℤ) ^ 3 := by
  rw [ex5Form, Ch11Wave6.hessian_diag, det_diagonal, Fin.prod_univ_three]
  simp
  ring

/-- Helper: $f$ is indefinite over $\mathbb Q$ for $p \ne 0$. Argument `p` (`hp`: nonzero). -/
theorem isIndefinite_ex5f (p : ℕ) (hp : p ≠ 0) :
    Lattices.IsIndefinite ((ex5Form p).map (Int.castRingHom ℚ)) := by
  have : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  refine Lattices.isIndefinite_of_neg_pos (ex5Form p) ![0, 0, 1] ![1, 0, 0] ?_ ?_
  · rw [evalIn_ex5f]; simp; positivity
  · rw [evalIn_ex5f]; simp

/-- Helper: $f$ is nondegenerate over $\mathbb Q$ for $p \ne 0$. Argument `p` (`hp`: nonzero). -/
theorem nondegenerate_ex5f (p : ℕ) (hp : p ≠ 0) : ((ex5Form p).map (Int.castRingHom ℚ)).Nondegenerate :=
  Lattices.nondegenerate_map_of_det_ne_zero (ex5Form p) (by
    rw [hessian_det_ex5f]; have : (p : ℤ) ≠ 0 := by exact_mod_cast hp
    simpa using this)

/-! ### Residues modulo $p$ -/

/-- Helper: a nonzero residue modulo an odd prime $p \not\equiv 1 \pmod 8$ is a square, or $-1$ times a square
(then $p \equiv 3 \pmod 4$), or $2$ times a square (then $p \equiv 5 \pmod 8$). Arguments: `p` the prime (`hp2`: odd,
`h8`: $p \not\equiv 1 \bmod 8$), `a` the residue (`ha`: nonzero). -/
theorem zmod_class (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (h8 : p % 8 ≠ 1) (a : ZMod p) (ha : a ≠ 0) :
    (∃ c : ZMod p, a = 1 * c ^ 2) ∨ (p % 4 = 3 ∧ ∃ c : ZMod p, a = -1 * c ^ 2) ∨
      (p % 8 = 5 ∧ ∃ c : ZMod p, a = 2 * c ^ 2) := by
  have hpr : p.Prime := Fact.out
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hpr).mpr hp2
  by_cases hs : IsSquare a
  · obtain ⟨c, hc⟩ := hs
    exact Or.inl ⟨c, by rw [hc]; ring⟩
  right
  have hqa : quadraticChar (ZMod p) a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hs
  by_cases h4 : p % 4 = 3
  · left
    refine ⟨h4, ?_⟩
    have hn : ¬ IsSquare (-1 : ZMod p) := fun h => (ZMod.exists_sq_eq_neg_one_iff.mp h) h4
    have hq1 : quadraticChar (ZMod p) (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hn
    have hsq : IsSquare (-1 * a) := by
      refine (quadraticChar_one_iff_isSquare (mul_ne_zero (by simp) ha)).mp ?_
      rw [map_mul, hq1, hqa]; norm_num
    obtain ⟨d, hd⟩ := hsq
    exact ⟨d, by linear_combination (-1) * hd⟩
  · right
    have h85 : p % 8 = 5 := by omega
    refine ⟨h85, ?_⟩
    have hn : ¬ IsSquare (2 : ZMod p) := fun h => by
      have := (ZMod.exists_sq_eq_two_iff hp2).mp h
      omega
    have hq1 : quadraticChar (ZMod p) 2 = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hn
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp h')
    have hsq : IsSquare (2 * a) := by
      refine (quadraticChar_one_iff_isSquare (mul_ne_zero h20 ha)).mp ?_
      rw [map_mul, hq1, hqa]; norm_num
    obtain ⟨d, hd⟩ := hsq
    refine ⟨d / 2, ?_⟩
    field_simp
    linear_combination hd

/-- Helper: at the place `v` over $p$, a unit $z$ of the completion has $s z$ a square for some $s \in \{1, -1, 2\}$,
where $s = -1$ forces $p \equiv 3 \pmod 4$ and $s = 2$ forces $p \equiv 5 \pmod 8$. Arguments: `p` the prime (`hp`,
`hp2`: odd, `h8`: $p \not\equiv 1 \bmod 8$), `v` the place (`hv`: its prime is $p$), `z` the unit (`hz`: absolute
value $1$). -/
theorem exists_sign_mul_isSquare (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h8 : p % 8 ≠ 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : Rat.HeightOneSpectrum.natGenerator v = p)
    (z : v.adicCompletion ℚ) (hz : Valued.v z = 1) :
    ∃ s : ℤ, (s = 1 ∨ (s = -1 ∧ p % 4 = 3) ∨ (s = 2 ∧ p % 8 = 5)) ∧ IsSquare ((s : v.adicCompletion ℚ) * z) := by
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
  rcases zmod_class p hp2 h8 _ ha0 with ⟨c, hc⟩ | ⟨h4, c, hc⟩ | ⟨h5, c, hc⟩
  · exact ⟨1, Or.inl rfl, key 1 c (by rw [hc]; push_cast; ring)⟩
  · exact ⟨-1, Or.inr (Or.inl ⟨rfl, h4⟩), key (-1) c (by rw [hc]; push_cast; ring)⟩
  · exact ⟨2, Or.inr (Or.inr ⟨rfl, h5⟩), key 2 c (by rw [hc]; push_cast; ring)⟩

/-! ### The local spinor norm groups -/

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- Helper: $\theta(\Lambda_v)$ depends only on square classes. Arguments: `p` (`hp0`: nonzero), `v` the place, `a b`
the units (`ha`: $a \in \theta$, `h`: same square class). -/
theorem mem_theta5_of_class_eq (p : ℕ) (hp0 : p ≠ 0) {v : HeightOneSpectrum (𝓞 ℚ)} {a b : (v.adicCompletion ℚ)ˣ}
    (ha : a ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp0) v
      Lattices.stdLat)
    (h : Lattices.SqClass.mk b = Lattices.SqClass.mk a) :
    b ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp0) v
      Lattices.stdLat := by
  unfold Lattices.localSpinorNormGroup at ha ⊢
  simp only [Subgroup.mem_comap, Lattices.sqClassHom_apply] at ha ⊢
  rw [h]; exact ha

/-- Helper: an element with trivial square class is in $\theta(\Lambda_v)$. Arguments: `p` (`hp0`), `v`, `a` (`h`). -/
theorem mem_theta5_of_sq (p : ℕ) (hp0 : p ≠ 0) {v : HeightOneSpectrum (𝓞 ℚ)} {a : (v.adicCompletion ℚ)ˣ}
    (h : Lattices.SqClass.mk a = 1) :
    a ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp0) v
      Lattices.stdLat := by
  unfold Lattices.localSpinorNormGroup
  simp only [Subgroup.mem_comap, Lattices.sqClassHom_apply, h]
  exact Subgroup.one_mem _

/-- Helper: at a place $v$ over $2$ (for odd $p$), every unit of the completion is in $\theta(\Lambda_v)$ (Lemma 3.8,
Corollary, since $2^5 \nmid -8p^3$). Arguments: `p` (`hp2`: odd prime), `v` (`h2`: over $2$), `u` (`hu`: a unit). -/
theorem units_mem_theta5_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    u ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero) v
      Lattices.stdLat := by
  refine Ch11Wave6.units_mem_localSpinorNormGroup_two (ex5Form p) (nondegenerate_ex5f p hp.ne_zero) ?_ v h2 u hu
  rintro ⟨-, hd⟩
  have h5 : (Lattices.casselsExpTwo 3 + ((3 : ℕ) : ℤ)).toNat = 5 := by
    unfold Lattices.casselsExpTwo
    norm_num
  rw [h5, hessian_det_ex5f] at hd
  obtain ⟨k, hk⟩ := hd
  have h4 : (2 : ℤ) ∣ (p : ℤ) ^ 3 := ⟨-2 * k, by linarith⟩
  have h2p : (2 : ℤ) ∣ (p : ℤ) := Int.prime_two.dvd_of_dvd_pow h4
  have : 2 ∣ p := by exact_mod_cast h2p
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm

/-- Helper: $f$ evaluated over a $\mathbb Q$-algebra field is as in `evalIn_ex5Q`; the polar form
$B(x, z) = 2(x_0z_0 + p x_1z_1 - p^2x_2z_2)$. Arguments: `p`, `x z`. -/
theorem qbil_ex5 {K : Type*} [Field K] [Algebra ℚ K] (p : ℕ) (x z : Fin 3 → K) :
    Lattices.qbil ((ex5Form p).map (Int.castRingHom ℚ)) K x z =
      2 * (x 0 * z 0 + (p : K) * (x 1 * z 1) - (p : K) ^ 2 * (x 2 * z 2)) := by
  rw [Lattices.qbil_eq_polar, evalIn_ex5Q, evalIn_ex5Q, evalIn_ex5Q]
  simp
  ring

/-- Helper: $\mathrm{loc}_v(\mathbb Z^3)$ is the standard lattice. Argument `v`. -/
theorem loc_std5 (v : HeightOneSpectrum (𝓞 ℚ)) :
    Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1 = Lattices.std v := Lattices.loc_intVec v

/-- Helper: $f$ is integral on $\mathrm{loc}_v(\mathbb Z^3)$. Arguments: `p`, `v`. -/
theorem hint5 (p : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ x ∈ Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1,
      Valued.v (((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x) ≤ 1 := by
  intro x hx; rw [loc_std5] at hx
  convert Lattices.valued_evalIn_le_one_int v (ex5Form p) hx using 3
  exact Subsingleton.elim _ _

/-- Helper: a symmetry in a vector $y \in \Lambda_v$ with $|B(y, z)| \le |Q(y)|$ on $\Lambda_v$ stabilizes it.
Arguments: `p` the prime, `v` the place, `y` (`hyM`: in the lattice, `hy0`: $Q(y) \ne 0$, `hb`: the bound). -/
theorem symm_stab5 (p : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 3 → v.adicCompletion ℚ}
    (hyM : y ∈ Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1)
    (hy0 : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) y ≠ 0)
    (hb : ∀ z ∈ Lattices.std v, Valued.v (Lattices.qbil ((ex5Form p).map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) y z) ≤
      Valued.v (((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) y)) :
    Lattices.symm ((ex5Form p).map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) y ∈
      Lattices.locStabV ((ex5Form p).map (Int.castRingHom ℚ)) v Lattices.stdLat := by
  show Lattices.locAct v (Lattices.symm ((ex5Form p).map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) y :
      GL (Fin 3) (v.adicCompletion ℚ)) (Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1) =
    Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1
  refine Lattices.locAct_symm_eq hyM hy0 fun z hz => hb z ?_
  rwa [loc_std5] at hz

/-- Helper: a natural number prime to the prime of `v` is a unit in the completion. -/
theorem valued_nat5 (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) (h : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ m) :
    Valued.v (m : v.adicCompletion ℚ) = 1 := by
  have := Lattices.valued_natCast_eq_one' (v := v) h
  simpa using this

/-- Helper: $v(n) \le 1$ for a natural number $n$. -/
theorem valued_nat_le5 (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) : Valued.v (m : v.adicCompletion ℚ) ≤ 1 := by
  simpa using Lattices.valued_intCast_le_one' v (m : ℤ)

/-- Helper: from $w \in \theta(\Lambda_v)$ with $w = 2 m r^2$, $m$ a unit and $r \ne 0$, conclude $2 \in \theta$ ($v \mid 2$).
Arguments: `p` (`hp`, `hp2`), `v` (`h2`), `h20` ($2 \ne 0$), `w` (`hw0`, `hw`: in $\theta$), `m` (`hm`: a unit),
`r` (`hr`), `e` the relation. -/
theorem two_mem_of5 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (h20 : (2 : v.adicCompletion ℚ) ≠ 0) (w : v.adicCompletion ℚ) (hw0 : w ≠ 0)
    (hw : Units.mk0 w hw0 ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ))
      (nondegenerate_ex5f p hp.ne_zero) v Lattices.stdLat)
    (m : v.adicCompletion ℚ) (hm : Valued.v m = 1) (r : v.adicCompletion ℚ) (hr : r ≠ 0)
    (e : w = 2 * m * r ^ 2) :
    Units.mk0 (2 : v.adicCompletion ℚ) h20 ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ))
      (nondegenerate_ex5f p hp.ne_zero) v Lattices.stdLat := by
  have hm0 : m ≠ 0 := fun h => by rw [h, map_zero] at hm; exact zero_ne_one hm
  have hmu := units_mem_theta5_two p hp hp2 v h2 (Units.mk0 m hm0) (by simpa using hm)
  have hx := Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hmu)
  refine mem_theta5_of_class_eq p hp.ne_zero hx ?_
  have hxe : Units.mk0 w hw0 * (Units.mk0 m hm0)⁻¹ = Units.mk0 (2 : v.adicCompletion ℚ) h20 * (Units.mk0 r hr) ^ 2 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_pow_eq_pow_val]
    rw [e]; field_simp
  rw [hxe, Lattices.SqClass.mk_mul, (Lattices.SqClass.mk_eq_one_iff _).mpr ⟨Units.mk0 r hr, rfl⟩, mul_one]

/-- Helper: the vector $e_0$ lies in the lattice and has value $1$, so its symmetry stabilizes it. Arguments: `p`
(`hp0`), `v`. -/
theorem symm_e0_stab5 (p : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Lattices.symm ((ex5Form p).map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) (Pi.single 0 1) ∈
      Lattices.locStabV ((ex5Form p).map (Int.castRingHom ℚ)) v Lattices.stdLat := by
  have hxv : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 0 1) = 1 := by
    rw [evalIn_ex5Q]; simp
  have hxM : (Pi.single 0 1 : Fin 3 → v.adicCompletion ℚ) ∈
      Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1 := by
    rw [loc_std5]; exact Lattices.single_mem_std 0 (by simp)
  exact Lattices.symm_mem_locStabV_of_unit Lattices.stdLat (hint5 p v) hxM (by rw [hxv, map_one])

/-- Helper: at a place $v$ over $2$, the element $2$ of the completion is in $\theta(\Lambda_v)$. For
$p \equiv 1 \pmod 4$ the symmetries in $e_0$ (value $1$) and $e_0 + e_1$ (value $1 + p = 2\cdot\frac{p+1}{2}$); for
$p \equiv 3 \pmod 4$ those in $e_1$ (value $p$) and $e_1 + e_2$ (value $p - p^2 = -2\cdot\frac{p-1}{2}\cdot p$). Arguments:
`p` (`hp`, `hp2`: odd prime), `v` (`h2`: over $2$), `h20`: $2 \ne 0$ in the completion. -/
theorem two_mem_theta5 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (h20 : (2 : v.adicCompletion ℚ) ≠ 0) :
    Units.mk0 (2 : v.adicCompletion ℚ) h20 ∈ Lattices.localSpinorNormGroup
      ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero) v Lattices.stdLat := by
  have hng := (Lattices.two_mem_iff_natGenerator v).mp h2
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
  have hp0 := hp.ne_zero
  have hpv : Valued.v (p : v.adicCompletion ℚ) = 1 := valued_nat5 v p (by rw [hng]; omega)
  have hpK : (p : v.adicCompletion ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hv2 : Valued.v (2 : v.adicCompletion ℚ) ≤ 1 := by simpa using valued_nat_le5 v 2
  have hxv : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 0 1) = 1 := by
    rw [evalIn_ex5Q]; simp
  have hx0 : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 0 1) ≠ 0 := by
    rw [hxv]; exact one_ne_zero
  have hmem : ∀ y : Fin 3 → v.adicCompletion ℚ, (∀ i, Valued.v (y i) ≤ 1) →
      y ∈ Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1 := fun y hy => by
    rw [loc_std5, Lattices.mem_std_iff]; exact hy
  have hP : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ 1 → Valued.v ((p : v.adicCompletion ℚ) * y) ≤ 1 := fun y hy => by
    rw [map_mul, hpv, one_mul]; exact hy
  have : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases this with h4 | h4
  · -- the symmetries in `e₀` and `e₀ + e₁`
    set m : ℕ := (p + 1) / 2 with hmdef
    have hm2 : 2 * m = p + 1 := by omega
    have hmK : (1 + (p : v.adicCompletion ℚ)) = 2 * (m : v.adicCompletion ℚ) := by
      have : ((2 * m : ℕ) : v.adicCompletion ℚ) = ((p + 1 : ℕ) : v.adicCompletion ℚ) := by rw [hm2]
      push_cast at this; linear_combination -this
    have hmv : Valued.v (m : v.adicCompletion ℚ) = 1 := valued_nat5 v m (by rw [hng]; omega)
    have hyv : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) ![1, 1, 0] = 2 * m := by
      rw [evalIn_ex5Q, ← hmK]; simp
    have hm0 : (m : v.adicCompletion ℚ) ≠ 0 := fun h => by rw [h, map_zero] at hmv; exact zero_ne_one hmv
    have hy0 : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) ![1, 1, 0] ≠ 0 := by
      rw [hyv]; exact mul_ne_zero h20 hm0
    have hys := symm_stab5 p v (hmem _ (fun i => by fin_cases i <;> simp)) hy0 (fun z hz => by
      rw [Lattices.mem_std_iff] at hz
      have hq : Lattices.qbil ((ex5Form p).map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) ![1, 1, 0] z =
          2 * (z 0 + p * z 1) := by rw [qbil_ex5]; simp
      rw [hq, hyv, map_mul, map_mul, hmv, mul_one]
      have hle : Valued.v (z 0 + (p : v.adicCompletion ℚ) * z 1) ≤ 1 :=
        Valuation.map_add_le _ (hz 0) (hP _ (hz 1))
      calc Valued.v (2 : v.adicCompletion ℚ) * Valued.v (z 0 + (p : v.adicCompletion ℚ) * z 1)
          ≤ Valued.v (2 : v.adicCompletion ℚ) * 1 := mul_le_mul_right hle _
        _ = _ := mul_one _)
    have hw0 : (2 : v.adicCompletion ℚ) * m * 1 ^ 2 ≠ 0 := by simpa using mul_ne_zero h20 hm0
    refine two_mem_of5 p hp hp2 v h2 h20 (2 * m) (by simpa using mul_ne_zero h20 hm0) ?_ m hmv 1 one_ne_zero
      (by ring)
    refine Lattices.mem_localSpinorNormGroup_of_symm_pair (nondegenerate_ex5f p hp0) Lattices.stdLat hx0 hy0
      (symm_e0_stab5 p v) hys _ ?_
    rw [hxv, hyv, one_mul, Lattices.sqClassOf_of_ne_zero (mul_ne_zero h20 hm0)]
  · -- the symmetries in `e₁` and `e₁ + e₂`
    set m : ℕ := (p - 1) / 2 with hmdef
    have hm2 : 2 * m + 1 = p := by omega
    have hmK : (p : v.adicCompletion ℚ) - (p : v.adicCompletion ℚ) ^ 2 =
        2 * (-(m : v.adicCompletion ℚ)) * p := by
      have : ((2 * m + 1 : ℕ) : v.adicCompletion ℚ) = (p : v.adicCompletion ℚ) := by rw [hm2]
      push_cast at this
      rw [← this]; ring
    have hmv : Valued.v (-(m : v.adicCompletion ℚ)) = 1 := by
      rw [Valuation.map_neg]; exact valued_nat5 v m (by rw [hng]; omega)
    have hm0 : (m : v.adicCompletion ℚ) ≠ 0 := fun h => by
      rw [h, neg_zero, map_zero] at hmv; exact zero_ne_one hmv
    have hav : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 1 1) = p := by
      rw [evalIn_ex5Q]; simp
    have hbv : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) ![0, 1, 1] =
        2 * (-(m : v.adicCompletion ℚ)) * p := by
      rw [evalIn_ex5Q, ← hmK]; simp
    have ha0 : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 1 1) ≠ 0 := by
      rw [hav]; exact hpK
    have hb0 : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) ![0, 1, 1] ≠ 0 := by
      rw [hbv]; exact mul_ne_zero (mul_ne_zero h20 (neg_ne_zero.mpr hm0)) hpK
    have haM : (Pi.single 1 1 : Fin 3 → v.adicCompletion ℚ) ∈
        Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1 := by
      rw [loc_std5]; exact Lattices.single_mem_std 1 (by simp)
    have has := Lattices.symm_mem_locStabV_of_unit Lattices.stdLat (hint5 p v) haM (by rw [hav, hpv])
    have hbs := symm_stab5 p v (hmem _ (fun i => by fin_cases i <;> simp)) hb0 (fun z hz => by
      rw [Lattices.mem_std_iff] at hz
      have hq : Lattices.qbil ((ex5Form p).map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) ![0, 1, 1] z =
          2 * (p * z 1 - p ^ 2 * z 2) := by rw [qbil_ex5]; simp
      rw [hq, hbv, map_mul, map_mul, map_mul, hmv, hpv, mul_one, mul_one]
      have hle : Valued.v ((p : v.adicCompletion ℚ) * z 1 - (p : v.adicCompletion ℚ) ^ 2 * z 2) ≤ 1 := by
        refine (Valuation.map_sub _ _ _).trans (max_le (hP _ (hz 1)) ?_)
        rw [map_mul, map_pow, hpv, one_pow, one_mul]; exact hz 2
      calc Valued.v (2 : v.adicCompletion ℚ) * Valued.v ((p : v.adicCompletion ℚ) * z 1 -
            (p : v.adicCompletion ℚ) ^ 2 * z 2)
          ≤ Valued.v (2 : v.adicCompletion ℚ) * 1 := mul_le_mul_right hle _
        _ = _ := mul_one _)
    have hw0 : (p : v.adicCompletion ℚ) * (2 * (-(m : v.adicCompletion ℚ)) * p) ≠ 0 :=
      mul_ne_zero hpK (mul_ne_zero (mul_ne_zero h20 (neg_ne_zero.mpr hm0)) hpK)
    refine two_mem_of5 p hp hp2 v h2 h20 _ hw0 ?_ (-(m : v.adicCompletion ℚ)) hmv p hpK (by ring)
    refine Lattices.mem_localSpinorNormGroup_of_symm_pair (nondegenerate_ex5f p hp0) Lattices.stdLat ha0 hb0
      has hbs _ ?_
    rw [hav, hbv, Lattices.sqClassOf_of_ne_zero hw0]

/-- Helper: for $p \equiv 3 \pmod 4$ and a place $v$ over $p$, $-1 \in \theta(\Lambda_v)$: the symmetries in $e_0$
(value $1$) and $e_2$ (value $-p^2$, and $B(e_2, z) = -2p^2z_2$ has absolute value at most $|p^2|$) have value product
$-p^2$ of square class $-1$. Arguments: `p` (`hp`), `v` the place. -/
theorem neg_one_mem_theta5 (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (-1 : (v.adicCompletion ℚ)ˣ) ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ))
      (nondegenerate_ex5f p hp.ne_zero) v Lattices.stdLat := by
  have hp0 := hp.ne_zero
  have hpK : (p : v.adicCompletion ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hv2 : Valued.v (2 : v.adicCompletion ℚ) ≤ 1 := by simpa using valued_nat_le5 v 2
  have hxv : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 0 1) = 1 := by
    rw [evalIn_ex5Q]; simp
  have hx0 : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 0 1) ≠ 0 := by
    rw [hxv]; exact one_ne_zero
  have hyv : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 2 1) =
      -((p : v.adicCompletion ℚ) ^ 2) := by
    rw [evalIn_ex5Q]; simp
  have hy0 : ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) (Pi.single 2 1) ≠ 0 := by
    rw [hyv]; exact neg_ne_zero.mpr (pow_ne_zero 2 hpK)
  have hyM : (Pi.single 2 1 : Fin 3 → v.adicCompletion ℚ) ∈
      Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1 := by
    rw [loc_std5]; exact Lattices.single_mem_std 2 (by simp)
  have hys := symm_stab5 p v hyM hy0 (fun z hz => by
    rw [Lattices.mem_std_iff] at hz
    have hq : Lattices.qbil ((ex5Form p).map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) (Pi.single 2 1) z =
        -((p : v.adicCompletion ℚ) ^ 2 * (2 * z 2)) := by
      rw [qbil_ex5]; simp
      try ring
    rw [hq, hyv, Valuation.map_neg, Valuation.map_neg, map_mul, map_mul]
    have h1 : Valued.v (2 : v.adicCompletion ℚ) * Valued.v (z 2) ≤ 1 :=
      (mul_le_mul' hv2 (hz 2)).trans (by simp)
    calc Valued.v ((p : v.adicCompletion ℚ) ^ 2) * (Valued.v (2 : v.adicCompletion ℚ) * Valued.v (z 2))
        ≤ Valued.v ((p : v.adicCompletion ℚ) ^ 2) * 1 := mul_le_mul_right h1 _
      _ = _ := mul_one _)
  refine Lattices.mem_localSpinorNormGroup_of_symm_pair (nondegenerate_ex5f p hp0) Lattices.stdLat hx0 hy0
    (symm_e0_stab5 p v) hys _ ?_
  have e : (1 : v.adicCompletion ℚ) * -((p : v.adicCompletion ℚ) ^ 2) =
      (((-1 : (v.adicCompletion ℚ)ˣ) : (v.adicCompletion ℚ))) * (p : v.adicCompletion ℚ) ^ 2 := by simp
  rw [hxv, hyv, e, Lattices.sqClassOf_mul_sq _ hpK]

/-! ### The group $G = R/ST$ is trivial on unit classes -/

open Classical in
/-- Helper: the places of $\mathbb Q$ over $2$ and $p$, as a finite set. Arguments: `p`, `hp`. -/
def ex5P (p : ℕ) (hp : p.Prime) : Finset (HeightOneSpectrum (𝓞 ℚ)) := {ratPlace 2 Nat.prime_two, ratPlace p hp}

open Classical in
/-- Helper: `ex5P p hp` consists of exactly the places whose prime is $2$ or $p$. Arguments: `p`, `hp`, `v`. -/
theorem mem_ex5P (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ ex5P p hp ↔ Rat.HeightOneSpectrum.natGenerator v = 2 ∨ Rat.HeightOneSpectrum.natGenerator v = p := by
  unfold ex5P
  rw [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl (natGenerator_ratPlace 2 Nat.prime_two)
    · exact Or.inr (natGenerator_ratPlace p hp)
  · rintro (h | h)
    · exact Or.inl (Lattices.natGenerator_inj' (h.trans (natGenerator_ratPlace 2 Nat.prime_two).symm))
    · exact Or.inr (Lattices.natGenerator_inj' (h.trans (natGenerator_ratPlace p hp).symm))

/-- **The trivial element of $G$ on unit classes** (Cassels, (3.15) with $P = \{2, p\}$): every family `x` of unit
square classes at the places of `P` has $x\cdot\mathrm{diag}(t) \in S$ for some $t \in T$ ($t = 1$ or $2$). Arguments:
`p` the prime (`hp`, `hp2`: odd, `h8`: $p \not\equiv 1 \bmod 8$), `P` the places over $2$ and $p$ (`hmem`), `x` the
family (`hx`: each component is a unit square class). -/
theorem exists_diag_mem5 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h8 : p % 8 ≠ 1)
    (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hmem : ∀ v, v ∈ P ↔ Rat.HeightOneSpectrum.natGenerator v = 2 ∨ Rat.HeightOneSpectrum.natGenerator v = p)
    (x : Lattices.CasselsR P)
    (hx : ∀ v : P, Lattices.IsUnitSqClass v.1 (Lattices.SqClass.mk (x v))) :
    ∃ t : ℚˣ, t ∈ Lattices.casselsT ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero) P ∧
      x * Lattices.casselsDiag P t ∈
        Lattices.casselsS ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero)
          Lattices.stdLat P := by
  have hp0 := hp.ne_zero
  have hpP : (ratPlace p hp) ∈ P := (hmem _).mpr (Or.inr (natGenerator_ratPlace p hp))
  set vp : P := ⟨ratPlace p hp, hpP⟩ with hvpdef
  have hvp : Rat.HeightOneSpectrum.natGenerator vp.1 = p := natGenerator_ratPlace p hp
  obtain ⟨z, hz1, hzc⟩ := hx vp
  have hz0 : z ≠ 0 := fun h => by rw [h, map_zero] at hz1; exact zero_ne_one hz1
  obtain ⟨s, hs, hsq⟩ := exists_sign_mul_isSquare p hp hp2 h8 vp.1 hvp z hz1
  obtain ⟨t', ht', hcase⟩ : ∃ t' : ℕ, (t' = 1 ∨ t' = 2) ∧
      (IsSquare ((t' : vp.1.adicCompletion ℚ) * z) ∨ (t' = 1 ∧ p % 4 = 3 ∧ IsSquare (-z))) := by
    rcases hs with rfl | ⟨rfl, h4⟩ | ⟨rfl, h5⟩
    · exact ⟨1, Or.inl rfl, Or.inl (by simpa using hsq)⟩
    · exact ⟨1, Or.inl rfl, Or.inr ⟨rfl, h4, by simpa using hsq⟩⟩
    · exact ⟨2, Or.inr rfl, Or.inl (by simpa using hsq)⟩
  have htn : t' ≠ 0 := by rcases ht' with rfl | rfl <;> norm_num
  have ht0 : (t' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htn
  have htK : ∀ v : P, (t' : v.1.adicCompletion ℚ) ≠ 0 := fun v => Nat.cast_ne_zero.mpr htn
  refine ⟨Units.mk0 (t' : ℚ) ht0, ?_, ?_⟩
  · refine (Lattices.mem_casselsT_rat_iff _ (nondegenerate_ex5f p hp0) le_rfl P _).mpr ⟨fun v hv => ?_, fun _ => ?_⟩
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
          Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp0) v.1
            Lattices.stdLat := by
        rcases ht' with rfl | rfl
        · convert Subgroup.one_mem _
          exact Units.ext (by simp)
        · convert two_mem_theta5 p hp hp2 v.1 h2' two_ne_zero using 1
      have hW : Units.mk0 w hw0 ∈
          Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp0) v.1
            Lattices.stdLat :=
        units_mem_theta5_two p hp hp2 v.1 h2' _ hw1
      refine mem_theta5_of_class_eq p hp0 (Subgroup.mul_mem _ hW hT) ?_
      rw [hdv, Lattices.SqClass.mk_mul, Lattices.SqClass.mk_mul, hwc, Lattices.sqClassOf_of_ne_zero hw0]
    · -- the prime `p`: only the place `vp`
      have hvv : v = vp := Subtype.ext (Lattices.natGenerator_inj' (h5.trans hvp.symm))
      subst hvv
      rcases hcase with hsq' | ⟨ht1, h4, hneg⟩
      · refine mem_theta5_of_sq p hp0 ?_
        rw [hdv, Lattices.SqClass.mk_mul, hzc, Lattices.sqClassOf_of_ne_zero hz0, ← Lattices.SqClass.mk_mul]
        obtain ⟨y, hy⟩ := hsq'
        have hy0 : y ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hy
          exact mul_ne_zero (htK vp) hz0 hy
        refine (Lattices.SqClass.mk_eq_one_iff _).mpr ⟨Units.mk0 y hy0, ?_⟩
        apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mul]
        rw [sq, ← hy]
        ring
      · refine mem_theta5_of_class_eq p hp0 (neg_one_mem_theta5 p hp vp.1) ?_
        rw [hdv, Lattices.SqClass.mk_mul, hzc, Lattices.sqClassOf_of_ne_zero hz0, ← Lattices.SqClass.mk_mul]
        obtain ⟨y, hy⟩ := hneg
        have hy0 : y ≠ 0 := by
          rintro rfl
          rw [mul_zero, neg_eq_zero] at hy
          exact hz0 hy
        have e : Units.mk0 z hz0 * Units.mk0 (t' : vp.1.adicCompletion ℚ) (htK vp) =
            (-1) * (Units.mk0 y hy0) ^ 2 := by
          apply Units.ext
          simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mul, Units.val_neg, Units.val_one]
          rw [ht1]
          push_cast
          linear_combination (-1 : vp.1.adicCompletion ℚ) * hy
        rw [e, Lattices.SqClass.mk_mul, (Lattices.SqClass.mk_eq_one_iff _).mpr ⟨Units.mk0 y hy0, rfl⟩, mul_one]

/-! ### The theorem -/

/-- Helper: the unit families $X$ lie in $ST$ for $f = x^2 + py^2 - p^2z^2$ and $P = \{2, p\}$ ($p \not\equiv 1
\bmod 8$ an odd prime): the group $G = R/ST$ of (3.15) is trivial on unit classes. Arguments: `p`, `hp`, `hp2`, `h8`. -/
theorem casselsX_le_ex5 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h8 : p % 8 ≠ 1) :
    Lattices.casselsX (ex5P p hp) ≤
      Lattices.casselsST ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero)
        Lattices.stdLat (ex5P p hp) := by
  intro x hx
  have hx' : ∀ v : ex5P p hp, Lattices.IsUnitSqClass v.1 (Lattices.SqClass.mk (x v)) := fun v =>
    ⟨(x v : v.1.adicCompletion ℚ), hx v, by
      rw [Lattices.sqClassOf_of_ne_zero (x v).ne_zero, Units.mk0_val]⟩
  obtain ⟨t, ht, hs⟩ := exists_diag_mem5 p hp hp2 h8 (ex5P p hp) (mem_ex5P p hp) x hx'
  have e : x = (x * Lattices.casselsDiag (ex5P p hp) t) * (Lattices.casselsDiag (ex5P p hp) t)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs)
    (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)))

/-- **Cassels, Ch. 11, Example 5** (p. 252), one-class case, lattice form: for an odd prime $p \not\equiv 1 \pmod 8$,
every form $f'$ in the genus of $x_0^2 + p x_1^2 - p^2x_2^2$ is integrally equivalent to it. *Proof:* the group
$G = R/ST$ of (3.15) for $P = \{2, p\}$ is trivial on unit classes (`casselsX_le_ex5`), so the genus is one proper
spinor genus; $f$ is indefinite, so the spinor genus is one class (Theorem 1.4);
`ConwaySloane.intEquiv_of_sameGenus_of_casselsX_le`. Arguments: `p` the prime (`hp`, `hp2`, `h8`), `f'` a form of the
genus (`h`). -/
theorem ex5_intEquiv_of_sameGenus (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h8 : p % 8 ≠ 1) (f' : QuadForm ℤ 3)
    (h : SameGenus (ex5Form p) f') : IntEquiv (ex5Form p) f' := by
  have hf : (ex5Form p).hessian.det ≠ 0 := by
    rw [hessian_det_ex5f]
    have : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    simpa using this
  refine ConwaySloane.intEquiv_of_sameGenus_of_casselsX_le le_rfl (ex5Form p) hf (isIndefinite_ex5f p hp.ne_zero)
    (ex5P p hp) ?_ (casselsX_le_ex5 p hp hp2 h8) f' h
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

/-- **Cassels, Ch. 11, Example 5** (p. 252), the case $p \not\equiv 1 \pmod 8$, proved: *for a prime $p > 2$ with
$p \not\equiv 1 \pmod 8$, $x^2 + py^2 - p^2z^2$ is in a genus of $1$ class.* The set of classes of the genus of
`ex5Form p` has exactly one element (`ex5_intEquiv_of_sameGenus`). Arguments: `p` the prime (`hp`, `hp2`: $p \ne 2$,
`h8`: $p \not\equiv 1 \bmod 8$). -/
@[kb "cassels1978" "Ch. 11, Ex. 5, p. 252 (p ≢ 1 mod 8: one class)"]
theorem ex5_one_class (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h8 : p % 8 ≠ 1) :
    (genusClasses (ex5Form p)).ncard = 1 := by
  have : genusClasses (ex5Form p) = {classOf (ex5Form p)} := by
    ext c
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨Q', rfl, hQ'⟩
      exact (classOf_eq_classOf_iff.mpr (ex5_intEquiv_of_sameGenus p hp hp2 h8 Q' hQ')).symm
    · rintro rfl
      exact classOf_self_mem_genusClasses (ex5Form p)
  rw [this, Set.ncard_singleton]

/-! ### Local facts for $p \equiv 1 \pmod 8$ (for the two-class case) -/

/-- **$\theta(\Lambda_2)$ is everything:** for odd $p$ and a place $v$ over $2$, every element of $\mathbb Q_2^\times$
is a spinor norm of $O^+(\Lambda_v)$, $\Lambda = \mathbb Z^3$ with $f = x_0^2 + p x_1^2 - p^2x_2^2$. (Units by
`units_mem_theta5_two`, $2$ by `two_mem_theta5`; a general element is a unit times a power of $2$.) Arguments: `p`
(`hp`, `hp2`: odd prime), `v` (`h2`: over $2$), `a` the element of $(\mathbb Q_2)^\times$. -/
theorem theta5_two_all (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (a : (v.adicCompletion ℚ)ˣ) :
    a ∈ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero) v
      Lattices.stdLat := by
  have h20 : (2 : v.adicCompletion ℚ) ≠ 0 := two_ne_zero
  have t2 := two_mem_theta5 p hp hp2 v h2 h20
  have hv2 : Valued.v (2 : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := Lattices.valued_two_dyadic v h2
  have ha : Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (WithZero.log (Valued.v (a : v.adicCompletion ℚ))) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr a.ne_zero)).symm
  set n := WithZero.log (Valued.v (a : v.adicCompletion ℚ)) with hn
  have hu : Valued.v (((a * (Units.mk0 (2 : v.adicCompletion ℚ) h20) ^ n : (v.adicCompletion ℚ)ˣ)) :
      v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, ha, Units.val_mk0, hv2,
      ← WithZero.exp_zsmul, ← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1
    simp
  have hmem := units_mem_theta5_two p hp hp2 v h2 _ hu
  have e : a = (a * (Units.mk0 (2 : v.adicCompletion ℚ) h20) ^ n) * ((Units.mk0 (2 : v.adicCompletion ℚ) h20) ^ n)⁻¹ := by
    group
  rw [e]
  exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.zpow_mem _ t2 n))

/-- Helper: for $p \equiv 1 \pmod 4$ and a place $v$ over $p$, $-1$ is a square in $\mathbb Q_v$ (Hensel: choose
$c^2 \equiv -1 \bmod p$; then $-1/c^2 \equiv 1$). Arguments: `p` (`hp`, `hp2`: odd, `h4`: $p \equiv 1 \bmod 4$), `v`
(`hv`: its prime is $p$). -/
theorem isSquare_neg_one5 (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : Rat.HeightOneSpectrum.natGenerator v = p) :
    IsSquare (-1 : v.adicCompletion ℚ) := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h => by
    have := (Lattices.two_mem_iff_natGenerator v).mp h
    omega
  obtain ⟨c, hc⟩ : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hcn : ((c.val : ℕ) : ZMod p) = c := ZMod.natCast_zmod_val c
  have hnd : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ c.val := by
    rw [hv]
    intro h
    exact hc0 (by rw [← hcn]; exact (ZMod.natCast_eq_zero_iff _ _).mpr h)
  have hcv : Valued.v ((c.val : ℕ) : v.adicCompletion ℚ) = 1 := valued_nat5 v _ hnd
  have hcK : ((c.val : ℕ) : v.adicCompletion ℚ) ≠ 0 := fun h => by
    rw [h, map_zero] at hcv; exact zero_ne_one hcv
  have hdvd : (p : ℤ) ^ 1 ∣ 1 + ((c.val : ℕ) : ℤ) ^ 2 := by
    rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcn]; linear_combination -hc
  have hle := (Lattices.valued_intCast_le_iff v (1 + ((c.val : ℕ) : ℤ) ^ 2) 1).mpr (by rw [hv]; exact hdvd)
  set cK : v.adicCompletion ℚ := ((c.val : ℕ) : v.adicCompletion ℚ) with hcKdef
  have ht : Valued.v (-1 * (cK ^ 2)⁻¹ - 1) < 1 := by
    have e : -1 * (cK ^ 2)⁻¹ - 1 = -(((1 + ((c.val : ℕ) : ℤ) ^ 2 : ℤ) : v.adicCompletion ℚ)) * (cK ^ 2)⁻¹ := by
      push_cast
      rw [← hcKdef]
      field_simp
      ring
    rw [e, map_mul, Valuation.map_neg, map_inv₀, map_pow, hcv, one_pow, inv_one, mul_one]
    exact lt_of_le_of_lt (by simpa using hle) Lattices.exp_neg_one_lt_one
  obtain ⟨s, hs⟩ := Lattices.isSquare_of_val_sub_one_lt_odd (v := v) h2 ht
  refine ⟨s * cK, ?_⟩
  have : (-1 : v.adicCompletion ℚ) = (-1 * (cK ^ 2)⁻¹) * cK ^ 2 := by field_simp
  rw [this, hs]; ring

/-- **A nonsquare unit is not a spinor norm at $p \equiv 1 \pmod 8$:** for a prime $p \equiv 1 \pmod 8$ and a place $v$
over $p$, if $u$ is a unit of $\mathbb Q_v$ that is not a square, then $u \notin \theta(\Lambda_v)$, $\Lambda =
\mathbb Z^3$ with $f = x_0^2 + p x_1^2 - p^2x_2^2$. (Example 4 with the standard basis, whose values $1, p, -p^2$ have
distinct absolute values: $\theta(\Lambda_v)$ is generated by the squares, $p$ and $-p^2$; and $-1$ is a square in
$\mathbb Q_v$, so this group is contained in $\{p^k w^2\}$.) Arguments: `p` (`hp`, `hp8`: $p \equiv 1 \bmod 8$), `v`
(`hv`: its prime is $p$), `u` (`hu`: a unit; `hns`: not a square). -/
theorem nonsquare_unit_not_mem_theta5 (p : ℕ) (hp : p.Prime) (hp8 : p % 8 = 1) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : Rat.HeightOneSpectrum.natGenerator v = p) (u : (v.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) (hns : ¬ IsSquare (u : v.adicCompletion ℚ)) :
    u ∉ Lattices.localSpinorNormGroup ((ex5Form p).map (Int.castRingHom ℚ)) (nondegenerate_ex5f p hp.ne_zero) v
      Lattices.stdLat := by
  intro hmem
  have hp0 := hp.ne_zero
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h => by
    have := (Lattices.two_mem_iff_natGenerator v).mp h
    omega
  have hpK : (p : v.adicCompletion ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hsq1 := isSquare_neg_one5 p hp (by omega) v hv
  obtain ⟨s, hs⟩ := hsq1
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  -- the value of `p`
  have hvp : Valued.v (p : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
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
  have hQ := nondegenerate_ex5f p hp0
  have hγ : Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ 3).1 =
      Lattices.locAct v (1 : GL (Fin 3) (v.adicCompletion ℚ)) (Lattices.std v) := by
    rw [Lattices.locAct_one]; exact loc_std5 v
  have horth : ∀ k l, k ≠ l → Lattices.locGram ((ex5Form p).map (Int.castRingHom ℚ)) v
      (1 : GL (Fin 3) (v.adicCompletion ℚ)) k l = 0 := by
    intro k l hkl
    simp only [Lattices.locGram, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
      QuadForm.hessian_map, ex5Form, Ch11Wave6.hessian_diag]
    simp [Matrix.map_apply, hkl]
  have hQe : ∀ i : Fin 3, ((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ)
      ((1 : GL (Fin 3) (v.adicCompletion ℚ)).val *ᵥ Pi.single i 1) =
      ![1, (p : v.adicCompletion ℚ), -((p : v.adicCompletion ℚ) ^ 2)] i := by
    intro i
    fin_cases i <;> simp [evalIn_ex5Q]
  have hvv : ∀ i : Fin 3, Valued.v (![1, (p : v.adicCompletion ℚ), -((p : v.adicCompletion ℚ) ^ 2)] i) =
      WithZero.exp (![0, -1, -2] i : ℤ) := by
    intro i
    fin_cases i
    · simp
    · simpa using hvp
    · show Valued.v (-((p : v.adicCompletion ℚ) ^ 2)) = WithZero.exp (-2 : ℤ)
      rw [Valuation.map_neg, map_pow, hvp, sq, ← WithZero.exp_add]
      norm_num
  have hdist : ∀ i j, i ≠ j → Valued.v (((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ)
        ((1 : GL (Fin 3) (v.adicCompletion ℚ)).val *ᵥ Pi.single i 1)) ≠
      Valued.v (((ex5Form p).map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ)
        ((1 : GL (Fin 3) (v.adicCompletion ℚ)).val *ᵥ Pi.single j 1)) := by
    intro i j hij h
    rw [hQe, hQe, hvv, hvv, WithZero.exp_inj] at h
    fin_cases i <;> fin_cases j <;> simp at h hij
  rw [ConwaySloane.instAlgebraAdicCompletion_rat_eq v] at hdist
  have key := ex4Statement_holds.holds 3 (by norm_num) ((ex5Form p).map (Int.castRingHom ℚ)) hQ v h2
    Lattices.stdLat 1 hγ horth hdist
  rw [key] at hmem
  -- the subgroup `{p^k w^2}`
  let P : (v.adicCompletion ℚ)ˣ := Units.mk0 (p : v.adicCompletion ℚ) hpK
  let H : Subgroup (v.adicCompletion ℚ)ˣ :=
    { carrier := {a | ∃ (k : ℤ) (w : (v.adicCompletion ℚ)ˣ), a = P ^ k * w ^ 2}
      mul_mem' := by
        rintro a b ⟨k, w, rfl⟩ ⟨l, x, rfl⟩
        exact ⟨k + l, w * x, by rw [_root_.zpow_add, mul_pow]; exact mul_mul_mul_comm _ _ _ _⟩
      one_mem' := ⟨0, 1, by simp⟩
      inv_mem' := by
        rintro a ⟨k, w, rfl⟩
        exact ⟨-k, w⁻¹, by rw [mul_inv, _root_.zpow_neg, inv_pow]⟩ }
  have hgens : ex4Gens ((ex5Form p).map (Int.castRingHom ℚ)) v (1 : GL (Fin 3) (v.adicCompletion ℚ))
      ⟨0, by norm_num⟩ ⊆ H := by
    rintro g (⟨w, rfl⟩ | ⟨j, hj, hg⟩)
    · exact ⟨0, w, by simp⟩
    · rw [hQe, hQe] at hg
      fin_cases j
      · exact absurd rfl hj
      · refine ⟨1, 1, Units.ext ?_⟩
        simp at hg
        simp [P, hg]
      · refine ⟨2, Units.mk0 s hs0, Units.ext ?_⟩
        simp at hg
        simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_pow_eq_pow_val, P]
        rw [hg]
        simp only [zpow_ofNat]
        linear_combination (p : v.adicCompletion ℚ) ^ 2 * hs
  obtain ⟨k, w, huw⟩ := ((Subgroup.closure_le _).mpr hgens) hmem
  have hvw : Valued.v (w : v.adicCompletion ℚ) = WithZero.exp (WithZero.log (Valued.v (w : v.adicCompletion ℚ))) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr w.ne_zero)).symm
  set m := WithZero.log (Valued.v (w : v.adicCompletion ℚ)) with hm
  have hue : (u : v.adicCompletion ℚ) = (p : v.adicCompletion ℚ) ^ k * (w : v.adicCompletion ℚ) ^ 2 := by
    rw [huw]; simp [P]
  have hv1 := hu
  rw [hue, map_mul, map_zpow₀, map_pow, hvp, hvw, sq, ← WithZero.exp_zsmul, ← WithZero.exp_add,
    ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at hv1
  have hk : k = m + m := by simp at hv1; omega
  refine hns ⟨(p : v.adicCompletion ℚ) ^ m * (w : v.adicCompletion ℚ), ?_⟩
  rw [hue, hk, zpow_add₀ hpK]
  ring

end QuadFormsKB.Cassels.Ch11Ex4
