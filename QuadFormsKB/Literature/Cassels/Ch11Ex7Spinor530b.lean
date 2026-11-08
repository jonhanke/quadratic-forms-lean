/-
# Cassels, Ch. 11, Example 7 (i): the genus of $x^2 + xy + y^2 + 9z^2$ has two proper spinor genera

J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 11, Example 7 (i), p. 252 (`cassels1978`).

**Layer.** $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ (`ex7f`), the lattice $\mathbb Z^3$ (`stdLat`), Cassels' group
$G = R/ST$ of (3.15) for $P = \{2, 3\}$ (`P96`, the primes dividing $2\det H$; `CasselsG`).

**Route (Cassels' own, via Theorem 3.1).** $2f$ is the form `csQ A96` of Conway–Sloane's example (§9.6), whose local
spinor norm groups are bounded (`theta3_le`: at $3$ inside $\langle 3\rangle\mathbb Q_3^{\times2}$; `theta2_even`: at
$2$ of even order). Rescaling does not change $\theta(\Lambda_v)$ (`localSpinorNormGroup_smul`), so the same bounds
hold for $f$. Condition (3.7) holds by Lemma 3.3 (`casselsCond_std`). By $R = XT$ every element of $G$ is the class of
a family of units; at $2$ all units lie in $\theta(\Lambda_2)$ (Lemma 3.8, Cor.); at $3$ a unit $z$ has $z$ or $2z$
a square. So $G = \{1, [\Delta_3(2)]\}$, and the class of $\Delta_3(2)$ is nontrivial (`not_mem_casselsST_of_qClass`).
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex7Spinor530
import QuadFormsKB.Literature.Cassels.Ch11Ex5b
import QuadFormsKB.Literature.ConwaySloane.Section9Example96Rep

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Ex4

open QuadFormsKB QuadFormsKB.Lattices QuadFormsKB.ConwaySloane

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- The rational form of Example 7: $f$ of `ex7f` over $\mathbb Q$. -/
abbrev ex7Q : QuadForm ℚ 3 := ex7f.map (Int.castRingHom ℚ)

theorem ex7Q_nondeg : ex7Q.Nondegenerate :=
  Lattices.nondegenerate_map_of_det_ne_zero ex7f (by rw [hessian_det_ex7f]; norm_num)

/-- **The form of §9.6 is twice the form of Example 7**: `csQ A96` $= 2 f$ over $\mathbb Q$. -/
theorem csQ_A96_eq : csQ A96 = (2 : ℚ) • ex7Q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [csQ, Cassels.Ch8Ex2.gramForm, A96, ex7Q, QuadForm.map, ex7f, QuadForm.ofUpper] <;> norm_num

/-- Equal forms have equal local spinor norm groups (transport along an equality). Arguments: `e` the equality,
`hQ`, `hQ'` the nondegeneracies, `v` the prime, `L` the lattice. -/
theorem localSpinorNormGroup_congr7 {Q Q' : QuadForm ℚ 3} (e : Q = Q') (hQ : Q.Nondegenerate)
    (hQ' : Q'.Nondegenerate) (v : HeightOneSpectrum (𝓞 ℚ)) (L : Lat ℚ 3) :
    localSpinorNormGroup Q hQ v L = localSpinorNormGroup Q' hQ' v L := by
  subst e; rfl

/-- $\theta(\Lambda_v)$ of Example 7 equals that of §9.6 (`csQ A96`). Arguments: `v` the prime, `u` the unit. -/
theorem mem_theta_ex7_iff (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ) :
    u ∈ localSpinorNormGroup ex7Q ex7Q_nondeg v stdLat ↔
      u ∈ localSpinorNormGroup (csQ A96) A96_nondeg v stdLat := by
  have hQ' : ((2 : ℚ) • ex7Q).Nondegenerate := by rw [← csQ_A96_eq]; exact A96_nondeg
  rw [localSpinorNormGroup_congr7 csQ_A96_eq A96_nondeg hQ' v stdLat,
    localSpinorNormGroup_smul ex7Q_nondeg two_ne_zero hQ' v stdLat]

/-- A unit with trivial square class (e.g. a square) lies in $\theta(\Lambda_v)$. -/
theorem mem_theta_ex7_of_sq {v : HeightOneSpectrum (𝓞 ℚ)} {a : (v.adicCompletion ℚ)ˣ}
    (h : SqClass.mk a = 1) : a ∈ localSpinorNormGroup ex7Q ex7Q_nondeg v stdLat := by
  unfold localSpinorNormGroup
  simp only [Subgroup.mem_comap, sqClassHom_apply, h]
  exact Subgroup.one_mem _

/-- At $v \mid 2$ every unit lies in $\theta(\Lambda_v)$ (Lemma 3.8, Corollary: $2^5 \nmid 54$). Arguments: `v`
(`h2`: over $2$), `u` (`hu`: of valuation $1$). -/
theorem units_mem_theta_ex7_two (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    u ∈ localSpinorNormGroup ex7Q ex7Q_nondeg v stdLat := by
  refine Ch11Wave6.units_mem_localSpinorNormGroup_two ex7f ex7Q_nondeg ?_ v h2 u hu
  rintro ⟨-, hd⟩
  have h5 : (Lattices.casselsExpTwo 3 + ((3 : ℕ) : ℤ)).toNat = 5 := by
    unfold Lattices.casselsExpTwo
    norm_num
  rw [h5, hessian_det_ex7f] at hd
  norm_num at hd

/-- Example 7 is positive definite, so not indefinite (Cassels' $j = 1$). -/
theorem not_isIndefinite_ex7Q : ¬ IsIndefinite ex7Q := by
  intro hind
  have : IsIndefinite (csQ A96) := by
    rw [csQ_A96_eq]
    obtain ⟨w, y, hy0, hy⟩ := hind
    refine ⟨w, y, hy0, ?_⟩
    rw [evalIn_smul_alg, hy, mul_zero]
  exact not_isIndefinite_A96 this

theorem casselsJ_ex7Q : casselsJ ex7Q = 1 := by
  simp [casselsJ, not_isIndefinite_ex7Q]

/-- Cassels' condition (3.7) for $P = \{2, 3\}$ (`P96`): away from $2, 3$ the lattice is unimodular (Lemma 3.3). -/
theorem ex7_cond :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P96 → ∀ u : (v.adicCompletion ℚ)ˣ,
      u ∈ localSpinorNormGroup ex7Q ex7Q_nondeg v stdLat ↔ IsUnitSqClass v (SqClass.mk u) := by
  refine casselsCond_std (by norm_num) ex7f ex7Q_nondeg P96 fun v hv hd => hv ?_
  rw [hessian_det_ex7f] at hd
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  have hd' : primeOf v ∣ 2 ^ 2 * 3 ^ 3 := by
    have : ((primeOf v : ℕ) : ℤ) ∣ ((2 ^ 2 * 3 ^ 3 : ℕ) : ℤ) := by simpa using hd
    exact_mod_cast this
  rcases (Nat.Prime.dvd_mul hp).mp hd' with h | h
  · exact mem_P96_iff.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)))
  · exact mem_P96_iff.mpr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)))

local notation "F3" => v3.adicCompletion ℚ

open scoped Classical in
/-- The family $\Delta_3(2)$ ($2$ at $3$, $1$ at $2$) is not in $ST$ for Example 7. -/
theorem ex7_xR_not_mem :
    xR96 ∉ casselsST ex7Q ex7Q_nondeg stdLat P96 := by
  classical
  refine not_mem_casselsST_of_qClass ex7Q ex7Q_nondeg stdLat P96 (by norm_num) q3
    (fun A hA => theta3_le A ((mem_theta_ex7_iff _ A).mp hA)) ?_ ?_ ?_ ?_
  · intro p hpq A hA
    obtain ⟨k, hk⟩ := theta2_even p.1 (primeOf_eq_two_of_ne_q3 p hpq) A ((mem_theta_ex7_iff _ A).mp hA)
    have hord : ordP P96 p A = -k * 2 := by
      rw [ordP, hk, log_exp]; ring
    have e : casselsDiag P96 (natGenUnit p.1 ^ ordP P96 p A) q3 =
        (casselsDiag P96 (natGenUnit p.1 ^ (-k)) q3) ^ 2 := by
      rw [hord, _root_.zpow_mul, map_zpow, Pi.pow_apply]
      exact zpow_ofNat _ 2
    rw [e, (SqClass.mk_eq_one_iff _).mpr ⟨_, rfl⟩]
    exact Subgroup.one_mem _
  · rw [casselsJ_ex7Q, map_one, Pi.one_apply]
    exact Subgroup.one_mem _
  · intro p
    by_cases hp : p = q3
    · subst hp
      rw [xR96, Pi.mulSingle_eq_same]
      exact valued_v3_two
    · rw [xR96, Pi.mulSingle_eq_of_ne hp]; simp
  · rw [xR96, Pi.mulSingle_eq_same]
    intro hmem
    rcases mem_zpowers_q3 hmem with h | h
    · apply not_isSquare_two_v3
      rw [← sqClassOf_eq_one_iff (two_ne_zero : (2 : F3) ≠ 0), sqClassOf_of_ne_zero two_ne_zero]
      exact h
    · have h' : sqClassOf (2 : F3) = sqClassOf (3 : F3) := by
        rw [sqClassOf_of_ne_zero (two_ne_zero : (2 : F3) ≠ 0)]
        exact h.trans sqClass_primeUnit_q3
      have hm : sqClassOf ((2 : F3) * 3⁻¹) = 1 := by
        rw [sqClassOf_mul two_ne_zero (by norm_num), h', ← sqClassOf_mul (by norm_num) (by norm_num),
          mul_inv_cancel₀ three_ne_zero, sqClassOf_one]
      refine not_isSquare_of_valued_eq_exp_odd (k := 0) ?_ ((sqClassOf_eq_one_iff (by norm_num)).mp hm)
      rw [map_mul, map_inv₀, valued_v3_two, valued_v3_three, one_mul, ← WithZero.exp_neg]
      norm_num

/-- **$|G| = 2$** (Cassels, Ch. 11, Example 7 (i)): for $P = \{2, 3\}$ the group $G = R/ST$ has two elements, $1$ and
the class of $\Delta_3(2)$. -/
theorem ex7_card_casselsG :
    Nat.card (CasselsG ex7Q ex7Q_nondeg stdLat P96) = 2 := by
  classical
  -- membership in `S` for families that are units at `2` and a square at `3`
  have hS : ∀ y : CasselsR P96, (∀ p : P96, p ≠ q3 → Valued.v ((y p : (p.1.adicCompletion ℚ)ˣ) :
        p.1.adicCompletion ℚ) = 1) → IsSquare ((y q3 : (q3.1.adicCompletion ℚ)ˣ) : q3.1.adicCompletion ℚ) →
      y ∈ casselsS ex7Q ex7Q_nondeg stdLat P96 := by
    intro y hy hsq
    rw [casselsS, Subgroup.mem_pi]
    intro p _
    by_cases hp : p = q3
    · subst hp
      obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact (y q3).ne_zero (by rw [hs, mul_zero])
      refine mem_theta_ex7_of_sq ((SqClass.mk_eq_one_iff _).mpr ⟨Units.mk0 s hs0, Units.ext ?_⟩)
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
      rw [sq, hs]
    · exact units_mem_theta_ex7_two p.1
        ((two_mem_iff_natGenerator p.1).mpr (primeOf_eq_two_of_ne_q3 p hp)) _ (hy p hp)
  have hupper : ∀ r : CasselsR P96, r ∈ casselsST ex7Q ex7Q_nondeg stdLat P96 ∨
      r * xR96⁻¹ ∈ casselsST ex7Q ex7Q_nondeg stdLat P96 := by
    intro r
    obtain ⟨x, hx, t, ht, rfl⟩ := exists_casselsX_mul_casselsT ex7Q ex7Q_nondeg P96 (by norm_num) r
    have hT : casselsDiag P96 t ∈ casselsST ex7Q ex7Q_nondeg stdLat P96 :=
      Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
    have hv3' : Rat.HeightOneSpectrum.natGenerator q3.1 = 3 := natGenerator_v3
    have hz := unit_sq_or5 3 Nat.prime_three (by norm_num) q3.1 hv3' 2 (by decide)
      ((x q3 : (q3.1.adicCompletion ℚ)ˣ) : q3.1.adicCompletion ℚ) (hx q3)
    rcases hz with h | h
    · left
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hS x (fun p _ => hx p) h)) hT
    · right
      have hx' : x * xR96⁻¹ ∈ casselsST ex7Q ex7Q_nondeg stdLat P96 := by
        refine Subgroup.mem_sup_left (hS _ ?_ ?_)
        · intro p hp
          simp only [Pi.mul_apply, Pi.inv_apply, xR96, Pi.mulSingle_eq_of_ne hp, inv_one, mul_one]
          exact hx p
        · obtain ⟨s, hs⟩ := h
          refine ⟨s * 2⁻¹, ?_⟩
          simp only [Pi.mul_apply, Pi.inv_apply, xR96, Pi.mulSingle_eq_same, Units.val_mul, Units.val_inv_eq_inv_val,
            u96, Units.val_mk0]
          have hs' : (2 : q3.1.adicCompletion ℚ) * ((x q3 : (q3.1.adicCompletion ℚ)ˣ) : q3.1.adicCompletion ℚ) = s * s := by simpa using hs
          rw [show s * 2⁻¹ * (s * 2⁻¹) = (s * s) * (2⁻¹ * 2⁻¹) by ring, ← hs']
          field_simp
      rw [show x * casselsDiag P96 t * xR96⁻¹ = x * xR96⁻¹ * casselsDiag P96 t from mul_right_comm _ _ _]
      exact Subgroup.mul_mem _ hx' hT
  have hnot := ex7_xR_not_mem
  rw [Nat.card_eq_two_iff]
  refine ⟨1, QuotientGroup.mk xR96, ?_, ?_⟩
  · intro h
    exact hnot ((QuotientGroup.eq_one_iff _).mp h.symm)
  · ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    induction g using QuotientGroup.induction_on with
    | H r =>
      rcases hupper r with h | h
      · left
        exact (QuotientGroup.eq_one_iff r).mpr h
      · right
        rw [QuotientGroup.eq]
        have := Subgroup.inv_mem _ h
        rwa [_root_.mul_inv_rev, inv_inv, mul_comm] at this

/-- **Cassels, Ch. 11, Example 7 (i)** (p. 252), proved: the genus of $f = x^2 + xy + y^2 + 9z^2$ on $\mathbb Z^3$
consists of two proper spinor genera. Unconditional: $P = \{2, 3\}$ satisfies (3.7) (`ex7_cond`), the group
$G = R/ST$ has order $2$ (`ex7_card_casselsG`), and Theorem 3.1 identifies $|G|$ with the number of proper spinor
genera. -/
@[kb "cassels1978" "Ch. 11, Ex. 7 (i), p. 252 (two spinor genera, proved)"]
theorem ex7SpinorGenera_holds : Ex7SpinorGenera where
  spinorGenusNumber :=
    properSpinorGenusNumber_eq_two_of_card ex7Q ex7Q_nondeg stdLat P96 (by norm_num) ex7_cond
      ex7_card_casselsG

end QuadFormsKB.Cassels.Ch11Ex4
