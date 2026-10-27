/-
# Cassels, Chapter 11, Theorem 8.3, Corollary: representations of $q^{2m}c$

**Layer:** a $\mathbb Z$-lattice $\Lambda$ = `L : Lat ℚ n` on $V = (\mathbb Q^n, Q)$, $Q$ regular, $n \ge 3$, isotropic at
the finite prime $q$; representations $c = Q(x)$, $x \in \Lambda$, and local representations over $\Lambda_p$.

**Proves** Cassels' Corollary to Theorem 8.3 (p. 233) in a repaired form (`exists_pow_represents_of_isotropic`): if the
genus of $\Lambda$ consists of one spinor genus (Cassels' case $n = 3$), or $n \ge 4$
(`exists_pow_represents_of_isotropic_four`; Cassels obtains the needed representation by a form of the spinor genus
from Theorem 7.1, here `exists_sameProperSpinorGenus_mem`), there is $m \ge 0$ such that
for every $c \ne 0$ represented by $V$ over $\mathbb Q$ and by $\Lambda_p$ for every $p$, the number $q^{2m}c$ is
represented by $\Lambda$.
*Update (gap).* Cassels states: for $c$ divisible by $q^{2m}$ and represented over every $\mathbb Z_p$, $c$ is
represented over $\mathbb Z$; his proof applies the representation of $b$ to $c = q^{2m}b$, which needs $b = c/q^{2m}$ to
be represented over $\mathbb Z_q$ — not automatic. The version proved here
is what the argument gives. Representation over $\mathbb R$ is replaced by rational representation (Cassels uses the
Hasse principle for it); the addendum on primitive representations at $p \ne q$ is not formalized.
*Proof:* $c$ is represented by some $\Gamma$ of the genus (O'Meara 102:5, `exists_sameGenus_represents`), $\Gamma$ is in
the spinor genus of $\Lambda$, so (Theorem 8.3) $\sigma\Gamma_p = \Lambda_p$ ($p \ne q$) for some $\sigma \in O^+(V)$;
there are finitely many classes in the genus, so one $m$ with $q^m\sigma\Gamma_q \subseteq \Lambda_q$ serves all of them.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec8
import QuadFormsKB.Literature.OMeara.Sec102Rep
import QuadFormsKB.Literature.Cassels.Ch11Sec4Index
import QuadFormsKB.Literature.Cassels.Ch11Sec8Cor
import QuadFormsKB.Literature.Cassels.Ch11Sec7

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ}

private theorem intEquiv_symm_intCast_aux (z : ℤ) :
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm z = (z : 𝓞 ℚ) := by
  simp

private theorem intCast_mem_iff_aux (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) :
    (z : 𝓞 ℚ) ∈ w.asIdeal ↔ (Rat.HeightOneSpectrum.natGenerator w : ℤ) ∣ z := by
  rw [← Ideal.mem_span_singleton, Rat.HeightOneSpectrum.span_natGenerator, ← Ideal.comap_symm,
    Ideal.mem_comap, intEquiv_symm_intCast_aux]

/-- Two lattices agreeing (inclusion) away from $q$: a power of $p_q$ scales one into the other. -/
private theorem exists_pow_smul_mem_aux (q : HeightOneSpectrum (𝓞 ℚ)) {L N : Lat ℚ n}
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ q → loc w N.1 ≤ loc w L.1) :
    ∃ a : ℕ, ∀ y ∈ N.1, (((Rat.HeightOneSpectrum.natGenerator q ^ a : ℕ) : 𝓞 ℚ)) • y ∈ L.1 := by
  obtain ⟨d1, hd1, h1, -⟩ := exists_global_bounds L.2
  obtain ⟨d2, hd2, -, h2⟩ := exists_global_bounds N.2
  set p := Rat.HeightOneSpectrum.natGenerator q with hp
  have hpp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator q
  have hD : ∀ y ∈ N.1, (d1 * d2) • y ∈ L.1 := fun y hy => by
    rw [mul_smul]; exact h1 _ (h2 y hy)
  set D : 𝓞 ℚ := d1 * d2 with hDdef
  have hD0 : D ≠ 0 := mul_ne_zero hd1 hd2
  set z : ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) D with hz
  have hDz : D = (z : 𝓞 ℚ) := by
    rw [← intEquiv_symm_intCast_aux, hz, RingEquiv.symm_apply_apply]
  have hz0 : z ≠ 0 := by
    intro h0; apply hD0; rw [hDz, h0]; simp
  obtain ⟨e, n', hn', hzn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hz0) p hpp.ne_one
  have hnat : ∀ y ∈ N.1, (((p ^ e * n' : ℕ) : 𝓞 ℚ)) • y ∈ L.1 := by
    intro y hy
    have h3 := hD y hy
    rw [hDz] at h3
    have : ((p ^ e * n' : ℕ) : 𝓞 ℚ) = ((z.natAbs : ℕ) : 𝓞 ℚ) := by rw [← hzn]
    rw [this]
    rcases Int.natAbs_eq z with h | h
    · have : ((z.natAbs : ℕ) : 𝓞 ℚ) = (z : 𝓞 ℚ) := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact h3
    · have : ((z.natAbs : ℕ) : 𝓞 ℚ) = -(z : 𝓞 ℚ) := by
        conv_rhs => rw [h]
        simp
      rw [this, neg_smul]; exact L.1.neg_mem h3
  refine ⟨e, fun y hy => ?_⟩
  rw [mem_iff_forall_loc L.2]
  intro w
  by_cases hw : w = q
  · subst hw
    refine locVec_mem_loc_of_smul_mem w (t := (n' : 𝓞 ℚ)) ?_ ?_
    · have := (intCast_mem_iff_aux w (n' : ℤ)).not.mpr (by exact_mod_cast hn')
      simp at this ⊢
      exact this
    · have := hnat y hy
      rw [Nat.cast_mul, mul_comm, mul_smul] at this
      simpa using this
  · have hy' := h w hw (locVec_mem_loc w hy)
    rw [locVec_smul_int]
    exact Submodule.smul_mem _ _ hy'

/-- **Cassels, Theorem 8.3, Corollary** (Ch. 11, p. 233), repaired (module docstring): *let $f$ be an integral form
in $n$ variables which is isotropic over $\mathbb Q_q$, with $n \ge 3$ and the genus of $f$ consisting of one spinor
genus. Then there is an integer $m \ge 0$ such that $q^{2m}c$ is represented by $f$ over $\mathbb Z$ for every
$c \ne 0$ represented by $f$ over every $\mathbb Z_p$ and over $\mathbb Q$.* Lattice form; $q$ the prime of the place
`q`, the genus-is-one-spinor-genus hypothesis is `hspn`. -/
@[kb "cassels1978" "Ch. 11, Thm. 8.3, Cor., p. 233 (repaired: q^{2m}c; one spinor genus; lattice form)"]
theorem exists_pow_represents_of_isotropic (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (q : HeightOneSpectrum (𝓞 ℚ)) (hq : Q.IsotropicIn (q.adicCompletion ℚ)) (L : Lat ℚ n)
    (hspn : ∀ M : Lat ℚ n, SameGenus Q L.1 M.1 → SameProperSpinorGenus Q L M) :
    ∃ m : ℕ, ∀ c : ℚ, c ≠ 0 → (∃ x : Fin n → ℚ, Q.evalIn ℚ x = c) →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ y ∈ loc v L.1,
        Q.evalIn (v.adicCompletion ℚ) y = algebraMap ℚ (v.adicCompletion ℚ) c) →
      ∃ z ∈ L.1, Q.evalIn ℚ z = (Rat.HeightOneSpectrum.natGenerator q : ℚ) ^ (2 * m) * c := by
  classical
  set p := Rat.HeightOneSpectrum.natGenerator q with hp
  obtain ⟨s, hsg, hs⟩ := ClassFin.exists_genus_reps Q hQ L
  have key : ∀ M ∈ s, ∃ (τ : orthGroup Q ℚ) (a : ℕ), ∀ y ∈ M.1,
      (((p ^ a : ℕ) : 𝓞 ℚ)) • ((τ : GL (Fin n) ℚ).val *ᵥ y) ∈ L.1 := by
    intro M hM
    obtain ⟨σ, -, hσ⟩ := exists_soSub_locAct_eq_of_sameProperSpinorGenus Q hn hQ q hq (hspn M (hsg M hM))
    obtain ⟨a, ha⟩ := exists_pow_smul_mem_aux q (L := L)
      (N := ⟨glImage ((σ⁻¹ : orthGroup Q ℚ) : GL (Fin n) ℚ) M.1, glImage_isLattice _ M.2⟩)
      (fun w hw => (loc_glImage_inv_eq Q σ w L M (hσ w hw)).le)
    exact ⟨σ⁻¹, a, fun y hy => ha _ (mulVec_mem_glImage hy)⟩
  choose! τ a hτ using key
  refine ⟨s.sup a, fun c hc0 hx hloc => ?_⟩
  obtain ⟨x, hx⟩ := hx
  obtain ⟨M', hgen, z, hzM, hzc⟩ := exists_sameGenus_represents Q L hc0 hx hloc
  obtain ⟨M0, hM0, γ, hγ, hγM⟩ := hs M' hgen
  have hz0 : (γ : GL (Fin n) ℚ).val *ᵥ z ∈ M0.1 := hγM ▸ mulVec_mem_glImage hzM
  have hq0 : Q.evalIn ℚ ((γ : GL (Fin n) ℚ).val *ᵥ z) = c := by
    rw [evalIn_mulVec_of_mem Q hγ, hzc]
  have hle : a M0 ≤ s.sup a := Finset.le_sup hM0
  set z0 := (γ : GL (Fin n) ℚ).val *ᵥ z
  set w := (τ M0 : GL (Fin n) ℚ).val *ᵥ z0 with hw
  have hwL := hτ M0 hM0 z0 hz0
  have hmem : (((p ^ (s.sup a) : ℕ) : 𝓞 ℚ)) • w ∈ L.1 := by
    have : (((p ^ (s.sup a) : ℕ) : 𝓞 ℚ)) = ((p ^ (s.sup a - a M0) : ℕ) : 𝓞 ℚ) * ((p ^ a M0 : ℕ) : 𝓞 ℚ) := by
      rw [← Nat.cast_mul, ← pow_add, Nat.sub_add_cancel hle]
    rw [this, mul_smul]
    exact L.1.smul_mem _ hwL
  refine ⟨_, hmem, ?_⟩
  have e1 : (((p ^ (s.sup a) : ℕ) : 𝓞 ℚ)) • w = ((p ^ (s.sup a) : ℕ) : ℚ) • w := by
    exact (Nat.cast_smul_eq_nsmul (𝓞 ℚ) _ w).trans (Nat.cast_smul_eq_nsmul ℚ _ w).symm
  rw [e1, QuadFormsKB.QuadForm.evalIn_smul, hw, evalIn_mulVec_of_mem Q (τ M0).2, hq0]
  push_cast
  ring

/-- **Cassels, Theorem 8.3, Corollary** (Ch. 11, p. 233), repaired (module docstring), for $n \ge 4$: *let $f$ be an
integral form in $n \ge 4$ variables which is isotropic over $\mathbb Q_q$. Then there is an integer $m \ge 0$ such that
$q^{2m}c$ is represented by $f$ over $\mathbb Z$ for every $c \ne 0$ represented by $f$ over every $\mathbb Z_p$ and over
$\mathbb Q$.* No hypothesis on the spinor genera: Cassels uses Theorem 7.1 (a representation by some form of the
spinor genus of $f$); here its non-primitive form `exists_sameProperSpinorGenus_mem`. Lattice form; $q$ the prime of
the place `q`. -/
@[kb "cassels1978" "Ch. 11, Thm. 8.3, Cor., p. 233 (repaired: q^{2m}c; n ≥ 4; lattice form)"]
theorem exists_pow_represents_of_isotropic_four (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    (q : HeightOneSpectrum (𝓞 ℚ)) (hq : Q.IsotropicIn (q.adicCompletion ℚ)) (L : Lat ℚ n) :
    ∃ m : ℕ, ∀ c : ℚ, c ≠ 0 → (∃ x : Fin n → ℚ, Q.evalIn ℚ x = c) →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ y ∈ loc v L.1,
        Q.evalIn (v.adicCompletion ℚ) y = algebraMap ℚ (v.adicCompletion ℚ) c) →
      ∃ z ∈ L.1, Q.evalIn ℚ z = (Rat.HeightOneSpectrum.natGenerator q : ℚ) ^ (2 * m) * c := by
  classical
  set p := Rat.HeightOneSpectrum.natGenerator q with hp
  obtain ⟨s, hsg, hs⟩ := ClassFin.exists_genus_reps Q hQ L
  have key : ∀ M ∈ s, (∃ M'' : Lat ℚ n, SameProperSpinorGenus Q L M'' ∧ IsIsometric Q M''.1 M.1) →
      ∃ (τ : orthGroup Q ℚ) (a : ℕ), ∀ y ∈ M.1,
        (((p ^ a : ℕ) : 𝓞 ℚ)) • ((τ : GL (Fin n) ℚ).val *ᵥ y) ∈ L.1 := by
    rintro M - ⟨M'', hspn, ρ, hρ, hρM⟩
    obtain ⟨σ, -, hσ⟩ := exists_soSub_locAct_eq_of_sameProperSpinorGenus Q (by omega) hQ q hq hspn
    obtain ⟨a, ha⟩ := exists_pow_smul_mem_aux q (L := L)
      (N := ⟨glImage ((σ⁻¹ : orthGroup Q ℚ) : GL (Fin n) ℚ) M''.1, glImage_isLattice _ M''.2⟩)
      (fun w hw => (loc_glImage_inv_eq Q σ w L M'' (hσ w hw)).le)
    refine ⟨σ⁻¹ * (⟨ρ, hρ⟩ : orthGroup Q ℚ)⁻¹, a, fun y hy => ha _ ?_⟩
    rw [← hρM] at hy
    obtain ⟨y', hy', rfl⟩ := mem_glImage.mp hy
    have e : (((σ⁻¹ * (⟨ρ, hρ⟩ : orthGroup Q ℚ)⁻¹ : orthGroup Q ℚ) : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ
        (ρ.val *ᵥ y') = (((σ⁻¹ : orthGroup Q ℚ) : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ y' := by
      rw [mulVec_mulVec, ← Units.val_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      change ((((σ⁻¹ : orthGroup Q ℚ) : GL (Fin n) ℚ) * ρ⁻¹ * ρ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ y' = _
      rw [inv_mul_cancel_right]; rfl
    rw [e]
    exact mulVec_mem_glImage hy'
  choose! τ a hτ using key
  refine ⟨s.sup a, fun c hc0 hx hloc => ?_⟩
  obtain ⟨x, hx⟩ := hx
  obtain ⟨M', hspn', hxM'⟩ := exists_sameProperSpinorGenus_mem Q hQ hn L hc0 hx hloc
  have hgen : SameGenus Q L.1 M'.1 :=
    SameSpinorGenus.sameGenus Q (SameProperSpinorGenus.sameSpinorGenus Q hspn')
  obtain ⟨M0, hM0, γ, hγ, hγM⟩ := hs M' hgen
  have hz0 : (γ : GL (Fin n) ℚ).val *ᵥ x ∈ M0.1 := hγM ▸ mulVec_mem_glImage hxM'
  have hq0 : Q.evalIn ℚ ((γ : GL (Fin n) ℚ).val *ᵥ x) = c := by
    rw [evalIn_mulVec_of_mem Q hγ, hx]
  have hle : a M0 ≤ s.sup a := Finset.le_sup hM0
  set z0 := (γ : GL (Fin n) ℚ).val *ᵥ x
  set w := (τ M0 : GL (Fin n) ℚ).val *ᵥ z0 with hw
  have hwL := hτ M0 hM0 ⟨M', hspn', γ, hγ, hγM⟩ z0 hz0
  have hmem : (((p ^ (s.sup a) : ℕ) : 𝓞 ℚ)) • w ∈ L.1 := by
    have : (((p ^ (s.sup a) : ℕ) : 𝓞 ℚ)) = ((p ^ (s.sup a - a M0) : ℕ) : 𝓞 ℚ) * ((p ^ a M0 : ℕ) : 𝓞 ℚ) := by
      rw [← Nat.cast_mul, ← pow_add, Nat.sub_add_cancel hle]
    rw [this, mul_smul]
    exact L.1.smul_mem _ hwL
  refine ⟨_, hmem, ?_⟩
  have e1 : (((p ^ (s.sup a) : ℕ) : 𝓞 ℚ)) • w = ((p ^ (s.sup a) : ℕ) : ℚ) • w := by
    exact (Nat.cast_smul_eq_nsmul (𝓞 ℚ) _ w).trans (Nat.cast_smul_eq_nsmul ℚ _ w).symm
  rw [e1, QuadFormsKB.QuadForm.evalIn_smul, hw, evalIn_mulVec_of_mem Q (τ M0).2, hq0]
  push_cast
  ring

end QuadFormsKB.Lattices
