/-
# Cassels, Chapter 11, Theorem 8.3, Corollary with primitive representations away from $q$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11: the Corollary to Theorem 8.3 (p. 233) as it is
used in the proof of Lemma 9.2 (p. 248: "By Theorem 8.3, Corollary, we may choose $c \in \Gamma$ not to be of the form
$pd$, $d \in \Gamma$"), and O'Meara (1973), Example 102:5 (p. 300).

**Layer:** lattices `L : Lat F n` on $V = (F^n, Q)$ over a number field $F$ (for Theorem 8.3: $F = \mathbb Q$), their
localizations `loc v L`, local primitive vectors `LocPrimitive` (Cassels, p. 227).

**Proves.**
* `exists_sameGenus_primitive_at` (O'Meara 102:5 for one vector, with primitivity): if $Q(x) \ne 0$ and at every prime
  $\mathfrak p$ a vector $y_\mathfrak p \in L_\mathfrak p$ has $Q(y_\mathfrak p) = Q(x)$, then $x$ lies in a lattice $L'$ of
  the genus of $L$, and $x$ is primitive in $L'_\mathfrak p$ at every prime where $y_\mathfrak p$ is primitive in
  $L_\mathfrak p$.
* `exists_pow_represents_primitive` (Cassels, Theorem 8.3, Corollary, with the primitivity addendum used on p. 248): for
  a lattice $L$ with $n \ge 3$ whose genus is one proper spinor genus and a prime $q$ at which $V$ is isotropic there is
  $m \ge 0$ such that for every $c = Q(x) \ne 0$ represented by every $L_\mathfrak p$, the number $q^{2m}c$ is represented
  by $L$ by a vector that is primitive at every prime $\mathfrak p \ne q$ at which $c$ is primitively represented by
  $L_\mathfrak p$. This is the repaired form of `exists_pow_represents_of_isotropic` (the factor $q^{2m}$, an *Update*)
  with the addendum on primitive representations.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec8Rep
import QuadFormsKB.Literature.Cassels.Ch11Sec7Lemma
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm

open NumberField IsDedekindDomain Matrix Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section General

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **O'Meara 102:5 for one vector, with primitivity** (O'Meara 1973, §102A, p. 300; the gluing of Cassels' proof of
Theorem 7.1, p. 227): let $L$ be a lattice on $V$, $x \in V$ with $Q(x) \ne 0$, and for every prime $\mathfrak p$ let
$y_\mathfrak p \in L_\mathfrak p$ with $Q(y_\mathfrak p) = Q(x)$. Then there is a lattice $L'$ in the genus of $L$ with
$x \in L'$ such that $x$ is primitive in $L'_\mathfrak p$ at every prime $\mathfrak p$ satisfying `good` (a property of
primes at which $y_\mathfrak p$ is primitive in $L_\mathfrak p$). *Proof:* $L'_\mathfrak p = L_\mathfrak p$ where $x$ is
primitive in $L_\mathfrak p$ (almost all $\mathfrak p$), and $L'_\mathfrak p = \gamma_\mathfrak pL_\mathfrak p$ elsewhere,
with $\gamma_\mathfrak p \in O(V_\mathfrak p)$, $\gamma_\mathfrak py_\mathfrak p = x$ (Witt's theorem for one vector). -/
theorem exists_sameGenus_primitive_at (L : Lat F n) {x : Fin n → F} (hx0 : Q.eval x ≠ 0)
    (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F) (hyL : ∀ v, y v ∈ loc v L.1)
    (hy : ∀ v, Q.evalIn (v.adicCompletion F) (y v) = algebraMap F (v.adicCompletion F) (Q.eval x))
    (good : HeightOneSpectrum (𝓞 F) → Prop) (hgood : ∀ v, good v → LocPrimitive v (loc v L.1) (y v)) :
    ∃ L' : Lat F n, SameGenus Q L.1 L'.1 ∧ x ∈ L'.1 ∧
      ∀ v, good v → LocPrimitive v (loc v L'.1) (locVec v x) := by
  classical
  have hxne : x ≠ 0 := by
    rintro rfl; apply hx0; simp [QuadForm.evalIn]
  choose γ hγ hγy using fun v => exists_orth_mulVec_eq_local Q v (x := y v) (y := locVec v x)
    ((hy v).trans (evalIn_locVec Q v x).symm) (by rw [hy v]; exact (map_ne_zero _).mpr hx0)
  let M : LocFamily F n :=
    { M := fun v => if LocPrimitive v (loc v L.1) (locVec v x) then loc v L.1 else locAct v (γ v) (loc v L.1)
      isLattice := fun v => by
        split_ifs
        · exact loc_isLattice v L.2
        · exact locAct_isLattice _ (loc_isLattice v L.2)
      eventually_std := by
        filter_upwards [eventually_locPrimitive L.2 hxne, loc_eventually_std L.2] with v hv hL
        simp only [hv, ↓reduceIte]; exact hL }
  have hM : ∀ v, M.M v = if LocPrimitive v (loc v L.1) (locVec v x) then loc v L.1 else
      locAct v (γ v) (loc v L.1) := fun v => rfl
  have hmem : ∀ v, locVec v x ∈ loc v M.glue := by
    intro v
    rw [M.loc_glue, hM]
    split_ifs with h
    · exact h.1
    · rw [← hγy v]; exact ⟨y v, hyL v, rfl⟩
  refine ⟨⟨M.glue, M.glue_isLattice⟩, fun v => ?_, (mem_iff_forall_loc M.glue_isLattice x).2 hmem,
    fun v hv => ?_⟩
  · change ∃ g ∈ orthGroup Q _, locAct v g (loc v L.1) = loc v M.glue
    rw [M.loc_glue, hM]
    split_ifs
    · exact ⟨1, (orthGroup Q _).one_mem, locAct_one _⟩
    · exact ⟨γ v, hγ v, rfl⟩
  · change LocPrimitive v (loc v M.glue) (locVec v x)
    rw [M.loc_glue, hM]
    split_ifs with h
    · exact h
    · rw [← hγy v]; exact (hgood v hv).locAct _

end General

/-- **Cassels, Theorem 8.3, Corollary, with primitive representations away from $q$** (Ch. 11, p. 233, as used on
p. 248): let $L$ be a lattice on the regular space $V = (\mathbb Q^n, Q)$, $n \ge 3$, whose genus consists of one proper
spinor genus (`hspn`), and let $q$ be a prime at which $V$ is isotropic. Then there is $m \ge 0$ with the following
property. Let $x \in V$ with $c = Q(x) \ne 0$, and for every prime $\mathfrak p$ let $y_\mathfrak p \in L_\mathfrak p$ with
$Q(y_\mathfrak p) = c$; let `good` be a property of primes $\mathfrak p \ne q$ at which $y_\mathfrak p$ is primitive in
$L_\mathfrak p$. Then $q^{2m}c = Q(z)$ for some $z \in L$ which is primitive in $L_\mathfrak p$ at every `good` prime.
*Proof:* as for `exists_pow_represents_of_isotropic`, with `exists_sameGenus_primitive_at` in place of O'Meara 102:5;
primitivity is preserved by the global isometries used and by the scalar $q^m$, a unit at $\mathfrak p \ne q$. -/
@[kb "cassels1978" "Ch. 11, Thm. 8.3, Cor., p. 233 (repaired: q^{2m}c; primitive away from q, as used on p. 248)"]
theorem exists_pow_represents_primitive {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (q : HeightOneSpectrum (𝓞 ℚ)) (hq : Q.IsotropicIn (q.adicCompletion ℚ)) (L : Lat ℚ n)
    (hspn : ∀ M : Lat ℚ n, SameGenus Q L.1 M.1 → SameProperSpinorGenus Q L M) :
    ∃ m : ℕ, ∀ x : Fin n → ℚ, Q.eval x ≠ 0 →
      ∀ y : ∀ v : HeightOneSpectrum (𝓞 ℚ), Fin n → v.adicCompletion ℚ, (∀ v, y v ∈ loc v L.1) →
      (∀ v, Q.evalIn (v.adicCompletion ℚ) (y v) = algebraMap ℚ (v.adicCompletion ℚ) (Q.eval x)) →
      ∀ good : HeightOneSpectrum (𝓞 ℚ) → Prop, (∀ v, good v → v ≠ q ∧ LocPrimitive v (loc v L.1) (y v)) →
      ∃ z ∈ L.1, Q.eval z = (Rat.HeightOneSpectrum.natGenerator q : ℚ) ^ (2 * m) * Q.eval x ∧
        ∀ v, good v → LocPrimitive v (loc v L.1) (locVec v z) := by
  classical
  set p := Rat.HeightOneSpectrum.natGenerator q with hp
  obtain ⟨s, hsg, hs⟩ := ClassFin.exists_genus_reps Q hQ L
  have key : ∀ M ∈ s, ∃ (σ : orthGroup Q ℚ) (a : ℕ),
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ q →
        loc w (glImage ((σ⁻¹ : orthGroup Q ℚ) : GL (Fin n) ℚ) M.1) = loc w L.1) ∧
      ∀ y ∈ M.1, (((p ^ a : ℕ) : 𝓞 ℚ)) • (((σ⁻¹ : orthGroup Q ℚ) : GL (Fin n) ℚ).val *ᵥ y) ∈ L.1 := by
    intro M hM
    obtain ⟨σ, -, hσ⟩ := exists_soSub_locAct_eq_of_sameProperSpinorGenus Q hn hQ q hq (hspn M (hsg M hM))
    obtain ⟨a, ha⟩ := exists_pow_smul_mem_aux q (L := L)
      (N := ⟨glImage ((σ⁻¹ : orthGroup Q ℚ) : GL (Fin n) ℚ) M.1, glImage_isLattice _ M.2⟩)
      (fun w hw => (loc_glImage_inv_eq Q σ w L M (hσ w hw)).le)
    exact ⟨σ, a, fun w hw => loc_glImage_inv_eq Q σ w L M (hσ w hw), fun y hy => ha _ (mulVec_mem_glImage hy)⟩
  choose! σ a hσL hσ using key
  refine ⟨s.sup a, fun x hx0 y hyL hy good hgood => ?_⟩
  obtain ⟨M', hgen, hxM', hprim⟩ := exists_sameGenus_primitive_at Q L hx0 y hyL hy good fun v hv => (hgood v hv).2
  obtain ⟨M0, hM0, γ, hγ, hγM⟩ := hs M' hgen
  set z0 := (γ : GL (Fin n) ℚ).val *ᵥ x with hz0def
  have hz0 : z0 ∈ M0.1 := hγM ▸ mulVec_mem_glImage hxM'
  have hq0 : Q.evalIn ℚ z0 = Q.eval x := evalIn_mulVec_of_mem Q hγ x
  have hle : a M0 ≤ s.sup a := Finset.le_sup hM0
  set w := (((σ M0)⁻¹ : orthGroup Q ℚ) : GL (Fin n) ℚ).val *ᵥ z0 with hw
  have hwL := hσ M0 hM0 z0 hz0
  have hmem : (((p ^ (s.sup a) : ℕ) : 𝓞 ℚ)) • w ∈ L.1 := by
    have : (((p ^ (s.sup a) : ℕ) : 𝓞 ℚ)) = ((p ^ (s.sup a - a M0) : ℕ) : 𝓞 ℚ) * ((p ^ a M0 : ℕ) : 𝓞 ℚ) := by
      rw [← Nat.cast_mul, ← pow_add, Nat.sub_add_cancel hle]
    rw [this, mul_smul]
    exact L.1.smul_mem _ hwL
  refine ⟨_, hmem, ?_, fun v hv => ?_⟩
  · have e1 : (((p ^ (s.sup a) : ℕ) : 𝓞 ℚ)) • w = ((p ^ (s.sup a) : ℕ) : ℚ) • w :=
      (Nat.cast_smul_eq_nsmul (𝓞 ℚ) _ w).trans (Nat.cast_smul_eq_nsmul ℚ _ w).symm
    change Q.evalIn ℚ _ = _
    rw [e1, QuadFormsKB.QuadForm.evalIn_smul, hw, evalIn_mulVec_of_mem Q ((σ M0)⁻¹).2, hq0]
    push_cast
    ring
  · obtain ⟨hvq, -⟩ := hgood v hv
    rw [← hσL M0 hM0 v hvq, locVec_smul_int]
    have hunit : Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) ((p ^ (s.sup a) : ℕ) : 𝓞 ℚ) :
        v.adicCompletion ℚ) = 1 := by
      have hnd : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ p ^ (s.sup a) := by
        intro hd
        have hpv := Rat.HeightOneSpectrum.prime_natGenerator v
        have hpq := Rat.HeightOneSpectrum.prime_natGenerator q
        have h1 := (Nat.prime_dvd_prime_iff_eq hpv hpq).mp (hpv.dvd_of_dvd_pow hd)
        exact hvq ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h1))
      have := valued_natCast_eq_one' (v := v) hnd
      simpa using this
    have e2 : (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) ((p ^ (s.sup a) : ℕ) : 𝓞 ℚ)) • locVec v w =
        ((algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) ((p ^ (s.sup a) : ℕ) : 𝓞 ℚ) :
          v.adicCompletion ℚ)) • locVec v w := rfl
    rw [e2]
    refine LocPrimitive.smul_unit ?_ hunit
    rw [loc_glImage, hw, locVec_mulVec]
    refine LocPrimitive.locAct (g := GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ))
      (((σ M0)⁻¹ : orthGroup Q ℚ) : GL (Fin n) ℚ)) ?_
    rw [← hγM, loc_glImage, hz0def, locVec_mulVec]
    exact (hprim v hv).locAct (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) (γ : GL (Fin n) ℚ))

end QuadFormsKB.Lattices
