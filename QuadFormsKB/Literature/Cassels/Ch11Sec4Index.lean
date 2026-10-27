/-
# Cassels, Chapter 11, §4: the index $I(\Lambda, \Gamma)$

**Layer:** lattices `Lat F n` in $F^n$ over a number field $F$ (Cassels: $\mathbb Z$-lattices in $\mathbb Q^n$), the
index of a sublattice `AddSubgroup.relIndex`, the index of $L$ relative to $\mathcal O_F^n$,
`Tamagawa.SiegelSpace.latIndex` (the product of the local indices $\|\det A_\mathfrak p\|_\mathfrak p$; two
$\mathbb Z$-lattices "have the same determinant with respect to a fixed basis of $V$" exactly when their `latIndex`
agree, since the determinant of a basis is determined up to sign by the lattice).

**Defines** Cassels' $I(\Lambda, \Gamma) = (\Lambda : \Lambda \cap \Gamma)$ ((4.1), p. 215), `casselsI`.

**Proves**
* (4.1) (`casselsI_comm`): if $\Lambda, \Gamma$ have the same determinant, $\Lambda \cap \Gamma$ has the same index in
  both, $I(\Lambda, \Gamma) = I(\Gamma, \Lambda)$ (over a number field);
* (4.2) $\iff$ (4.3) (`loc_eq_iff_not_dvd_casselsI`): over $\mathbb Q$, for lattices of the same determinant,
  $\Lambda_p = \Gamma_p$ iff $p \nmid I(\Lambda, \Gamma)$ (Cassels: "by Lemma 2.1").
-/
import QuadFormsKB.Literature.Cassels.Ch11Thm13Int
import QuadFormsKB.Tamagawa.LatIndexCard

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Tamagawa.SiegelSpace

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Helpers -/

/-- The intersection of two lattices is a lattice. -/
theorem isLattice_inf_aux {L M : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) (hM : M.IsLattice F) :
    (L ⊓ M).IsLattice F := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hL
  obtain ⟨e, he, h1', h2'⟩ := exists_global_bounds hM
  refine isLattice_of_global_bounds (d := d * e) (mul_ne_zero hd he) (fun x hx => ⟨?_, ?_⟩) (fun x hx => ?_)
  · rw [mul_smul]; exact h1 _ (intVec.smul_mem e hx)
  · rw [mul_comm, mul_smul]; exact h1' _ (intVec.smul_mem d hx)
  · rw [mul_smul]; exact intVec.smul_mem d (h2' x hx.2)

/-- If $t \notin \mathfrak p$ and $t\,y \in M$ then $y \in M_\mathfrak p$. -/
theorem locVec_mem_loc_of_smul_mem (w : HeightOneSpectrum (𝓞 F)) {M : Submodule (𝓞 F) (Fin n → F)} {t : 𝓞 F}
    (ht : t ∉ w.asIdeal) {y : Fin n → F} (h : t • y ∈ M) : locVec w y ∈ loc w M := by
  have hv : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) t) = 1 := by
    rw [valued_algebraMap_int]; exact HeightOneSpectrum.intValuation_eq_one_iff.2 ht
  have hne : algebraMap (𝓞 F) (w.adicCompletion F) t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hc : Valued.v ((algebraMap (𝓞 F) (w.adicCompletion F) t)⁻¹) ≤ 1 := by
    rw [map_inv₀, hv]; simp
  have e : locVec w y = toO w _ hc • locVec w (t • y) := by
    rw [locVec_smul_int, smul_smul]
    have : toO w _ hc * algebraMap (𝓞 F) (w.adicCompletionIntegers F) t = 1 := by
      apply Subtype.ext
      change (algebraMap (𝓞 F) (w.adicCompletion F) t)⁻¹ * algebraMap (𝓞 F) (w.adicCompletion F) t = 1
      exact inv_mul_cancel₀ hne
    rw [this, one_smul]
  rw [e]; exact Submodule.smul_mem _ _ (locVec_mem_loc w h)

theorem relIndex_nsmul_mem_aux {G : Type*} [AddCommGroup G] {H K : AddSubgroup G} {x : G} (hx : x ∈ K) :
    H.relIndex K • x ∈ H := by
  have := AddSubgroup.nsmul_index_mem (H.addSubgroupOf K) (⟨x, hx⟩ : K)
  rw [AddSubgroup.mem_addSubgroupOf] at this
  simpa [AddSubgroup.relIndex] using this

theorem exists_of_prime_dvd_relIndex {G : Type*} [AddCommGroup G] {H K : AddSubgroup G} (p : ℕ) [Fact p.Prime]
    (hd : p ∣ H.relIndex K) (hne : H.relIndex K ≠ 0) : ∃ x ∈ K, x ∉ H ∧ p • x ∈ H := by
  have : (H.addSubgroupOf K).FiniteIndex := ⟨hne⟩
  have : Finite (K ⧸ H.addSubgroupOf K) := AddSubgroup.finite_quotient_of_finiteIndex
  have hd' : p ∣ Nat.card (K ⧸ H.addSubgroupOf K) := by
    rw [← AddSubgroup.index_eq_card]; exact hd
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' p hd'
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  refine ⟨x.1, x.2, ?_, ?_⟩
  · intro hx
    have h0 : (QuotientAddGroup.mk x : K ⧸ H.addSubgroupOf K) = 0 :=
      (QuotientAddGroup.eq_zero_iff x).2 (AddSubgroup.mem_addSubgroupOf.2 hx)
    rw [h0, addOrderOf_zero] at hq
    exact (Fact.out : p.Prime).one_lt.ne hq
  · have h0 : p • (QuotientAddGroup.mk x : K ⧸ H.addSubgroupOf K) = 0 := hq ▸ addOrderOf_nsmul_eq_zero _
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h0
    exact AddSubgroup.mem_addSubgroupOf.1 h0

section OverQ

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem asIdeal_eq_span_aux :
    v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator v
  have h2 : v.asIdeal = (v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).comap
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) :=
    (Ideal.comap_map_of_bijective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective).symm
  rw [← h] at h2
  rw [h2]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  have e1 : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) =
      ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) := map_natCast _ _
  rw [← e1]
  exact map_dvd_iff _

private theorem natCast_mem_asIdeal_iff (m : ℕ) :
    (m : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ m := by
  rw [asIdeal_eq_span_aux, Ideal.mem_span_singleton, ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)),
    map_natCast, map_natCast, Int.natCast_dvd_natCast]

private theorem natGenerator_notMem_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  intro h
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [asIdeal_eq_span_aux v, Ideal.span_le]; simpa using h
  exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)

/-- **Local-global at one prime:** if $y \in M_\mathfrak p$ and $p\,y \in M$ then $y \in M$. -/
private theorem mem_of_loc_of_smul_mem {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : M.IsLattice ℚ) {y : Fin n → ℚ}
    (h1 : locVec v y ∈ loc v M) (h2 : Rat.HeightOneSpectrum.natGenerator v • y ∈ M) : y ∈ M := by
  rw [mem_iff_forall_loc hM]
  intro w
  rcases eq_or_ne w v with rfl | hw
  · exact h1
  · refine locVec_mem_loc_of_smul_mem w (natGenerator_notMem_of_ne v hw) ?_
    rwa [Nat.cast_smul_eq_nsmul]

private theorem loc_le_of_not_dvd {K N : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (h : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ K.toAddSubgroup.relIndex N.toAddSubgroup) :
    loc v N ≤ loc v K := by
  rw [loc, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  refine locVec_mem_loc_of_smul_mem v (t := ((K.toAddSubgroup.relIndex N.toAddSubgroup : ℕ) : 𝓞 ℚ))
    (fun hm => h ((natCast_mem_asIdeal_iff v _).1 hm)) ?_
  rw [Nat.cast_smul_eq_nsmul]
  exact relIndex_nsmul_mem_aux (H := K.toAddSubgroup) (K := N.toAddSubgroup) hx

end OverQ

/-- **Cassels' index** $I(\Lambda, \Gamma) = (\Lambda : \Lambda \cap \Gamma)$ (Ch. 11, (4.1), p. 215), the index of
$\Lambda \cap \Gamma$ in $\Lambda$ (a positive integer for lattices). Cassels defines it for lattices of the same
determinant, when it is also the index of $\Lambda \cap \Gamma$ in $\Gamma$ (`casselsI_comm`). -/
@[kb "cassels1978" "Ch. 11, (4.1), p. 215"]
def casselsI (L M : Lat F n) : ℕ := (L.1 ⊓ M.1).toAddSubgroup.relIndex L.1.toAddSubgroup

/-- **Cassels (4.1)** (Ch. 11, p. 215): *if $\Lambda, \Gamma$ have the same determinant, then $\Lambda \cap \Gamma$ is
also a lattice and it has the same index in $\Lambda$ and $\Gamma$.* "Same determinant": `latIndex L = latIndex M`. -/
@[kb "cassels1978" "Ch. 11, (4.1), p. 215 (the index of Λ ∩ Γ in Λ and in Γ)"]
theorem casselsI_comm {L M : Lat F n} (h : latIndex L = latIndex M) : casselsI L M = casselsI M L := by
  set K : Lat F n := ⟨L.1 ⊓ M.1, isLattice_inf_aux L.2 M.2⟩ with hK
  have h1 : latIndex L = (K.1.toAddSubgroup.relIndex L.1.toAddSubgroup : ℝ) * latIndex K :=
    latIndex_mul_relIndex (L := K) (M := L) inf_le_left
  have h2 : latIndex M = (K.1.toAddSubgroup.relIndex M.1.toAddSubgroup : ℝ) * latIndex K :=
    latIndex_mul_relIndex (L := K) (M := M) inf_le_right
  have key : (K.1.toAddSubgroup.relIndex L.1.toAddSubgroup : ℝ) * latIndex K =
      (K.1.toAddSubgroup.relIndex M.1.toAddSubgroup : ℝ) * latIndex K := by rw [← h1, ← h2, h]
  have := mul_right_cancel₀ (latIndex_pos K).ne' key
  unfold casselsI
  rw [inf_comm M.1 L.1]
  exact_mod_cast this

/-- **Cassels (4.2) $\iff$ (4.3)** (Ch. 11, p. 215): *by Lemma 2.1 the localizations satisfy $\Lambda_p = \Gamma_p$ if
and only if $p \nmid I(\Lambda, \Gamma)$*, for $\mathbb Z$-lattices of the same determinant ($p$ the prime of $v$). -/
@[kb "cassels1978" "Ch. 11, (4.2)–(4.3), p. 215"]
theorem loc_eq_iff_not_dvd_casselsI {L M : Lat ℚ n} (h : latIndex L = latIndex M) (v : HeightOneSpectrum (𝓞 ℚ)) :
    loc v L.1 = loc v M.1 ↔ ¬ Rat.HeightOneSpectrum.natGenerator v ∣ casselsI L M := by
  have hp : (Rat.HeightOneSpectrum.natGenerator v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨hp⟩
  have hcomm := casselsI_comm h
  constructor
  · intro hloc hdvd
    have hne : casselsI L M ≠ 0 :=
      relIndex_ne_zero (L := (⟨L.1 ⊓ M.1, isLattice_inf_aux L.2 M.2⟩ : Lat ℚ n)) (M := L) inf_le_left
    obtain ⟨x, hxL, hxK, hpx⟩ := exists_of_prime_dvd_relIndex (H := (L.1 ⊓ M.1).toAddSubgroup)
      (K := L.1.toAddSubgroup) _ hdvd hne
    refine hxK ⟨hxL, mem_of_loc_of_smul_mem v M.2 ?_ hpx.2⟩
    rw [← hloc]; exact locVec_mem_loc v hxL
  · intro hnd
    have hnd' : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ casselsI M L := hcomm ▸ hnd
    have e1 := loc_le_of_not_dvd v (K := L.1 ⊓ M.1) (N := L.1) hnd
    have e2 := loc_le_of_not_dvd v (K := M.1 ⊓ L.1) (N := M.1) hnd'
    rw [inf_comm M.1 L.1] at e2
    exact le_antisymm (e1.trans (loc_mono v inf_le_right)) (e2.trans (loc_mono v inf_le_left))

end QuadFormsKB.Lattices
