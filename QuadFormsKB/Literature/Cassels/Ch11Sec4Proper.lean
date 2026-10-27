/-
# Cassels, Chapter 11, Lemma 4.2 for proper classes

**Layer:** lattices `Lat F n` in $V = F^n$ over a number field with a regular form $Q$; the genus `SameGenus`, proper
equivalence `IsProperIsometric`; over $\mathbb Q$ Cassels' index `casselsI` (`Ch11Sec4Index.lean`).

**Proves** Cassels' Lemma 4.2 (p. 216) as stated, with $\Gamma$ in the *proper* class of $\Delta$ (the library had
only the variant with an isometric $\Gamma$, `exists_isometric_agree`):
* `exists_isProperIsometric_loc_eq` (over a number field): for $\Lambda, \Delta$ in one genus and a finite set $T$ of
  primes there is $\Gamma$ properly isometric to $\Delta$ with $\Gamma_\mathfrak p = \Lambda_\mathfrak p$ for
  $\mathfrak p \in T$;
* `exists_isProperIsometric_casselsI` (over $\mathbb Q$): $I(\Lambda, \Gamma)$ is prime to every $p \in P_0$.
*Proof* (Cassels: by weak approximation in $O^+(V)$, Ch. 9, Thm. 7.2): $\Delta_p = \delta_p\Lambda_p$ with rotations
$\delta_p$ (genus = proper genus); write $\delta_p^{-1}$ as a product of an even number of symmetries, pad all words to a
common even length $N$, and approximate them by a global product of $N$ symmetries (`exists_symmProd_approx`), a
rotation.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec4Index
import QuadFormsKB.Lattices.SALemma1041
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Literature.Cassels.Ch11Sec4Thm

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Tamagawa.SiegelSpace

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)


open Topology in
/-- Weak approximation for products of symmetries with *anisotropic* global vectors (needs one prime in `T`). -/
theorem exists_symmProd_approx_aniso (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T.Nonempty) :
    ∀ (m : ℕ) (l : ∀ v : HeightOneSpectrum (𝓞 F), List (Fin n → v.adicCompletion F)),
      (∀ v ∈ T, (l v).length = m ∧ ∀ x ∈ l v, Q.evalIn _ x ≠ 0) →
      ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Matrix (Fin n) (Fin n) (v.adicCompletion F)),
        (∀ v ∈ T, U v ∈ 𝓝 (omat (symmProd Q _ (l v)))) →
        ∃ ys : List (Fin n → F), ys.length = m ∧ (∀ y ∈ ys, Q.evalIn F y ≠ 0) ∧
          ∀ v ∈ T, omat (symmProd Q _ (ys.map (locVec v))) ∈ U v := by
  classical
  obtain ⟨v₀, hv₀⟩ := hT
  intro m
  induction m with
  | zero =>
    intro l hl U hU
    refine ⟨[], rfl, by simp, fun v hv => ?_⟩
    have := hU v hv
    rw [List.length_eq_zero_iff.mp (hl v hv).1] at this
    simpa using mem_of_mem_nhds this
  | succ m ih =>
    intro l hl U hU
    have hcons : ∀ v ∈ T, l v = (l v).headD 0 :: (l v).tail := by
      intro v hv
      obtain ⟨a, l', hal⟩ := List.exists_cons_of_length_eq_add_one (hl v hv).1
      rw [hal]; rfl
    have hsplit : ∀ v ∈ T, ∃ A ∈ 𝓝 (omat (symm Q (v.adicCompletion F) ((l v).headD 0))),
        ∃ B ∈ 𝓝 (omat (symmProd Q _ (l v).tail)), ∀ M ∈ A, ∀ N ∈ B, M * N ∈ U v := by
      intro v hv
      have hU' : U v ∈ 𝓝 (omat (symm Q (v.adicCompletion F) ((l v).headD 0)) *
          omat (symmProd Q _ (l v).tail)) := by
        have := hU v hv
        rwa [hcons v hv, symmProd_cons, omat_mul] at this
      have h := (continuous_matmul_joint v).continuousAt (x := (omat (symm Q (v.adicCompletion F) ((l v).headD 0)),
        omat (symmProd Q _ (l v).tail))) |>.preimage_mem_nhds hU'
      obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp h
      refine ⟨A, hA, B, hB, fun M hM N hN => ?_⟩
      have := hAB (Set.mk_mem_prod hM hN)
      simpa only [Set.mem_preimage] using this
    choose! A hA B hB hAB using hsplit
    obtain ⟨ys, hlen, hysa, hys⟩ := ih (fun v => (l v).tail) (fun v hv =>
      ⟨by rw [List.length_tail, (hl v hv).1]; rfl, fun x hx => (hl v hv).2 x (List.mem_of_mem_tail hx)⟩) B hB
    obtain ⟨y, hyT, -⟩ := exists_vec_approx T (fun v => (l v).headD 0)
      (fun v => {y | omat (symm Q (v.adicCompletion F) y) ∈ A v ∧ Q.evalIn (v.adicCompletion F) y ≠ 0})
      fun v hv => by
        have hne : Q.evalIn _ ((l v).headD 0) ≠ 0 := (hl v hv).2 _ (by rw [hcons v hv]; exact List.mem_cons_self)
        exact Filter.inter_mem
          ((continuousAt_symm v Q hne).preimage_mem_nhds (hA v hv))
          ((continuous_evalIn v Q).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hne))
    refine ⟨y :: ys, by rw [List.length_cons, hlen], ?_, fun v hv => ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · have h := (hyT v₀ hv₀).2
        rw [evalIn_locVec] at h
        intro h0
        apply h
        have : Q.eval z = 0 := h0
        rw [this, map_zero]
      · exact hysa z hz
    · rw [List.map_cons, symmProd_cons, omat_mul]
      exact hAB v hv _ (hyT v hv).1 _ (hys v hv)

theorem det_symmProd {K : Type*} [Field K] [Algebra F K] [CharZero K] :
    ∀ l : List (Fin n → K), (∀ x ∈ l, Q.evalIn K x ≠ 0) →
      (((symmProd Q K l : orthGroup Q K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = (-1) ^ l.length
  | [], _ => by simp [symmProd]
  | a :: l, h => by
    rw [symmProd_cons, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, symm_det Q K (h a List.mem_cons_self),
      det_symmProd l (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.length_cons, pow_succ]
    ring

/-- **Cassels, Lemma 4.2** (Ch. 11, p. 216), over a number field: *let $\Lambda, \Delta$ be lattices in the same genus
and let $P_0$ be any finite set of primes. Then there is a lattice $\Gamma$ in the proper equivalence class of $\Delta$
such that* $\Gamma_p = \Lambda_p$ for all $p \in P_0$ (over $\mathbb Q$ equivalent to $p \nmid I(\Lambda, \Gamma)$,
`exists_isProperIsometric_casselsI`). -/
@[kb "cassels1978" "Ch. 11, Lemma 4.2, p. 216 (over a number field; Γ_p = Λ_p for p ∈ P₀)"]
theorem exists_isProperIsometric_loc_eq (hQ : Q.Nondegenerate) (L : Lat F n) (T : Finset (HeightOneSpectrum (𝓞 F)))
    {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    ∃ M' : Lat F n, IsProperIsometric Q M.1 M'.1 ∧ ∀ v ∈ T, loc v M'.1 = loc v L.1 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · exact ⟨M, IsProperIsometric.refl Q M.1, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have h1 : M.1 = L.1 := by
      rw [Submodule.eq_bot_of_subsingleton (p := M.1), Submodule.eq_bot_of_subsingleton (p := L.1)]
    exact ⟨L, h1 ▸ IsProperIsometric.refl Q M.1, fun v _ => rfl⟩
  obtain ⟨x0, hx0⟩ := ArchTest.exists_evalIn_ne_zero hQ hn
  have he : ∀ v : HeightOneSpectrum (𝓞 F), Q.evalIn (v.adicCompletion F) (locVec v x0) ≠ 0 := by
    intro v; rw [evalIn_locVec]; exact (map_ne_zero _).mpr hx0
  have hP : SameProperGenus Q M.1 L.1 := (sameProperGenus_iff_sameGenus Q hQ M.2).mpr hM.symm
  have hword : ∀ v : HeightOneSpectrum (𝓞 F), ∃ l : List (Fin n → v.adicCompletion F), Even l.length ∧
      (∀ x ∈ l, Q.evalIn _ x ≠ 0) ∧
      locAct v ((symmProd Q _ l : orthGroup Q _) : GL (Fin n) _) (loc v M.1) = loc v L.1 := by
    intro v
    obtain ⟨g, hg, hgL⟩ := hP v
    obtain ⟨l, hla, hl⟩ := exists_symmProd_eq Q (v.adicCompletion F) hQ g
    refine ⟨l, ?_, hla, by rw [hl]; exact hgL⟩
    have h := det_symmProd Q l hla
    rw [hl, Tamagawa.mem_soSub.mp hg] at h
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h.symm
  choose l hlev hla hlK using hword
  set N := T.sup fun v => (l v).length
  have hNev : Even N := Finset.sup_induction (p := Even) (by simp) (fun a ha b hb => by
      rcases le_total a b with h | h
      · rw [max_eq_right h]; exact hb
      · rw [max_eq_left h]; exact ha) fun v _ => hlev v
  set l' : ∀ v : HeightOneSpectrum (𝓞 F), List (Fin n → v.adicCompletion F) :=
    fun v => l v ++ List.replicate (N - (l v).length) (locVec v x0)
  have hl' : ∀ v ∈ T, (l' v).length = N ∧ (∀ x ∈ l' v, Q.evalIn _ x ≠ 0) ∧
      symmProd Q _ (l' v) = symmProd Q _ (l v) := by
    intro v hv
    have hle : (l v).length ≤ N := Finset.le_sup (f := fun v => (l v).length) hv
    obtain ⟨k, hk⟩ : Even (N - (l v).length) := (Nat.even_sub hle).mpr (by simp [hNev, hlev v])
    refine ⟨by simp [l']; omega, fun x hx => ?_, ?_⟩
    · rcases List.mem_append.mp hx with h | h
      · exact hla v x h
      · rw [List.eq_of_mem_replicate h]; exact he v
    · simp only [l']; rw [show N - (l v).length = 2 * k by omega, symmProd_append_replicate]
  choose U hU hUσ using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_mem_nhds_locAct_eq v ((symmProd Q _ (l v) : orthGroup Q _) : GL (Fin n) _) (loc_isLattice v M.2)
  obtain ⟨ys, hlen, hysa, hys⟩ := exists_symmProd_approx_aniso Q T hTne N l'
    (fun v hv => ⟨(hl' v hv).1, (hl' v hv).2.1⟩) U (fun v hv => by rw [(hl' v hv).2.2]; exact hU v)
  set γ := symmProd Q F ys
  have hdet : γ ∈ Tamagawa.soSub Q F := by
    rw [Tamagawa.mem_soSub]
    have h := det_symmProd Q ys hysa
    rw [hlen] at h
    exact h.trans (Even.neg_one_pow hNev)
  refine ⟨Lat.image (γ : GL (Fin n) F) M, ⟨γ, hdet, rfl⟩, fun v hv => ?_⟩
  rw [Lat.image, loc_glImage]
  have hγv : GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (γ : GL (Fin n) F) =
      ((symmProd Q _ (ys.map (locVec v)) : orthGroup Q _) : GL (Fin n) _) := by
    rw [← orthMap_symmProd]; rfl
  rw [hγv, hUσ v _ (hys v hv), hlK v]

/-- **Cassels, Lemma 4.2** (Ch. 11, p. 216): *let $\Lambda, \Delta$ be lattices in the same genus and let $P_0$ be any
finite set of primes $p$. Then there is a lattice $\Gamma$ in the proper equivalence class of $\Delta$ such that
$I(\Lambda, \Gamma)$ is not divisible by any $p \in P_0$.* -/
@[kb "cassels1978" "Ch. 11, Lemma 4.2, p. 216"]
theorem exists_isProperIsometric_casselsI {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (P₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) {M : Lat ℚ n} (hM : SameGenus Q L.1 M.1) :
    ∃ M' : Lat ℚ n, IsProperIsometric Q M.1 M'.1 ∧
      ∀ v ∈ P₀, ¬ Rat.HeightOneSpectrum.natGenerator v ∣ casselsI L M' := by
  have hI : latIndex L = latIndex M := latIndex_eq_of_sameGenus_of_nondeg Q hQ hM
  obtain ⟨M', hM', hloc⟩ := exists_isProperIsometric_loc_eq Q hQ L P₀ hM
  refine ⟨M', hM', fun v hv => ?_⟩
  have hI' : latIndex L = latIndex M' := by
    obtain ⟨γ, -, hγ⟩ := hM'
    have h1 : SameGenus Q M.1 M'.1 := IsIsometric.sameGenus Q ⟨γ, γ.2, hγ⟩
    exact latIndex_eq_of_sameGenus_of_nondeg Q hQ (hM.trans Q h1)
  exact (loc_eq_iff_not_dvd_casselsI hI' v).mp (hloc v hv).symm

end QuadFormsKB.Lattices
