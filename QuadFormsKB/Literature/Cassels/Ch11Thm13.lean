/-
# Cassels, Chapter 11, Theorems 1.3 and 1.5: when a genus is one spinor genus

**Layer:** an integer-valued form $f$ = `f : QuadForm ℤ n` in $n \ge 3$ variables (Cassels: "$\phi$ takes integral
values on $\Lambda$"), the space $V = (\mathbb Q^n, f)$ (`f.map (Int.castRingHom ℚ)`), the lattice
$\Lambda = \mathbb Z^n$ = `stdLat` (coordinates in $\mathcal O_{\mathbb Q}$); Cassels' number of spinor genera in the
genus is $g^+(\Lambda)$ = `properSpinorGenusNumber` (`Ch11Sec1.lean`).

*Determinants.* Cassels' $d$ is the determinant of the matrix $(f_{ij})$, $f(x) = \sum f_{ij}x_ix_j$ (Ch. 1, §2); here
$f$ has the Hessian $H = 2(f_{ij})$, so $\det H = 2^n d$. For odd $p$, $p^k \mid d$ iff $p^k \mid \det H$; for a
classically integral $f$ ($d \in \mathbb Z$), $2^T \mid d$ iff $2^{T+n} \mid \det H$. The statements are given with
$\det H$.

**Proves**
* Theorem 1.3 (p. 202; proof in §3, p. 215) (`exists_dvd_det_of_one_lt_properSpinorGenusNumber`): if the genus of
  $\Lambda$ contains more than one spinor genus, then (i) $p^{n(n-1)/2} \mid d$ for some odd prime $p$, or (ii) $f$ is
  classically integral and $2^{n(n-3)/2 + [(n+1)/2]} \mid d$. *Proof* (Cassels: "an immediate consequence of the
  Corollaries to Lemmas 3.6, 3.7 and 3.8"): otherwise $U_p \subseteq \theta(\Lambda_p)$ for every $p$ (Lemma 3.7,
  Cor., at odd $p$; Lemma 3.8, Cor., at $p = 2$), and the genus is one spinor genus (Lemma 3.6, Cor.).
* Theorem 1.5 (p. 203) (`isProperIsometric_of_sameGenus_of_det`): for indefinite $f$ satisfying the negations of
  (i) and (ii), every lattice of the genus of $\Lambda$ is properly equivalent to $\Lambda$ (by Lemma 1.1, Cor. 2:
  every form in the genus of $f$ is properly equivalent to $f$), and $\Lambda$ is improperly equivalent to itself (by
  Lemma 1.1, Cor. 1: so is $f$).

Cassels assumes $n \ge 3$ throughout §3 (p. 207), where Theorem 1.3 is proved.
-/
import QuadFormsKB.Literature.Cassels.Ch11Thm13Int
import QuadFormsKB.Literature.Cassels.Ch11Sec3
import QuadFormsKB.Literature.Cassels.Ch11Sec1Indef
import QuadFormsKB.Equiv.Integral

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- **The local step of Theorem 1.3**: if $f$ satisfies the negations of (i) and (ii), then
$U_p \subseteq \theta(\Lambda_p)$ for every prime $p$ (Lemma 3.7, Cor., at odd $p$; Lemma 3.8, Cor., at $p = 2$). -/
theorem units_mem_localSpinorNormGroup_of_det {n : ℕ} (f : QuadForm ℤ n)
    (hQ : (f.map (Int.castRingHom ℚ)).Nondegenerate)
    (hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ^ (n * (n - 1) / 2) ∣ f.hessian.det)
    (hii : ¬ (IsClassicallyIntegral f ∧ (2 : ℤ) ^ (casselsExpTwo n + n).toNat ∣ f.hessian.det))
    (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    u ∈ localSpinorNormGroup (f.map (Int.castRingHom ℚ)) hQ v stdLat := by
  set Q := f.map (Int.castRingHom ℚ) with hQdef
  have hL : loc v (stdLat : Lat ℚ n).1 = std v := loc_intVec v
  have hγ : loc v (stdLat : Lat ℚ n).1 = locAct v (1 : GL (Fin n) (v.adicCompletion ℚ)) (std v) := by
    rw [locAct_one]; exact hL
  have hint : ∀ x ∈ loc v (stdLat : Lat ℚ n).1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1 := by
    intro x hx; rw [hL] at hx; exact valued_evalIn_le_one_int v f hx
  revert u hu
  by_contra hnot
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
  · have hp2 := (two_mem_iff_natGenerator v).mp h2
    have hv2 := valued_two_dyadic v h2
    apply hii
    refine ⟨?_, ?_⟩
    · have hci := classicallyIntegral_of_not_units_mem_two Q hQ h2 stdLat hint hnot
      have hmem : ∀ i, (Pi.single i 1 : Fin n → v.adicCompletion ℚ) ∈ loc v (stdLat : Lat ℚ n).1 :=
        fun i => by rw [hL]; exact single_mem_std i (by simp)
      have hG : ∀ i j, Valued.v (locGram Q v 1 i j) ≤ Valued.v (2 : v.adicCompletion ℚ) := fun i j => by
        have := hci _ (hmem i) _ (hmem j)
        rw [← locGram_apply_eq]
        simp only [Units.val_one, Matrix.one_mulVec]
        convert this using 3
        exact Subsingleton.elim _ _
      rw [isClassicallyIntegral_iff]
      intro i j hij
      have h := hG i j
      rw [locGram_one_int, hv2, show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, valued_intCast_le_iff, hp2] at h
      have hH : f.hessian i j = f.coeff i j := by
        simp [QuadForm.hessian, f.upper hij]
      rw [hH] at h
      exact even_iff_two_dvd.mpr (by simpa using h)
    · have hd := valued_det_le_of_not_units_mem_two Q hQ h2 stdLat hint hnot 1 hγ
      have hT : 0 ≤ casselsExpTwo n + n := by rw [casselsExpTwo_eq]; positivity
      rw [locGram_one_int_det, ← Int.toNat_of_nonneg hT, valued_intCast_le_iff, hp2] at hd
      exact_mod_cast hd
  · have hd := valued_det_le_of_not_units_mem Q v hQ h2 stdLat (by convert hint; exact Subsingleton.elim _ _) hnot 1 hγ
    rw [locGram_one_int_det, valued_intCast_le_iff] at hd
    exact hi _ hp (fun h => h2 ((two_mem_iff_natGenerator v).mpr h)) hd

/-- **Cassels, Theorem 1.3** (Ch. 11, p. 202): *suppose that $\phi$ takes integral values on the lattice $\Lambda$ and
denote by $d$ the determinant of the corresponding quadratic forms. Suppose that the genus of $\Lambda$ contains more
than one spinor genus. Then at least one of the following must occur: (i) there is an odd prime $p$ such that
$p^{n(n-1)/2} \mid d$; (ii) the quadratic forms induced on $\Lambda$ are integral in the classical sense and
$2^{n(n-3)/2 + [(n+1)/2]} \mid d$.* Here $\Lambda = \mathbb Z^n$ with the integer-valued form $f$, $n \ge 3$, and the
divisibilities are stated for $\det H = 2^nd$ (module docstring). -/
@[kb "cassels1978" "Ch. 11, Thm. 1.3, p. 202 (proof: §3, p. 215)"]
theorem exists_dvd_det_of_one_lt_properSpinorGenusNumber {n : ℕ} (hn : 3 ≤ n) (f : QuadForm ℤ n)
    (hQ : (f.map (Int.castRingHom ℚ)).Nondegenerate)
    (h : 1 < properSpinorGenusNumber (f.map (Int.castRingHom ℚ)) stdLat) :
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (p : ℤ) ^ (n * (n - 1) / 2) ∣ f.hessian.det) ∨
      (IsClassicallyIntegral f ∧ (2 : ℤ) ^ (casselsExpTwo n + n).toNat ∣ f.hessian.det) := by
  by_contra hcon
  have hloc := units_mem_localSpinorNormGroup_of_det f hQ
    (fun p hp hp2 hd => hcon (Or.inl ⟨p, hp, hp2, hd⟩)) (fun h => hcon (Or.inr h))
  set Q := f.map (Int.castRingHom ℚ)
  have hsub : genusProperSpinorGenera Q stdLat ⊆ {Quotient.mk (properSpnSetoid Q) stdLat} := by
    rintro c ⟨M, rfl, hM⟩
    rw [Set.mem_singleton_iff]
    exact Quotient.sound (SameProperSpinorGenus.symm Q
      (sameProperSpinorGenus_of_sameGenus_rat Q hQ hn stdLat hloc hM))
  have hle : properSpinorGenusNumber Q stdLat ≤ 1 :=
    (Set.ncard_le_ncard hsub (Set.finite_singleton _)).trans (Set.ncard_singleton _).le
  omega

/-- **Cassels, Theorem 1.5** (Ch. 11, p. 203): *let $f$ be an indefinite form in $n \ge 3$ variables which is
integer-valued and has determinant $d \ne 0$. Suppose that (i) $p^{n(n-1)/2} \nmid d$ for every odd prime $p$; (ii)
either $f$ is not integral in the classical sense or $2^{n(n-3)/2 + [(n+1)/2]} \nmid d$. Then every form in the genus of
$f$ is properly equivalent to $f$. Further, $f$ is improperly equivalent to itself.* In the language of lattices
(Lemma 1.1, Cor. 1 and 2): every lattice in the genus of $\Lambda = \mathbb Z^n$ is properly equivalent to $\Lambda$,
and some $\alpha \in O(V)$ with $\det\alpha = -1$ has $\alpha\Lambda = \Lambda$; divisibilities for $\det H = 2^nd$. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.5, p. 203 (lattice form)"]
theorem isProperIsometric_of_sameGenus_of_det {n : ℕ} (hn : 3 ≤ n) (f : QuadForm ℤ n)
    (hQ : (f.map (Int.castRingHom ℚ)).Nondegenerate) (hind : IsIndefinite (f.map (Int.castRingHom ℚ)))
    (hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ^ (n * (n - 1) / 2) ∣ f.hessian.det)
    (hii : ¬ IsClassicallyIntegral f ∨ ¬ (2 : ℤ) ^ (casselsExpTwo n + n).toNat ∣ f.hessian.det) :
    (∀ M : Lat ℚ n, SameGenus (f.map (Int.castRingHom ℚ)) (stdLat : Lat ℚ n).1 M.1 →
      IsProperIsometric (f.map (Int.castRingHom ℚ)) (stdLat : Lat ℚ n).1 M.1) ∧
    ∃ α : orthGroup (f.map (Int.castRingHom ℚ)) ℚ, ((α : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = -1 ∧
      glImage (α : GL (Fin n) ℚ) (stdLat : Lat ℚ n).1 = (stdLat : Lat ℚ n).1 := by
  set Q := f.map (Int.castRingHom ℚ)
  have hloc := units_mem_localSpinorNormGroup_of_det f hQ hi (fun h => hii.elim (· h.1) (· h.2))
  have hall : ∀ M : Lat ℚ n, SameGenus Q (stdLat : Lat ℚ n).1 M.1 → IsProperIsometric Q (stdLat : Lat ℚ n).1 M.1 :=
    fun M hM => isProperIsometric_of_sameProperSpinorGenus Q hn hQ hind
      (sameProperSpinorGenus_of_sameGenus_rat Q hQ hn stdLat hloc hM)
  refine ⟨hall, ?_⟩
  obtain ⟨x, hx⟩ := ArchTest.exists_evalIn_ne_zero hQ (by omega)
  set α := symm Q ℚ x
  have hM : SameGenus Q (stdLat : Lat ℚ n).1 (Lat.image (α : GL (Fin n) ℚ) stdLat).1 :=
    IsIsometric.sameGenus Q ⟨(α : GL (Fin n) ℚ), α.2, rfl⟩
  obtain ⟨σ, hσ, hσL⟩ := hall _ hM
  refine ⟨α * σ, ?_, ?_⟩
  · have hσ1 : ((σ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = 1 := hσ
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, hσ1, mul_one]
    exact symm_det Q ℚ hx
  · rw [Subgroup.coe_mul, glImage_mul, hσL]
    show glImage (α : GL (Fin n) ℚ) (glImage (α : GL (Fin n) ℚ) (stdLat : Lat ℚ n).1) = _
    rw [← glImage_mul, ← Subgroup.coe_mul, symm_mul_self, Subgroup.coe_one, glImage_one]

end QuadFormsKB.Lattices
