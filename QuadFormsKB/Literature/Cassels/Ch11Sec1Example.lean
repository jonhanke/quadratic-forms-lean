/-
# Cassels, Chapter 11, Lemma 1.5: spinor genera of more than one class

**Layer:** $V = \mathbb Q^n$ with the diagonal form $\phi = q_1x_1^2 + \dots + q_nx_n^2$, $q_j$ the $j$-th odd prime
(`casselsOddPrimeForm`; 0-based: the coefficient of $x_j$ is the $(j+1)$-st prime `Nat.nth Nat.Prime (j + 1)`, so
$3, 5, 7, 11, \dots$); the lattice $\Lambda = \mathbb Z^n$ = `stdLat`; Cassels' (proper) spinor genus
`SameProperSpinorGenus`; classes `IsIsometric`.

**Proves** Cassels' Lemma 1.5 (p. 203): *for every $n \ge 3$ there are lattices whose spinor genus contains more than
one class* (`exists_sameProperSpinorGenus_not_isIsometric`). Cassels' proof, followed here: the genus of $\Lambda$ is
one spinor genus (Lemma 3.6, Corollary, with $U_p \subseteq \theta(\Lambda_p)$ from Lemma 3.7 at odd $p$, since at most
one $q_j$ is divisible by $p$, and from Lemma 3.8 (ii) at $p = 2$, all $q_j$ being $2$-adic units; Cassels cites
Theorem 1.3); $1$ is represented by $\phi$ on $\Lambda_p$ for every $p$ and over $\mathbb Q$
($3\cdot1^2 + 5\cdot1^2 + 7\cdot2^2 = 6^2$), hence by some lattice $\Gamma$ of the genus (Cassels: Ch. 9,
Theorem 1.3; here O'Meara 102:5, `exists_sameGenus_represents`); but $\phi(x) \ge 3$ for $0 \ne x \in \Lambda$.
(The scan has lost the definition of $\phi(b_j)$; it is reconstructed from the proof: $\phi(b_j) = q_j$.)
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3Dyadic
import QuadFormsKB.Literature.Cassels.Ch11Sec3
import QuadFormsKB.Literature.OMeara.Sec102Rep

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- **Cassels' form of Lemma 1.5** (Ch. 11, p. 203): $\phi = q_1x_1^2 + \dots + q_nx_n^2$ with $q_j$ the $j$-th odd
prime ($3, 5, 7, \dots$; 0-based, the coefficient of $x_j$ is `Nat.nth Nat.Prime (j + 1)`). -/
def casselsOddPrimeForm (n : ℕ) : QuadForm ℚ n := QuadForm.diag fun j => ((Nat.nth Nat.Prime (j.1 + 1) : ℕ) : ℚ)

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.NF

section Helpers

/-- The vector $(a, b, c, 0, \dots, 0)$. -/
def vec3 {m : ℕ} {K : Type*} [Zero K] (a b c : K) : Fin (m + 3) → K :=
  Fin.cons a (Fin.cons b (Fin.cons c (0 : Fin m → K)))

theorem evalIn_vec3 {m : ℕ} {K : Type*} [Field K] {_ : Algebra ℚ K} (a b c : K) :
    (casselsOddPrimeForm (m + 3)).evalIn K (vec3 a b c) = 3 * a ^ 2 + 5 * b ^ 2 + 7 * c ^ 2 := by
  rw [casselsOddPrimeForm, QuadForm.evalIn_diag]
  simp [Fin.sum_univ_succ, vec3, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
    Nat.nth_prime_three_eq_seven]
  ring

theorem locGram_one_cassels {m : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) (k l : Fin m) :
    locGram (casselsOddPrimeForm m) v 1 k l =
      if k = l then algebraMap ℚ (v.adicCompletion ℚ) (2 * ((Nat.nth Nat.Prime (k.1 + 1) : ℕ) : ℚ)) else 0 := by
  by_cases h : k = l
  · subst h
    simp [locGram, QuadForm.hessian, casselsOddPrimeForm, QuadForm.diag, Matrix.diagonal_transpose,
      Matrix.diagonal_add, two_mul]
  · simp [locGram, QuadForm.hessian, casselsOddPrimeForm, QuadForm.diag, Matrix.diagonal_transpose,
      Matrix.diagonal_add, h]

theorem val_natCast_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) (h : (k : 𝓞 ℚ) ∉ v.asIdeal) :
    Valued.v ((k : ℕ) : v.adicCompletion ℚ) = 1 := by
  have hπ : ¬ π v ∣ ι v (k : 𝓞 ℚ) := by rwa [π_dvd_ι_iff]
  have hu : IsUnit (ι v (k : 𝓞 ℚ)) := DVR.dvr_isUnit_of_not_dvd (irreducible_π v) hπ
  have := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hu
  rw [map_natCast] at this
  simpa using this

theorem not_mem_of_two_mem {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    (3 : 𝓞 ℚ) ∉ v.asIdeal ∧ (5 : 𝓞 ℚ) ∉ v.asIdeal ∧ (7 : 𝓞 ℚ) ∉ v.asIdeal := by
  refine ⟨fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_),
    fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_),
    fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)⟩
  · have := v.asIdeal.sub_mem h h2
    rwa [show (3 : 𝓞 ℚ) - 2 = 1 by norm_num] at this
  · have := v.asIdeal.sub_mem h (v.asIdeal.mul_mem_left 2 h2)
    rwa [show (5 : 𝓞 ℚ) - 2 * 2 = 1 by norm_num] at this
  · have := v.asIdeal.sub_mem h (v.asIdeal.mul_mem_left 3 h2)
    rwa [show (7 : 𝓞 ℚ) - 3 * 2 = 1 by norm_num] at this

theorem at_most_one_mem (v : HeightOneSpectrum (𝓞 ℚ)) :
    ¬ ((3 : 𝓞 ℚ) ∈ v.asIdeal ∧ (5 : 𝓞 ℚ) ∈ v.asIdeal) ∧ ¬ ((3 : 𝓞 ℚ) ∈ v.asIdeal ∧ (7 : 𝓞 ℚ) ∈ v.asIdeal) ∧
      ¬ ((5 : 𝓞 ℚ) ∈ v.asIdeal ∧ (7 : 𝓞 ℚ) ∈ v.asIdeal) := by
  refine ⟨fun ⟨h3, h5⟩ => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_),
    fun ⟨h3, h7⟩ => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_),
    fun ⟨h5, h7⟩ => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)⟩
  · have := v.asIdeal.sub_mem (v.asIdeal.mul_mem_left 2 h3) h5
    rwa [show (2 : 𝓞 ℚ) * 3 - 5 = 1 by norm_num] at this
  · have := v.asIdeal.sub_mem h7 (v.asIdeal.mul_mem_left 2 h3)
    rwa [show (7 : 𝓞 ℚ) - 2 * 3 = 1 by norm_num] at this
  · have := v.asIdeal.sub_mem (v.asIdeal.mul_mem_left 3 h5) (v.asIdeal.mul_mem_left 2 h7)
    rwa [show (3 : 𝓞 ℚ) * 5 - 2 * 7 = 1 by norm_num] at this

/-- Units $a, b$ of $\mathfrak o_\mathfrak p$ ($\mathfrak p \nmid 2$) with $as^2 + bt^2 = 1$ solvable in $\mathfrak o_\mathfrak p$. -/
theorem rep_pair (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) (a b : v.adicCompletion ℚ)
    (ha : Valued.v a = 1) (hb : Valued.v b = 1) :
    ∃ s t : v.adicCompletion ℚ, Valued.v s ≤ 1 ∧ Valued.v t ≤ 1 ∧ a * s ^ 2 + b * t ^ 2 = 1 := by
  let a' : v.adicCompletionIntegers ℚ := ⟨a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ha.le⟩
  let b' : v.adicCompletionIntegers ℚ := ⟨b, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hb.le⟩
  have ha' : IsUnit a' := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr ha
  have hb' : IsUnit b' := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hb
  obtain ⟨s, t, hst⟩ := Nbr.exists_binary_one_dvr (NF.irreducible_π v) (NF.π_not_dvd_two v h2) ha' hb'
  refine ⟨s, t, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp s.2,
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp t.2, ?_⟩
  have := congrArg (fun x : v.adicCompletionIntegers ℚ => (x : v.adicCompletion ℚ)) hst
  simpa [a', b'] using this

theorem vec3_mem_std (v : HeightOneSpectrum (𝓞 ℚ)) {m : ℕ} {a b c : v.adicCompletion ℚ} (ha : Valued.v a ≤ 1)
    (hb : Valued.v b ≤ 1) (hc : Valued.v c ≤ 1) : (vec3 a b c : Fin (m + 3) → v.adicCompletion ℚ) ∈ std v := by
  rw [mem_std_iff]
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i) i
  · simpa only [vec3, Fin.cons_zero] using ha
  · simpa only [vec3, Fin.cons_zero, Fin.cons_succ] using hb
  · simpa only [vec3, Fin.cons_zero, Fin.cons_succ] using hc
  · simp [vec3]

/-- $33$ is a square in $\mathbb Z_2$ ($33 \equiv 1 \bmod 8$), with a unit square root. -/
theorem exists_sqrt_33 {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ t : v.adicCompletion ℚ, Valued.v t = 1 ∧ t ^ 2 = 33 := by
  have he := ordTwo_spec v
  rw [Tamagawa.Indefinite.ordTwo_eq_one h2] at he
  have h33 : ¬ π v ∣ (33 : v.adicCompletionIntegers ℚ) := by
    have := (Tamagawa.Indefinite.π_dvd_intCast_iff h2 33).not.mpr (by norm_num)
    simpa using this
  have h1 : ¬ π v ∣ (1 : v.adicCompletionIntegers ℚ) := fun h => (irreducible_π v).not_isUnit (isUnit_of_dvd_one h)
  have h3 : π v ^ (2 * 1 + 1) ∣ (1 : v.adicCompletionIntegers ℚ) * 1 ^ 2 - 33 := by
    have := Tamagawa.Indefinite.π_pow_three_dvd_intCast h2 (z := -32) (by norm_num)
    have e : (1 : v.adicCompletionIntegers ℚ) * 1 ^ 2 - 33 = ((-32 : ℤ) : v.adicCompletionIntegers ℚ) := by
      push_cast; norm_num
    rw [e]; exact this
  obtain ⟨s, hs⟩ := (DVR.exists_sq_mod_iff_exists_sq (irreducible_π v) (by simpa [pow_one] using he.1)
    (two_ne_zero' v) 1 he h1 h33).mp ⟨1, h3⟩
  have hs' : s ^ 2 = 33 := by simpa using hs
  have hπs : ¬ π v ∣ s := fun h => h33 (hs' ▸ dvd_pow h two_ne_zero)
  have hu : IsUnit s := DVR.dvr_isUnit_of_not_dvd (irreducible_π v) hπs
  refine ⟨(s : v.adicCompletion ℚ), HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hu, ?_⟩
  exact (show ((s : v.adicCompletion ℚ)) ^ 2 = ((s ^ 2 : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) from rfl).trans
    (by rw [hs']; rfl)

end Helpers

/-- **Cassels, Lemma 1.5** (Ch. 11, p. 203): *for every $n \ge 3$ there are lattices whose spinor genus contains more
than one class*: for $\phi$ = `casselsOddPrimeForm n` and $\Lambda = \mathbb Z^n$ there is a lattice $\Gamma$ in the
(proper) spinor genus of $\Lambda$ that is not isometric to $\Lambda$. -/
@[kb "cassels1978" "Ch. 11, Lemma 1.5, p. 203 (φ(b_j) = q_j reconstructed)"]
theorem exists_sameProperSpinorGenus_not_isIsometric {n : ℕ} (hn : 3 ≤ n) :
    ∃ M : Lat ℚ n, SameProperSpinorGenus (casselsOddPrimeForm n) stdLat M ∧
      ¬ IsIsometric (casselsOddPrimeForm n) (stdLat : Lat ℚ n).1 M.1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  set Q := casselsOddPrimeForm (m + 3) with hQdef
  have hprime : ∀ j : ℕ, (Nat.nth Nat.Prime j : ℚ) ≠ 0 := fun j =>
    Nat.cast_ne_zero.mpr (Nat.prime_nth_prime j).ne_zero
  have hQ : Q.Nondegenerate := QuadForm.nondegenerate_diag fun j => hprime _
  have hL : ∀ v : HeightOneSpectrum (𝓞 ℚ), loc v (stdLat : Lat ℚ (m + 3)).1 = std v := fun v => loc_intVec v
  -- indices
  let i0 : Fin (m + 3) := ⟨0, by omega⟩
  let i1 : Fin (m + 3) := ⟨1, by omega⟩
  let i2 : Fin (m + 3) := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := fun h => by simp [i0, i1] at h
  have h02 : i0 ≠ i2 := fun h => by simp [i0, i2] at h
  have h12 : i1 ≠ i2 := fun h => by simp [i1, i2] at h
  have G0 : ∀ v : HeightOneSpectrum (𝓞 ℚ), locGram Q v 1 i0 i0 = 2 * 3 := fun v => by
    rw [locGram_one_cassels]; simp [i0, Nat.nth_prime_one_eq_three]
  have G1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), locGram Q v 1 i1 i1 = 2 * 5 := fun v => by
    rw [locGram_one_cassels]; simp [i1, Nat.nth_prime_two_eq_five]
  have G2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), locGram Q v 1 i2 i2 = 2 * 7 := fun v => by
    rw [locGram_one_cassels]; simp [i2, Nat.nth_prime_three_eq_seven]
  have horth : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ k l, k ≠ l → locGram Q v 1 k l = 0 := fun v k l hkl => by
    rw [locGram_one_cassels]; simp [hkl]
  have hγ : ∀ v : HeightOneSpectrum (𝓞 ℚ), loc v (stdLat : Lat ℚ (m + 3)).1 = locAct v (1 : GL (Fin (m + 3)) _) (std v) :=
    fun v => by rw [locAct_one]; exact hL v
  -- global representation
  have hx : Q.evalIn ℚ (vec3 (1 / 6 : ℚ) (1 / 6) (1 / 3) : Fin (m + 3) → ℚ) = 1 := by
    rw [evalIn_vec3]; norm_num
  -- local representations
  have hex := exists_sameGenus_represents Q (stdLat : Lat ℚ (m + 3)) one_ne_zero hx (by
    intro v
    rw [hL v, map_one]
    by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
    · obtain ⟨t, ht, ht2⟩ := exists_sqrt_33 h2
      have hti : Valued.v t⁻¹ = 1 := by rw [map_inv₀, ht, inv_one]
      have h2v : Valued.v (2 : v.adicCompletion ℚ) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (2 : v.adicCompletionIntegers ℚ).2
      refine ⟨vec3 0 t⁻¹ (2 * t⁻¹), vec3_mem_std v (by simp) hti.le (by rw [map_mul, hti, mul_one]; exact h2v), ?_⟩
      have ht0 : t ≠ 0 := fun h => by rw [h, map_zero] at ht; exact zero_ne_one ht
      rw [evalIn_vec3]
      field_simp
      rw [ht2]; norm_num
    · obtain ⟨hn1, hn2, hn3⟩ := at_most_one_mem v
      have u3 : (3 : 𝓞 ℚ) ∈ v.asIdeal → (5 : 𝓞 ℚ) ∉ v.asIdeal ∧ (7 : 𝓞 ℚ) ∉ v.asIdeal :=
        fun h => ⟨fun h' => hn1 ⟨h, h'⟩, fun h' => hn2 ⟨h, h'⟩⟩
      have V : ∀ k : ℕ, (k : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (k : v.adicCompletion ℚ) = 1 :=
        fun k hk => val_natCast_eq_one v k hk
      have V3 : (3 : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (3 : v.adicCompletion ℚ) = 1 := fun h => by
        simpa using V 3 (by simpa using h)
      have V5 : (5 : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (5 : v.adicCompletion ℚ) = 1 := fun h => by
        simpa using V 5 (by simpa using h)
      have V7 : (7 : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (7 : v.adicCompletion ℚ) = 1 := fun h => by
        simpa using V 7 (by simpa using h)
      by_cases e3 : (3 : 𝓞 ℚ) ∈ v.asIdeal
      · obtain ⟨e5, e7⟩ := u3 e3
        obtain ⟨s, t, hs, ht, hst⟩ := rep_pair v h2 5 7 (V5 e5) (V7 e7)
        refine ⟨vec3 0 s t, vec3_mem_std v (by simp) hs ht, ?_⟩
        rw [evalIn_vec3]; linear_combination hst
      · by_cases e5 : (5 : 𝓞 ℚ) ∈ v.asIdeal
        · have e7 : (7 : 𝓞 ℚ) ∉ v.asIdeal := fun h' => hn3 ⟨e5, h'⟩
          obtain ⟨s, t, hs, ht, hst⟩ := rep_pair v h2 3 7 (V3 e3) (V7 e7)
          refine ⟨vec3 s 0 t, vec3_mem_std v hs (by simp) ht, ?_⟩
          rw [evalIn_vec3]; linear_combination hst
        · obtain ⟨s, t, hs, ht, hst⟩ := rep_pair v h2 3 5 (V3 e3) (V5 e5)
          refine ⟨vec3 s t 0, vec3_mem_std v hs ht (by simp), ?_⟩
          rw [evalIn_vec3]; linear_combination hst)
  obtain ⟨M, hMg, z, hzM, hz⟩ := hex
  refine ⟨M, sameProperSpinorGenus_of_sameGenus_rat Q hQ (by omega) stdLat ?_ hMg, ?_⟩
  · intro v u hu
    by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
    · obtain ⟨n3, n5, n7⟩ := not_mem_of_two_mem h2
      have V3 : Valued.v (3 : v.adicCompletion ℚ) = 1 := by simpa using val_natCast_eq_one v 3 (by simpa using n3)
      have V5 : Valued.v (5 : v.adicCompletion ℚ) = 1 := by simpa using val_natCast_eq_one v 5 (by simpa using n5)
      have V7 : Valued.v (7 : v.adicCompletion ℚ) = 1 := by simpa using val_natCast_eq_one v 7 (by simpa using n7)
      refine units_mem_localSpinorNormGroup_two_ternary Q hQ h2 stdLat 1 (hγ v) h01 h02 h12
        (fun l k hlk _ => horth v l k hlk) ?_ (Or.inl ?_) u hu
      · rw [G1, G0, map_mul, map_mul, V3, V5]
      · rw [G2, G0, map_mul, map_mul, V3, V7]
    · obtain ⟨hn1, hn2, hn3⟩ := at_most_one_mem v
      have V : ∀ k : ℕ, (k : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (k : v.adicCompletion ℚ) = 1 :=
        fun k hk => val_natCast_eq_one v k hk
      have V3 : (3 : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (3 : v.adicCompletion ℚ) = 1 := fun h => by
        simpa using V 3 (by simpa using h)
      have V5 : (5 : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (5 : v.adicCompletion ℚ) = 1 := fun h => by
        simpa using V 5 (by simpa using h)
      have V7 : (7 : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (7 : v.adicCompletion ℚ) = 1 := fun h => by
        simpa using V 7 (by simpa using h)
      by_cases e3 : (3 : 𝓞 ℚ) ∈ v.asIdeal
      · have e5 : (5 : 𝓞 ℚ) ∉ v.asIdeal := fun h' => hn1 ⟨e3, h'⟩
        have e7 : (7 : 𝓞 ℚ) ∉ v.asIdeal := fun h' => hn2 ⟨e3, h'⟩
        exact units_mem_localSpinorNormGroup_of_orthogonal Q v hQ h2 stdLat 1 (hγ v) (horth v) h12
          (by rw [G1, G2, map_mul, map_mul, V5 e5, V7 e7]) u hu
      · by_cases e5 : (5 : 𝓞 ℚ) ∈ v.asIdeal
        · have e7 : (7 : 𝓞 ℚ) ∉ v.asIdeal := fun h' => hn3 ⟨e5, h'⟩
          exact units_mem_localSpinorNormGroup_of_orthogonal Q v hQ h2 stdLat 1 (hγ v) (horth v) h02
            (by rw [G0, G2, map_mul, map_mul, V3 e3, V7 e7]) u hu
        · exact units_mem_localSpinorNormGroup_of_orthogonal Q v hQ h2 stdLat 1 (hγ v) (horth v) h01
            (by rw [G0, G1, map_mul, map_mul, V3 e3, V5 e5]) u hu
  · rintro ⟨γ, hγo, hMeq⟩
    have hzM' : z ∈ glImage γ (stdLat : Lat ℚ (m + 3)).1 := by rw [hMeq]; exact hzM
    obtain ⟨w, hw, hwz⟩ := mem_glImage.mp hzM'
    obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hw
    have h1 : Q.evalIn ℚ (intCoe x) = 1 := by
      rw [← evalIn_mulVec_of_mem Q hγo (intCoe x), hwz]; exact hz
    have hint : ∀ j, ∃ k : ℤ, algebraMap (𝓞 ℚ) ℚ (x j) = (k : ℚ) := fun j => by
      obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp (RingOfIntegers.isIntegral_coe (x j))
      exact ⟨k, by simpa using hk.symm⟩
    choose k hk using hint
    have hsum : ∑ j, ((Nat.nth Nat.Prime (j.1 + 1) : ℕ) : ℚ) * ((k j : ℤ) : ℚ) ^ 2 = 1 := by
      rw [← h1, hQdef, casselsOddPrimeForm, QuadForm.evalIn_diag]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      show _ = _ * (algebraMap (𝓞 ℚ) ℚ (x j)) ^ 2
      rw [hk j]
    by_cases hall : ∀ j, k j = 0
    · simp [hall] at hsum
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      have hq : (3 : ℚ) ≤ ((Nat.nth Nat.Prime (j.1 + 1) : ℕ) : ℚ) := by
        have := Nat.nth_monotone Nat.infinite_setOfPred_prime (show 1 ≤ j.1 + 1 by omega)
        rw [Nat.nth_prime_one_eq_three] at this
        exact_mod_cast this
      have hk1 : (1 : ℚ) ≤ ((k j : ℤ) : ℚ) ^ 2 := by
        have : (1 : ℤ) ≤ k j ^ 2 := by nlinarith [sq_pos_of_ne_zero hj]
        exact_mod_cast this
      have hle := Finset.single_le_sum (f := fun j : Fin (m + 3) => ((Nat.nth Nat.Prime (j.1 + 1) : ℕ) : ℚ) *
        ((k j : ℤ) : ℚ) ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)
      nlinarith

end QuadFormsKB.Lattices
