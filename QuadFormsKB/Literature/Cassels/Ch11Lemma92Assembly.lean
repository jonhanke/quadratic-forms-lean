/-
# Cassels, Chapter 11, proof of Lemma 9.2: assembling $\Gamma$ from its localizations

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Lemma 9.2, pp. 246–248: "We now
construct a lattice $\Gamma$ on the 3-dimensional space $V^{(2)}$ … we define $\Gamma$ in terms of its local completions
$\Gamma_p$" and the final stage ("Then there is a $b \in \mathbb Z$ such that …").

**Conventions.** As in `Ch11Lemma92.lean`. The vector $\mathbf u$, the matrix $W$ (a basis of $\mathbb Z^4 \cap \mathbf u^\perp$
with left inverse $\tilde W$) and $h = $ `gramOf f W` are fixed; $\Gamma$ is a lattice on $(\mathbb Q^3, h)$ in the coordinates $W$.

**Local packages** (`LocalPkg`): at a place $v$ over a prime $p \in S$, $p \ne q$: a lattice $M_v \subseteq \mathfrak o_v^3$ (Cassels'
$\Gamma_p$) with $\theta(M_v) \supseteq U_p$, a modulus $p^N$ and, for every $a$ of the type considered, a residue $b_0$ such that
every $b \equiv b_0 \pmod{p^N}$ makes $c = a - f(\mathbf u)b^2$ represented by $M_v$ and $b\mathbf u + Wz$ primitive at $p$ for every
$z \in M_v$ with $h(z) = c$ (at the special prime $p(0)$: $b\mathbf u + Wz$ or $b\mathbf u - Wz$).

**Proves.** `exists_family_of_pkgs`: from local packages at the primes of $S \setminus \{q\}$ and the condition at $q$, the
datum of the final stage (`L92Datum`) together with finite sets $B$ for every exponent (Chinese remainder theorem). The
places outside $S$ and $q$ need no package: there $\Gamma_p = \mathbb Z_p^4 \cap V^{(2)}$ is unimodular (`not_dvd_hessian_det`).
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92Global
import QuadFormsKB.Literature.Cassels.Ch11Sec9Steps
import QuadFormsKB.Literature.ConwaySloane.Section9Group

open NumberField IsDedekindDomain Matrix QuadFormsKB.Cassels.Ch11L93

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

open QuadFormsKB.Cassels QuadFormsKB.Lattices QuadFormsKB.Cassels.Ch11Sec9Gamma

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **A local package at the place `v`** (Cassels' $\Gamma_p$ and the local conditions on $b$, pp. 246–248), for the form `f`,
the vector `u`, the coordinates `W`, the type `A` (a set of integers $a$) and the special prime `p0`. Fields: `M` the local
lattice ($\Gamma_p$ in the coordinates $W$); `isLattice`; `le_std` $M \subseteq \mathfrak o_v^3$; `units` $U_p \subseteq \theta(\Gamma_p)$
(for any global lattice with localization $M$); `N` the exponent of the modulus; `cond` the local conditions on $b$. -/
structure LocalPkg (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ) (A : ℤ → Prop) (p0 : ℕ)
    (v : HeightOneSpectrum (𝓞 ℚ)) where
  /-- The local lattice $\Gamma_p$. -/
  M : Submodule (v.adicCompletionIntegers ℚ) (Fin 3 → v.adicCompletion ℚ)
  /-- It is a lattice. -/
  isLattice : M.IsLattice (v.adicCompletion ℚ)
  /-- It is contained in $\mathfrak o_v^3$. -/
  le_std : M ≤ std v
  /-- $U_p \subseteq \theta(\Gamma_p)$. -/
  units : ∀ (L : Lat ℚ 3) (hQ : ((gramOf f W).map (Int.castRingHom ℚ)).Nondegenerate), loc v L.1 = M →
    ∀ w : (v.adicCompletion ℚ)ˣ, Valued.v (w : v.adicCompletion ℚ) = 1 → w ∈ localSpinorNormGroup _ hQ v L
  /-- The exponent of the modulus. -/
  N : ℕ
  /-- The local conditions on $b$. -/
  cond : ∀ a : ℤ, A a → ∃ b0 : ℤ, ∀ b : ℤ, b ≡ b0 [ZMOD ((Rat.HeightOneSpectrum.natGenerator v ^ N : ℕ) : ℤ)] →
    (∃ y ∈ M, ((gramOf f W).map (Int.castRingHom ℚ)).evalIn _ y =
      algebraMap ℚ _ ((a - b ^ 2 * f.eval u : ℤ) : ℚ)) ∧
    ∀ z : Fin 3 → ℤ, locVec v (fun i => (z i : ℚ)) ∈ M → (gramOf f W).eval z = a - b ^ 2 * f.eval u →
      PrimAt (Rat.HeightOneSpectrum.natGenerator v) (b • u + W *ᵥ z) ∨
        (Rat.HeightOneSpectrum.natGenerator v = p0 ∧ PrimAt p0 (b • u - W *ᵥ z))

/-! ### Helpers -/

theorem localSpinorNormGroup_eq_of_loc {n : ℕ} {Q : QuadForm ℚ n} (hQ : Q.Nondegenerate) {v : HeightOneSpectrum (𝓞 ℚ)}
    {L L' : Lat ℚ n} (h : loc v L.1 = loc v L'.1) :
    localSpinorNormGroup Q hQ v L = localSpinorNormGroup Q hQ v L' := by
  have hs : locStabV Q v L = locStabV Q v L' := by
    ext g
    change locAct v _ (loc v L.1) = loc v L.1 ↔ locAct v _ (loc v L'.1) = loc v L'.1
    rw [h]
  unfold localSpinorNormGroup; rw [hs]

/-- **$h = f \circ W$ is positive definite** when $f$ is and $\tilde WW = 1$. -/
theorem posDef_gramOf {f : QuadForm ℤ 4} (hf : IntQF.PosDef f) {W : Matrix (Fin 4) (Fin 3) ℤ}
    {Wt : Matrix (Fin 3) (Fin 4) ℤ} (hWt : Wt * W = 1) : IntQF.PosDef (gramOf f W) := by
  intro z hz
  rw [gramOf_eval]
  refine hf _ fun h0 => hz ?_
  have := congrArg (fun x => Wt *ᵥ x) h0
  simpa [mulVec_mulVec, hWt] using this

/-- The set of places over the primes of a finite set is finite. -/
theorem finite_places (S : Finset ℕ) :
    {v : HeightOneSpectrum (𝓞 ℚ) | Rat.HeightOneSpectrum.natGenerator v ∈ S}.Finite := by
  refine (S.finite_toSet.preimage ?_)
  intro v _ w _ h
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

/-- **Primitivity of $b\mathbf u + Wz$ at $p \nmid 2f(\mathbf u)$ when $p \nmid b$** (any $z$). -/
theorem primAt_add_of_not_dvd_b (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ)
    (horth : ∀ z, bl f u (W *ᵥ z) = 0) {p : ℕ} (hp : p.Prime)
    (hpg : ¬ (p : ℤ) ∣ 2 * f.eval u) {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) (z : Fin 3 → ℤ) : PrimAt p (b • u + W *ᵥ z) := by
  intro hall
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h1 : bl f u (b • u + W *ᵥ z) = b * (2 * f.eval u) := by
    rw [bl_add_right, horth, add_zero, bl_smul_right, bl_self]
  have : (p : ℤ) ∣ bl f u (b • u + W *ᵥ z) := by
    rw [bl, dotProduct_mulVec]; exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (hall i) _
  rw [h1] at this
  rcases hpp.dvd_or_dvd this with h | h
  · exact hb h
  · exact hpg h

/-! ### The assembly -/

/-- **Assembling the datum and the finite sets of $b$** (Cassels, pp. 246–249). Let $f$ be positive definite, $q$ a prime,
$\mathbf u$, $W$, $\tilde W$ with $\tilde WW = 1$ and $B(\mathbf u, Wz) = 0$, $S$ a finite set of primes containing $q$ and all
primes dividing $2f(\mathbf u)\det H_f$ (with $q \nmid 2f(\mathbf u)\det H_f$), `A` a set of integers prime to $q$, and suppose
given a local package at every place over $S \setminus \{q\}$ and, at $q$, residues $b_0$ with $q^{2k} \mid a - f(\mathbf u)b^2$ for
$b \equiv b_0 \pmod{q^{2k}}$. Then there is a datum `D` of the final stage (with $\Gamma$ glued from the packages, Cassels'
Theorem 1.1, and the standard lattice elsewhere) such that for every $k$ a finite set $B$ of $b$ serves every $a \in A$. -/
theorem exists_family_of_pkgs (f : QuadForm ℤ 4) (hf : IntQF.PosDef f) {q : ℕ} (hq : q.Prime)
    (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ) (Wt : Matrix (Fin 3) (Fin 4) ℤ) (hWt : Wt * W = 1)
    (horth : ∀ z, bl f u (W *ᵥ z) = 0) (S : Finset ℕ) (hSp : ∀ p ∈ S, p.Prime) (hqS : q ∈ S)
    (hout : ∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ 2 * f.eval u * f.hessian.det)
    (hqg : ¬ (q : ℤ) ∣ 2 * f.eval u * f.hessian.det)
    (A : ℤ → Prop) (hAq : ∀ a, A a → ¬ (q : ℤ) ∣ a) (p0 : ℕ)
    (pkg : ∀ v : HeightOneSpectrum (𝓞 ℚ), Rat.HeightOneSpectrum.natGenerator v ∈ S →
      Rat.HeightOneSpectrum.natGenerator v ≠ q → LocalPkg f u W A p0 v)
    (hqb : ∀ a, A a → ∀ k : ℕ, ∃ b0 : ℤ, ∀ b : ℤ, b ≡ b0 [ZMOD ((q ^ (2 * k) : ℕ) : ℤ)] →
      (q : ℤ) ^ (2 * k) ∣ a - b ^ 2 * f.eval u) :
    ∃ D : L92Datum f q hq, ∀ k : ℕ, ∃ B : Finset ℤ, ∀ a : ℤ, A a → ∃ b ∈ B, LocalOK D k a b := by
  classical
  set h := gramOf f W with hh
  set Qh := h.map (Int.castRingHom ℚ) with hQh
  have hpd := posDef_gramOf hf hWt
  have hQ : Qh.Nondegenerate := nondegenerate_map_of_det_ne_zero h (IntQF.PosDef.nondegenerate hpd)
  have hq2 : q ≠ 2 := by
    rintro rfl; exact hqg (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  let good : HeightOneSpectrum (𝓞 ℚ) → Prop := fun v =>
    Rat.HeightOneSpectrum.natGenerator v ∈ S ∧ Rat.HeightOneSpectrum.natGenerator v ≠ q
  have hbad : ∀ v, ¬ good v → ¬ (Rat.HeightOneSpectrum.natGenerator v : ℤ) ∣ 2 * f.eval u * f.hessian.det := by
    intro v hv
    by_cases hS : Rat.HeightOneSpectrum.natGenerator v ∈ S
    · have : Rat.HeightOneSpectrum.natGenerator v = q := by
        by_contra hne; exact hv ⟨hS, hne⟩
      rw [this]; exact hqg
    · exact hout _ (Rat.HeightOneSpectrum.prime_natGenerator v) hS
  have hhd : ∀ v, ¬ good v → ¬ (Rat.HeightOneSpectrum.natGenerator v : ℤ) ∣ 2 * h.hessian.det := fun v hv =>
    not_dvd_hessian_det f u W Wt hWt horth (Rat.HeightOneSpectrum.prime_natGenerator v) (hbad v hv)
  let Mf : LocFamily ℚ 3 :=
    { M := fun v => if hv : good v then (pkg v hv.1 hv.2).M else std v
      isLattice := fun v => by
        split_ifs with hv
        · exact (pkg v hv.1 hv.2).isLattice
        · exact isLattice_of_bounds v le_rfl le_rfl
      eventually_std := by
        rw [Filter.eventually_cofinite]
        refine (finite_places S).subset fun v hv => ?_
        by_contra hS
        apply hv
        have hng : ¬ good v := fun hg => hS hg.1
        simp only [hng, dite_false] }
  set L : Lat ℚ 3 := ⟨Mf.glue, Mf.glue_isLattice⟩ with hL
  have hloc_good : ∀ v (hv : good v), loc v L.1 = (pkg v hv.1 hv.2).M := fun v hv => by
    rw [show loc v L.1 = Mf.M v from Mf.loc_glue v]; simp only [Mf, hv, dite_true]
  have hloc_bad : ∀ v, ¬ good v → loc v L.1 = std v := fun v hv => by
    rw [show loc v L.1 = Mf.M v from Mf.loc_glue v]; simp only [Mf, hv, dite_false]
  have hqv : ¬ good (placeOf q hq) := fun hv => hv.2 (natGenerator_placeOf q hq)
  have hqd : ¬ (q : ℤ) ∣ h.hessian.det := fun hd => by
    have := hhd _ hqv; rw [natGenerator_placeOf] at this; exact this (dvd_mul_of_dvd_right hd _)
  let D : L92Datum f q hq :=
    { u := u
      W := W
      h := h
      L := L
      S := S
      split := eval_split f u W horth
      posdef := hpd
      intL := by
        rw [le_iff_forall_loc intVec_isLattice]
        intro v
        rw [loc_intVec]
        by_cases hv : good v
        · rw [hloc_good v hv]; exact (pkg v hv.1 hv.2).le_std
        · rw [hloc_bad v hv]
      spn := fun M hM => sameProperSpinorGenus_of_sameGenus_rat Qh hQ le_rfl L (fun v w hw => by
        by_cases hv : good v
        · exact (pkg v hv.1 hv.2).units L hQ (hloc_good v hv) w hw
        · rw [localSpinorNormGroup_eq_of_loc hQ (L' := stdLat) (by rw [hloc_bad v hv]; exact (loc_intVec v).symm)]
          refine (ConwaySloane.mem_localSpinorNormGroup_std_iff_of_not_dvd (by norm_num) h hQ v (hhd v hv) w).mpr ?_
          exact ⟨w, hw, by rw [sqClassOf_of_ne_zero w.ne_zero, Units.mk0_val]⟩) hM
      qS := hqS
      iso_q := by
        have : Fact q.Prime := ⟨hq⟩
        obtain ⟨x, ⟨i, hi⟩, hx⟩ := exists_primitive_padic_of_unimodular q hq2 h hqd le_rfl 0
        refine isotropicIn_adicCompletion_of_padic Qh (placeOf q hq) q (natGenerator_placeOf q hq).symm
          ⟨fun j => (x j : ℚ_[q]), ?_, ?_⟩
        · intro h0
          have h1 := congrFun h0 i
          simp only [Pi.zero_apply, PadicInt.coe_eq_zero] at h1
          exact hi.ne_zero h1
        · rw [evalIn_castHom_rat]
          have := hom_eval_castHom h PadicInt.Coe.ringHom x
          rw [hx] at this
          simpa using this.symm
      rep_q := fun c => by
        have : Fact q.Prime := ⟨hq⟩
        obtain ⟨x, -, hx⟩ := exists_primitive_padic_of_unimodular q hq2 h hqd le_rfl c
        rw [hloc_bad _ hqv]
        exact exists_mem_std_of_padic h (placeOf q hq) q (natGenerator_placeOf q hq) ⟨x, hx⟩
      rep_out := fun v hvS c => by
        have hv : ¬ good v := fun hv => hvS hv.1
        set p := Rat.HeightOneSpectrum.natGenerator v
        have : Fact p.Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
        have hp2 : p ≠ 2 := by
          intro h2; apply hhd v hv; rw [show (p : ℤ) = 2 by exact_mod_cast h2]; exact dvd_mul_right _ _
        obtain ⟨x, hxu, hx⟩ := exists_primitive_padic_of_unimodular p hp2 h
          (fun hd => hhd v hv (dvd_mul_of_dvd_right hd _)) le_rfl c
        rw [hloc_bad v hv]
        exact exists_locPrimitive_std_of_padic h v p rfl ⟨x, hxu, hx⟩
      prim_out := fun v hvS b z hz => by
        have hv : ¬ good v := fun hv => hvS hv.1
        rw [hloc_bad v hv] at hz
        refine primAt_add_of_not_dvd f u W Wt hWt horth (Rat.HeightOneSpectrum.prime_natGenerator v)
          (fun hd => hbad v hv (dvd_mul_of_dvd_left hd _)) b (primAt_of_locPrimitive v z hz) }
  refine ⟨D, fun k => ?_⟩
  set K := k + 1 with hK
  have hpS : ∀ p (hp : p ∈ S ∧ p ≠ q), Rat.HeightOneSpectrum.natGenerator (placeOf p (hSp p hp.1)) ∈ S := by
    intro p hp; rw [natGenerator_placeOf]; exact hp.1
  have hpq : ∀ p (hp : p ∈ S ∧ p ≠ q), Rat.HeightOneSpectrum.natGenerator (placeOf p (hSp p hp.1)) ≠ q := by
    intro p hp; rw [natGenerator_placeOf]; exact hp.2
  let e : ℕ → ℕ := fun p => if hp : p ∈ S ∧ p ≠ q then (pkg _ (hpS p hp) (hpq p hp)).N else 2 * K
  set Mod : ℕ := ∏ p ∈ S, p ^ e p with hModdef
  have hMod : 0 < Mod := Finset.prod_pos fun p hp => pow_pos (hSp p hp).pos _
  refine ⟨(Finset.range Mod).image (fun n : ℕ => (n : ℤ)), fun a ha => ?_⟩
  set g := f.eval u with hg
  -- the condition at a place of a prime of `S ∖ {q}`
  let CondAt : HeightOneSpectrum (𝓞 ℚ) → ℤ → Prop := fun v b =>
    (∃ y ∈ loc v L.1, Qh.evalIn _ y = algebraMap ℚ _ ((a - b ^ 2 * g : ℤ) : ℚ)) ∧
    ∀ z : Fin 3 → ℤ, (fun i => (z i : ℚ)) ∈ L.1 → h.eval z = a - b ^ 2 * g →
      PrimAt (Rat.HeightOneSpectrum.natGenerator v) (b • u + W *ᵥ z) ∨
        (Rat.HeightOneSpectrum.natGenerator v = p0 ∧ PrimAt p0 (b • u - W *ᵥ z))
  have hr : ∀ p ∈ S, ∃ r : ℤ, ∀ b : ℤ, b ≡ r [ZMOD ((p ^ e p : ℕ) : ℤ)] →
      (p = q → (q : ℤ) ^ (2 * K) ∣ a - b ^ 2 * g) ∧
      (∀ hp : p ∈ S ∧ p ≠ q, CondAt (placeOf p (hSp p hp.1)) b) := by
    intro p hpS'
    by_cases hp : p ∈ S ∧ p ≠ q
    · obtain ⟨r, hr⟩ := (pkg _ (hpS p hp) (hpq p hp)).cond a ha
      refine ⟨r, fun b hb => ⟨fun h' => absurd h' hp.2, fun hp' => ?_⟩⟩
      have he : e p = (pkg _ (hpS p hp) (hpq p hp)).N := dif_pos hp
      rw [he] at hb
      have hb' : b ≡ r [ZMOD ((Rat.HeightOneSpectrum.natGenerator (placeOf p (hSp p hp.1)) ^
          (pkg _ (hpS p hp) (hpq p hp)).N : ℕ) : ℤ)] := by rw [natGenerator_placeOf]; exact hb
      obtain ⟨hrep, hprim⟩ := hr b hb'
      have hgood : good (placeOf p (hSp p hp.1)) := ⟨hpS p hp, hpq p hp⟩
      refine ⟨?_, fun z hzL hz => hprim z ?_ hz⟩
      · rw [hloc_good _ hgood]; exact hrep
      · rw [← hloc_good _ hgood]; exact locVec_mem_loc _ hzL
    · have hpq' : p = q := by by_contra hne; exact hp ⟨hpS', hne⟩
      subst hpq'
      obtain ⟨r, hr⟩ := hqb a ha K
      refine ⟨r, fun b hb => ⟨fun _ => hr b ?_, fun hp' => absurd hp' hp⟩⟩
      have he : e p = 2 * K := dif_neg hp
      rw [he] at hb; exact hb
  choose! r hr using hr
  obtain ⟨x, hx⟩ := Ch11Sec9Steps.exists_int_modEq_primePow S hSp e r
  set b : ℤ := x % (Mod : ℤ) with hb
  have hModz : (0 : ℤ) < Mod := by exact_mod_cast hMod
  have hb0 : 0 ≤ b := Int.emod_nonneg _ hModz.ne'
  have hbM : b < Mod := Int.emod_lt_of_pos _ hModz
  have hbx : ∀ p ∈ S, b ≡ r p [ZMOD ((p ^ e p : ℕ) : ℤ)] := by
    intro p hp
    have hdvd : ((p ^ e p : ℕ) : ℤ) ∣ (Mod : ℤ) := by exact_mod_cast Finset.dvd_prod_of_mem _ hp
    exact ((Int.mod_modEq x _).of_dvd hdvd).trans (hx p hp)
  refine ⟨b, Finset.mem_image.mpr ⟨b.toNat, Finset.mem_range.mpr (by omega), by omega⟩, ?_, ?_, ?_⟩
  · -- `q ^ (2k)` divides `c`
    have := ((hr q hqS b (hbx q hqS)).1 rfl)
    exact (pow_dvd_pow _ (by omega)).trans this
  · -- representations at the primes of `S ∖ {q}`
    intro v hvS hvq
    obtain ⟨p, hp, rfl⟩ : ∃ p hp, v = placeOf p hp :=
      ⟨_, _, (placeOf_natGenerator v).symm⟩
    rw [natGenerator_placeOf] at hvS
    have hpq'' : p ≠ q := fun h' => hvq (by subst h'; rfl)
    exact ((hr p hvS b (hbx p hvS)).2 ⟨hvS, hpq''⟩).1
  · -- primitivity
    intro z hzL hz
    have hqb' : ¬ (q : ℤ) ∣ b := by
      intro hqb'
      have h1 := (hr q hqS b (hbx q hqS)).1 rfl
      have h2 : (q : ℤ) ∣ a - b ^ 2 * g := (dvd_pow_self _ (by omega)).trans h1
      have h3 : (q : ℤ) ∣ b ^ 2 * g := Dvd.dvd.mul_right (dvd_pow hqb' two_ne_zero) _
      exact hAq a ha (by have := dvd_add h2 h3; simpa using this)
    have hqgu : ¬ (q : ℤ) ∣ 2 * g := fun h' => hqg (dvd_mul_of_dvd_left h' _)
    have hneg : h.eval (-z) = a - b ^ 2 * g := by
      have := LocalDensity.evalIn_const_mul h (-1) z
      rw [show (fun j => (-1 : ℤ) * z j) = -z by funext j; simp] at this
      change h.evalIn ℤ (-z) = _
      rw [this, ← hz]; ring
    have hnegL : (fun i => (((-z) i : ℤ) : ℚ)) ∈ L.1 := by
      have := L.1.neg_mem hzL
      convert this using 1; funext i; simp
    have hcond : ∀ p (hp : p ∈ S), p ≠ q → CondAt (placeOf p (hSp p hp)) b := by
      intro p hp hpq'
      exact (hr p hp b (hbx p hp)).2 ⟨hp, hpq'⟩
    by_cases hplus : p0 ∈ S ∧ p0 ≠ q ∧ ¬ PrimAt p0 (b • u + W *ᵥ z)
    · -- the sign `-`
      right
      intro p hp hpp
      by_cases hpq' : p = q
      · subst hpq'
        have := primAt_add_of_not_dvd_b f u W horth hpp hqgu hqb' (-z)
        rwa [mulVec_neg, ← sub_eq_add_neg] at this
      · by_cases hp0 : p = p0
        · subst hp0
          have := (hcond p hp hpq').2 z hzL hz
          rw [natGenerator_placeOf] at this
          rcases this with h1 | ⟨-, h1⟩
          · exact absurd h1 hplus.2.2
          · exact h1
        · have := (hcond p hp hpq').2 (-z) hnegL hneg
          rw [natGenerator_placeOf] at this
          rcases this with h1 | ⟨h1, -⟩
          · rwa [mulVec_neg, ← sub_eq_add_neg] at h1
          · exact absurd h1 hp0
    · -- the sign `+`
      left
      intro p hp hpp
      by_cases hpq' : p = q
      · subst hpq'
        exact primAt_add_of_not_dvd_b f u W horth hpp hqgu hqb' z
      · have := (hcond p hp hpq').2 z hzL hz
        rw [natGenerator_placeOf] at this
        rcases this with h1 | ⟨h1, h2⟩
        · exact h1
        · subst h1
          by_contra hn
          exact hplus ⟨hp, hpq', hn⟩

end QuadFormsKB.Cassels.Ch11L92
