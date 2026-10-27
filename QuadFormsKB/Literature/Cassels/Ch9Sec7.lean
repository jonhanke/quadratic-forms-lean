/-
# Cassels, Chapter 9, §7 (and Theorem 1.4): semi-equivalence

**Layer:** rational forms `f g : QuadForm ℚ n` (Theorem 7.1) and integer-valued forms `QuadForm ℤ n` (Theorem 1.4);
a finite set $P$ of primes = `P : Finset Nat.Primes`; the ring
$\mathbb Z^{(P)} = \{c \in \mathbb Q : \lvert c\rvert_p \le 1 \text{ for all } p \in P\}$ (`intAway P`, Cassels p. 130
and p. 154); equivalence over $\mathbb Z^{(P)}$: $g(S\mathbf x) = f(\mathbf x)$ with $S \in \mathrm{GL}_n(\mathbb Z^{(P)})$
(`EquivAway`); equivalence over $\mathbb Z_p$ of rational forms: $g(S_p\mathbf x) = f(\mathbf x)$ on $\mathbb Q_p^n$
with $S_p \in \mathrm{GL}_n(\mathbb Z_p)$ (`EquivZp`).

**Proves**
* Theorem 7.1 (`equivAway_of_local`): regular rational forms equivalent over $\mathbb Q$ and over $\mathbb Z_p$ for
  each $p \in P$ are equivalent over $\mathbb Z^{(P)}$;
* Theorem 1.4 (`sameGenus_iff_semiEquiv`): two regular integral forms are in the same genus iff they are
  semi-equivalent (equivalent over $\mathbb Z^{(P)}$ for every finite set $P$ of primes).

*Proof of Theorem 7.1 (not Cassels' weak approximation in $O^{+}$, Theorem 7.2, but the lattice form of the same idea,
O'Meara's approximation in the genus):* in $V = (\mathbb Q^n, f)$ let $L = \mathbb Z^n$ and $M = S_\infty^{-1}\mathbb Z^n$
for a rational equivalence $S_\infty$; the hypotheses say $M_p = T_pL_p$ with $T_p \in O(V_p)$ for $p \in P$; glue the
lattice $K$ equal to $M_p$ at $p \in P$ and to $L_p$ elsewhere (in the genus of $L$), and use
`Lattices.exists_isometric_agree` to find $\sigma \in O(V)$ with $\sigma L_p = M_p$ for $p \in P$; then
$S = S_\infty\sigma$ maps $\mathbb Z_p^n$ onto $\mathbb Z_p^n$ for $p \in P$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec4
-- import QuadFormsKB.Literature.Cassels.Ch9Sec5
import QuadFormsKB.Lattices.SALemma1041
import QuadFormsKB.Literature.OMeara.Sec102

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **The ring $\mathbb Z^{(P)}$** of rationals $c$ with $\lvert c\rvert_p \le 1$ for every $p \in P$ (Cassels, Ch. 9,
§1, p. 130; §7, p. 154). For $P = \emptyset$ it is $\mathbb Q$. -/
@[kb "cassels1978" "Ch. 9, §1, p. 130 and §7, p. 154 (the ring ℤ^(P))"]
def intAway (P : Finset Nat.Primes) : Subring ℚ where
  carrier := {c | ∀ p ∈ P, ‖(c : ℚ_[(p : ℕ)])‖ ≤ 1}
  mul_mem' {a b} ha hb p hp := by
    rw [Rat.cast_mul, norm_mul]
    exact mul_le_one₀ (ha p hp) (norm_nonneg _) (hb p hp)
  one_mem' p _ := by simp
  add_mem' {a b} ha hb p hp := by
    rw [Rat.cast_add]
    exact (Padic.nonarchimedean _ _).trans (max_le (ha p hp) (hb p hp))
  zero_mem' p _ := by simp
  neg_mem' {a} ha p hp := by rw [Rat.cast_neg, norm_neg]; exact ha p hp

/-- **Equivalence over $\mathbb Z^{(P)}$** of rational forms: $g(S\mathbf x) = f(\mathbf x)$ for all
$\mathbf x \in \mathbb Q^n$, with $S \in \mathrm{GL}_n(\mathbb Z^{(P)})$ (the entries of $S$ and of $S^{-1}$ lie in
$\mathbb Z^{(P)}$). -/
@[kb "cassels1978" "Ch. 9, §1, p. 130 and §7, p. 154 (equivalence over ℤ^(P))"]
def EquivAway (P : Finset Nat.Primes) (f g : QuadForm ℚ n) : Prop :=
  ∃ S : GL (Fin n) (intAway P), ∀ x : Fin n → ℚ,
    g.evalIn ℚ ((S.val.map (intAway P).subtype) *ᵥ x) = f.evalIn ℚ x

/-- **Equivalence over $\mathbb Z_p$** of rational forms: $g(S_p\mathbf x) = f(\mathbf x)$ for all
$\mathbf x \in \mathbb Q_p^n$, with $S_p \in \mathrm{GL}_n(\mathbb Z_p)$ (Cassels, (7.2), p. 156: entries in
$\mathbb Z_p$ and $\lvert\det S_p\rvert_p = 1$). -/
def EquivZp (p : ℕ) [Fact p.Prime] (f g : QuadForm ℚ n) : Prop :=
  ∃ S : GL (Fin n) ℤ_[p], ∀ x : Fin n → ℚ_[p],
    g.evalIn ℚ_[p] ((S.val.map (PadicInt.Coe.ringHom (p := p))) *ᵥ x) = f.evalIn ℚ_[p] x

/-- The entries of `B ∈ GL_n(F_v)` have valuation at most one if `B` preserves the standard lattice. -/
theorem valued_entry_le_one_of_locAct_std {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (B : GL (Fin n) (v.adicCompletion F)) (h : Lattices.locAct v B (Lattices.std v) = Lattices.std v)
    (i j : Fin n) : Valued.v (B.val i j) ≤ 1 := by
  have h1 : (Pi.single j 1 : Fin n → v.adicCompletion F) ∈ Lattices.std v := by
    rw [Lattices.std, Lattices.mem_ball]
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have h2 : B.val *ᵥ (Pi.single j 1 : Fin n → v.adicCompletion F) ∈ Lattices.std v := by
    rw [← h]; exact Lattices.mem_locAct.mpr ⟨_, h1, rfl⟩
  have h3 := (Lattices.mem_ball v).mp h2 i
  simpa using h3

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion in
/-- A rational number of valuation at most one at `v` has `p`-adic norm at most one. -/
theorem norm_le_one_of_valued_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime]
    (h : p = (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) (c : ℚ)
    (hc : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) c) ≤ 1) : ‖(c : ℚ_[p])‖ ≤ 1 := by
  subst h
  have hmem : algebraMap ℚ (v.adicCompletion ℚ) c ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc
  have := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hmem
  have e : Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (algebraMap ℚ (v.adicCompletion ℚ) c) =
      (c : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) := by
    simp
  rw [e] at this
  exact (PadicInt.mem_subring_iff _).mp this

/-- A rational isometry with `p`-integral entries in both directions (`p ∈ P`) is an equivalence over `ℤ^(P)`. -/
theorem equivAway_of_entries (P : Finset Nat.Primes) (f g : QuadForm ℚ n) (A : GL (Fin n) ℚ)
    (hA : ∀ x : Fin n → ℚ, g.evalIn ℚ (A.val *ᵥ x) = f.evalIn ℚ x)
    (h1 : ∀ p ∈ P, ∀ i j, ‖((A.val i j : ℚ) : ℚ_[(p : ℕ)])‖ ≤ 1)
    (h2 : ∀ p ∈ P, ∀ i j, ‖((A⁻¹.val i j : ℚ) : ℚ_[(p : ℕ)])‖ ≤ 1) : EquivAway P f g := by
  let A' : Matrix (Fin n) (Fin n) (intAway P) := Matrix.of fun i j => ⟨A.val i j, fun p hp => h1 p hp i j⟩
  let B' : Matrix (Fin n) (Fin n) (intAway P) := Matrix.of fun i j => ⟨A⁻¹.val i j, fun p hp => h2 p hp i j⟩
  have hA' : A'.map (intAway P).subtype = A.val := Matrix.ext fun i j => rfl
  have hB' : B'.map (intAway P).subtype = A⁻¹.val := Matrix.ext fun i j => rfl
  have e1 : A' * B' = 1 := by
    apply Matrix.map_injective (intAway P).subtype_injective
    simp only []
    rw [Matrix.map_mul, hA', hB', Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  have e2 : B' * A' = 1 := by
    apply Matrix.map_injective (intAway P).subtype_injective
    simp only []
    rw [Matrix.map_mul, hA', hB', Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  exact ⟨⟨A', B', e1, e2⟩, fun x => by
    change g.evalIn ℚ (A'.map (intAway P).subtype *ᵥ x) = _
    rw [hA']; exact hA x⟩

/-- A ring map between fields over `ℚ` commutes with evaluating a rational form. -/
theorem evalIn_comp_ringHom (Q : QuadForm ℚ n) {K L : Type*} [Field K] [Field L] [Algebra ℚ K]
    [Algebra ℚ L] (φ : K →+* L) (x : Fin n → K) : Q.evalIn L (φ ∘ x) = φ (Q.evalIn K x) := by
  have hf : algebraMap ℚ L = φ.comp (algebraMap ℚ K) := Subsingleton.elim _ _
  simp only [QuadForm.evalIn, map_sum, hf]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

section Adic

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- Equivalence over `ℤ_p` of rational forms gives equivalence over the integers of the completion at `v`. -/
theorem equivZp_adic (v : HeightOneSpectrum (𝓞 ℚ)) (f g : QuadForm ℚ n)
    (h : EquivZp (Rat.HeightOneSpectrum.primesEquiv v : ℕ) f g) :
    ∃ P : GL (Fin n) (v.adicCompletionIntegers ℚ), ∀ x : Fin n → v.adicCompletion ℚ,
      g.evalIn (v.adicCompletion ℚ)
        ((P.val.map (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))) *ᵥ x) =
          f.evalIn (v.adicCompletion ℚ) x := by
  obtain ⟨S, hS⟩ := h
  let e : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] ≃+* v.adicCompletion ℚ :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.toAlgEquiv.toRingEquiv
  let ψ : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] →+* v.adicCompletionIntegers ℚ :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.toAlgEquiv.toRingEquiv.toRingHom
  have hψ : ∀ s : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)],
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ψ s) = e (PadicInt.Coe.ringHom s) := fun s => rfl
  refine ⟨Units.map (RingHom.mapMatrix (m := Fin n) ψ).toMonoidHom S, fun x => ?_⟩
  have hx : x = e ∘ (fun i => e.symm (x i)) := by funext i; simp
  have hmv : ((Units.map (RingHom.mapMatrix (m := Fin n) ψ).toMonoidHom S).val.map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))) *ᵥ x =
      e ∘ ((S.val.map (PadicInt.Coe.ringHom (p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)))) *ᵥ
        (fun i => e.symm (x i))) := by
    funext i
    rw [hx]
    simp only [Function.comp_apply, RingEquiv.symm_apply_apply]
    have := RingHom.map_mulVec e.toRingHom (S.val.map (PadicInt.Coe.ringHom (p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ))))
      (fun i => e.symm (x i)) i
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this]
    have hM : ((Units.map (RingHom.mapMatrix (m := Fin n) ψ).toMonoidHom S).val.map
        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))) =
        (S.val.map (PadicInt.Coe.ringHom (p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)))).map e := by
      exact Matrix.ext fun a b => hψ (S.val a b)
    rw [hM]
  rw [hmv]
  have k1 := evalIn_comp_ringHom g e.toRingHom
    ((S.val.map (PadicInt.Coe.ringHom (p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)))) *ᵥ
        (fun i => e.symm (x i)))
  have k2 := evalIn_comp_ringHom f e.toRingHom (fun i => e.symm (x i))
  have k3 : (e.toRingHom ∘ fun i => e.symm (x i)) = x := hx.symm
  rw [k3] at k2
  exact k1.trans ((congrArg e.toRingHom (hS _)).trans k2.symm)

/-- Theorem 7.1, proved with the completions as `v.adicCompletion ℚ`. -/
theorem equivAway_of_local_aux (P : Finset Nat.Primes) (f g : QuadForm ℚ n) (hf : f.Nondegenerate)
    (hQ : ∃ S : GL (Fin n) ℚ, ∀ x : Fin n → ℚ, g.evalIn ℚ (S.val *ᵥ x) = f.evalIn ℚ x)
    (hP : ∀ p ∈ P, EquivZp (p : ℕ) f g) : EquivAway P f g := by
  classical
  obtain ⟨S, hS⟩ := hQ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, fun x => by simp [QuadForm.evalIn]⟩
  have hcomp : g.compMat S.val = f := Lattices.QuadForm.ext_eval fun x => by
    rw [QuadForm.eval_compMat]; exact hS x
  have hI : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (x : Fin n → K),
      f.evalIn K x = g.evalIn K ((S.val.map (algebraMap ℚ K)) *ᵥ x) := fun K _ _ x => by
    have := Tamagawa.evalIn_compMat_gl g S K x
    rw [hcomp] at this; exact this
  set T₁ : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
    P.image (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm with hT₁
  let Mlat : Lattices.Lat ℚ n :=
    ⟨Lattices.glImage S⁻¹ Lattices.intVec, Lattices.glImage_isLattice _ Lattices.intVec_isLattice⟩
  let L : Lattices.Lat ℚ n := ⟨Lattices.intVec, Lattices.intVec_isLattice⟩
  have hMloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), Lattices.loc v Mlat.1 =
      Lattices.locAct v (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) S)⁻¹ (Lattices.std v) := by
    intro v
    change Lattices.loc v (Lattices.glImage S⁻¹ Lattices.intVec) = _
    rw [Lattices.loc_glImage, Lattices.loc_intVec, map_inv]
  have hT : ∀ v ∈ T₁, ∃ T ∈ Lattices.orthGroup f (v.adicCompletion ℚ),
      Lattices.locAct v T (Lattices.std v) = Lattices.loc v Mlat.1 := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    have hZ : EquivZp (Rat.HeightOneSpectrum.primesEquiv
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p) : ℕ) f g := by
      simpa only [Equiv.apply_symm_apply] using hP p hp
    obtain ⟨P₀, hP₀⟩ := equivZp_adic _ f g hZ
    refine ⟨(GeneralLinearGroup.map (algebraMap ℚ (((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p).adicCompletion ℚ)) S)⁻¹ *
      GeneralLinearGroup.map (algebraMap _ (((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p).adicCompletion ℚ)) P₀, ?_, ?_⟩
    · refine Lattices.mem_orthGroup_of_evalIn f fun z => ?_
      rw [Units.val_mul, ← mulVec_mulVec]
      rw [hI _ (((GeneralLinearGroup.map (algebraMap ℚ (((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p).adicCompletion ℚ)) S)⁻¹).val *ᵥ
        ((GeneralLinearGroup.map (algebraMap _ (((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p).adicCompletion ℚ)) P₀).val *ᵥ z))]
      have h2 := Lattices.mulVec_inv_mulVec (GeneralLinearGroup.map (algebraMap ℚ (((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p).adicCompletion ℚ)) S)
        ((GeneralLinearGroup.map (algebraMap _ (((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p).adicCompletion ℚ)) P₀).val *ᵥ z)
      change g.evalIn _ (((GeneralLinearGroup.map (algebraMap ℚ (((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p).adicCompletion ℚ)) S).val) *ᵥ _) = _
      rw [h2]
      exact hP₀ z
    · rw [Lattices.locAct_mul, Lattices.locAct_map_std, hMloc]
  choose! Tv hTo hTl using hT
  let KF : Lattices.LocFamily ℚ n :=
    { M := fun w => if w ∈ T₁ then Lattices.loc w Mlat.1 else Lattices.std w
      isLattice := fun w => by
        by_cases hw : w ∈ T₁
        · simp only [hw, if_true]; exact Lattices.loc_isLattice w Mlat.2
        · simp only [hw, if_false]; exact (Lattices.LocFamily.std (F := ℚ) (n := n)).isLattice w
      eventually_std := by
        filter_upwards [T₁.finite_toSet.eventually_cofinite_notMem] with w hw
        have hw' : w ∉ T₁ := fun h => hw (Finset.mem_coe.mpr h)
        show (if w ∈ T₁ then _ else _) = _
        rw [if_neg hw'] }
  let K : Lattices.Lat ℚ n := ⟨KF.glue, KF.glue_isLattice⟩
  have hKloc : ∀ w, Lattices.loc w K.1 = KF.M w := KF.loc_glue
  have hKMlat : ∀ v ∈ T₁, Lattices.loc v K.1 = Lattices.loc v Mlat.1 := by
    intro v hv
    rw [hKloc v]
    show (if v ∈ T₁ then _ else _) = _
    rw [if_pos hv]
  have hKL : Lattices.SameGenus f K.1 L.1 := by
    intro w
    by_cases hw : w ∈ T₁
    · refine ⟨(Tv w)⁻¹, Subgroup.inv_mem _ (hTo w hw), ?_⟩
      rw [hKMlat w hw, ← hTl w hw, Lattices.locAct_inv_locAct]
      exact (Lattices.loc_intVec w).symm
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [hKloc w, Lattices.locAct_one]
      show (if w ∈ T₁ then _ else _) = _
      rw [if_neg hw]
      exact (Lattices.loc_intVec w).symm
  have himp : ∀ v ∈ T₁, ∃ e : Fin n → v.adicCompletion ℚ, f.evalIn _ e ≠ 0 ∧
      Lattices.locAct v ((Lattices.symm f (v.adicCompletion ℚ) e : Lattices.orthGroup f _) :
        GL (Fin n) _) (Lattices.loc v K.1) = Lattices.loc v K.1 := by
    intro v _
    obtain ⟨x, -, hx0, hx⟩ := Lattices.exists_symm_locAct_eq f v hf hn (Lattices.loc_isLattice v K.2)
    exact ⟨x, hx0, hx⟩
  obtain ⟨M', ⟨σ, hσ, hσM⟩, hM'⟩ := Lattices.exists_isometric_agree f hf K T₁ himp L hKL
  have hσloc : ∀ v ∈ T₁, Lattices.locAct v (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) σ)
      (Lattices.std v) = Lattices.loc v Mlat.1 := by
    intro v hv
    have h1 := hM' v hv
    rw [← hσM, Lattices.loc_glImage, hKMlat v hv] at h1
    have e1 : Lattices.loc v L.1 = Lattices.std v := Lattices.loc_intVec v
    rw [e1] at h1
    exact h1
  have hAv : ∀ v ∈ T₁, Lattices.locAct v (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) (S * σ))
      (Lattices.std v) = Lattices.std v := by
    intro v hv
    rw [map_mul, Lattices.locAct_mul, hσloc v hv, hMloc v, ← Lattices.locAct_mul, mul_inv_cancel,
      Lattices.locAct_one]
  have hnorm : ∀ p ∈ P, ∀ B : GL (Fin n) ℚ,
      Lattices.locAct ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
        (GeneralLinearGroup.map (algebraMap ℚ _) B) (Lattices.std _) = Lattices.std _ →
      ∀ i j, ‖((B.val i j : ℚ) : ℚ_[(p : ℕ)])‖ ≤ 1 := by
    intro p hp B hB i j
    have := valued_entry_le_one_of_locAct_std _ _ hB i j
    exact norm_le_one_of_valued_le_one _ (p : ℕ) (by simp) _ this
  refine equivAway_of_entries P f g (S * σ) (fun x => ?_) (fun p hp i j => ?_) (fun p hp i j => ?_)
  · rw [Units.val_mul, ← mulVec_mulVec, hS, Lattices.evalIn_mulVec_of_mem f hσ x]
  · exact hnorm p hp _ (hAv _ (Finset.mem_image_of_mem _ hp)) i j
  · refine hnorm p hp _ ?_ i j
    rw [map_inv]
    exact (Lattices.locAct_eq_iff.mp (hAv _ (Finset.mem_image_of_mem _ hp))).symm

end Adic

/-- **Cassels, Theorem 7.1** (Ch. 9, p. 154): *let $f, g$ be regular forms with rational coefficients. Suppose that
they are equivalent over $\mathbb Q$ and over $\mathbb Z_p$ for each $p \in P$. Then they are equivalent over
$\mathbb Z^{(P)}$.* -/
@[kb "cassels1978" "Ch. 9, Thm. 7.1, p. 154"]
theorem equivAway_of_local (P : Finset Nat.Primes) (f g : QuadForm ℚ n) (hf : f.Nondegenerate)
    (hQ : ∃ S : GL (Fin n) ℚ, ∀ x : Fin n → ℚ, g.evalIn ℚ (S.val *ᵥ x) = f.evalIn ℚ x)
    (hP : ∀ p ∈ P, EquivZp (p : ℕ) f g) : EquivAway P f g :=
  equivAway_of_local_aux P f g hf hQ hP

/-- **Semi-equivalence** (Cassels, Ch. 9, §1, p. 130): integral forms $f, g$ are semi-equivalent if they are
equivalent over $\mathbb Z^{(P)}$ for every finite set $P$ of primes. (The end of Cassels' definition is lost in the
scan; equivalence over $\mathbb R$ follows from equivalence over $\mathbb Z^{(\emptyset)} = \mathbb Q$, as in his proof
of the "if" part of Theorem 1.4.) -/
@[kb "cassels1978" "Ch. 9, §1, p. 130 (semi-equivalence)"]
def SemiEquiv (f g : QuadForm ℤ n) : Prop :=
  ∀ P : Finset Nat.Primes, EquivAway P (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ))

/-- Value of the rational form of an integral form over a field of characteristic zero. -/
theorem evalIn_map_rat_eq (Q : QuadForm ℤ n) (K : Type*) [Field K] [CharZero K] (x : Fin n → K) :
    (Q.map (Int.castRingHom ℚ)).evalIn K x = (Q.map (Int.castRingHom K)).eval x := by
  rw [Lattices.evalIn_eq_eval_map, Lattices.QuadForm.map_map,
    RingHom.ext_int ((algebraMap ℚ K).comp (Int.castRingHom ℚ)) (Int.castRingHom K)]

/-- Equivalence over `ℤ_p` of integral forms gives `EquivZp` of the rational forms. -/
theorem equivZp_of_isometricGL (p : ℕ) [Fact p.Prime] (f g : QuadForm ℤ n)
    (h : IsometricGL (g.map (Int.castRingHom ℤ_[p])) (f.map (Int.castRingHom ℤ_[p]))) :
    EquivZp p (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ)) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun x => ?_⟩
  have hc : (g.map (Int.castRingHom ℤ_[p])).compMat S.val = f.map (Int.castRingHom ℤ_[p]) :=
    Lattices.QuadForm.ext_eval fun y => by rw [QuadForm.eval_compMat]; exact hS y
  have h1 := congrArg (QuadForm.map (PadicInt.Coe.ringHom (p := p))) hc
  rw [← QuadForm.map_compMat, Lattices.QuadForm.map_map, Lattices.QuadForm.map_map,
    RingHom.ext_int ((PadicInt.Coe.ringHom (p := p)).comp (Int.castRingHom ℤ_[p])) (Int.castRingHom ℚ_[p])] at h1
  rw [evalIn_map_rat_eq, evalIn_map_rat_eq, ← h1, QuadForm.eval_compMat]

/-- Semi-equivalence follows from being in the same genus (Theorem 7.1 applied to every finite `P`). -/
theorem semiEquiv_of_sameGenus (f g : QuadForm ℤ n) (hf : f.hessian.det ≠ 0) (h : SameGenus f g) :
    SemiEquiv f g := by
  intro P
  have hQ := Lattices.isometricGL_rat_of_sameGenus f g h.hessian_det_eq hf h
  refine equivAway_of_local P _ _ (Lattices.nondegenerate_map_of_det_ne_zero f hf) ?_ ?_
  · obtain ⟨S, hS⟩ := hQ.symm
    exact ⟨S, hS⟩
  · intro p _
    exact equivZp_of_isometricGL p.1 f g (h.1 p.1).symm

/-- Transfer of an equivalence of rational forms over `ℚ` to any `ℚ`-algebra. -/
theorem evalIn_transfer (f g : QuadForm ℚ n) (A : GL (Fin n) ℚ)
    (hA : ∀ x : Fin n → ℚ, g.evalIn ℚ (A.val *ᵥ x) = f.evalIn ℚ x)
    (K : Type*) [CommRing K] [Algebra ℚ K] (x : Fin n → K) :
    g.evalIn K ((A.val.map (algebraMap ℚ K)) *ᵥ x) = f.evalIn K x := by
  have hcomp : g.compMat A.val = f := Lattices.QuadForm.ext_eval fun x => by
    rw [QuadForm.eval_compMat]; exact hA x
  have := Tamagawa.evalIn_compMat_gl g A K x
  rw [hcomp] at this; exact this.symm

/-- A matrix over `ℤ^(P)` invertible over `ℤ^(P)` gives an element of `GL_n(ℤ_p)` for `p ∈ P`. -/
theorem exists_gl_padic (p : ℕ) [Fact p.Prime] (P : Finset Nat.Primes)
    (hp : (⟨p, Fact.out⟩ : Nat.Primes) ∈ P) (S : GL (Fin n) (intAway P)) :
    ∃ T : GL (Fin n) ℤ_[p], T.val.map (PadicInt.Coe.ringHom (p := p)) =
      S.val.map ((algebraMap ℚ ℚ_[p]).comp (intAway P).subtype) := by
  have hb : ∀ c : intAway P, ‖((c : ℚ) : ℚ_[p])‖ ≤ 1 := fun c => c.2 ⟨p, Fact.out⟩ hp
  let t : Matrix (Fin n) (Fin n) ℤ_[p] :=
    Matrix.of fun i j => ⟨(((S.val i j : intAway P) : ℚ) : ℚ_[p]), hb (S.val i j)⟩
  let t' : Matrix (Fin n) (Fin n) ℤ_[p] :=
    Matrix.of fun i j => ⟨(((S⁻¹.val i j : intAway P) : ℚ) : ℚ_[p]), hb (S⁻¹.val i j)⟩
  have ht : t.map (PadicInt.Coe.ringHom (p := p)) = S.val.map ((algebraMap ℚ ℚ_[p]).comp (intAway P).subtype) :=
    Matrix.ext fun i j => by simp [t]; rfl
  have ht' : t'.map (PadicInt.Coe.ringHom (p := p)) =
      S⁻¹.val.map ((algebraMap ℚ ℚ_[p]).comp (intAway P).subtype) :=
    Matrix.ext fun i j => by simp [t']; rfl
  have hinj : Function.Injective (PadicInt.Coe.ringHom (p := p)) := Subtype.val_injective
  have e1 : t * t' = 1 := by
    apply Matrix.map_injective hinj
    simp only []
    rw [Matrix.map_mul, ht, ht', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : t' * t = 1 := by
    apply Matrix.map_injective hinj
    simp only []
    rw [Matrix.map_mul, ht, ht', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨⟨t, t', e1, e2⟩, ht⟩

/-- The image in `ℚ_p` of the value of an integral form at a `ℤ_p`-vector. -/
theorem coe_eval_map_padic (p : ℕ) [Fact p.Prime] (Q : QuadForm ℤ n) (x : Fin n → ℤ_[p]) :
    PadicInt.Coe.ringHom (p := p) ((Q.map (Int.castRingHom ℤ_[p])).eval x) =
      (Q.map (Int.castRingHom ℚ_[p])).eval (fun i => PadicInt.Coe.ringHom (p := p) (x i)) := by
  rw [← Lattices.eval_map_comp, Lattices.QuadForm.map_map,
    RingHom.ext_int ((PadicInt.Coe.ringHom (p := p)).comp (Int.castRingHom ℤ_[p])) (Int.castRingHom ℚ_[p])]

/-- Semi-equivalent integral forms are in the same genus. -/
theorem sameGenus_of_semiEquiv (f g : QuadForm ℤ n) (h : SemiEquiv f g) : SameGenus f g := by
  constructor
  · intro p hp
    obtain ⟨S, hS⟩ := h {⟨p, hp.out⟩}
    obtain ⟨T, hT⟩ := exists_gl_padic p {⟨p, hp.out⟩} (Finset.mem_singleton_self _) S
    let Sq : GL (Fin n) ℚ := Units.map (RingHom.mapMatrix (m := Fin n) (intAway {⟨p, hp.out⟩}).subtype).toMonoidHom S
    have hSq : ∀ x : Fin n → ℚ, (g.map (Int.castRingHom ℚ)).evalIn ℚ (Sq.val *ᵥ x) =
        (f.map (Int.castRingHom ℚ)).evalIn ℚ x := hS
    have hx : ∀ x : Fin n → ℚ_[p], (g.map (Int.castRingHom ℚ_[p])).eval ((T.val.map (PadicInt.Coe.ringHom (p := p))) *ᵥ x) =
        (f.map (Int.castRingHom ℚ_[p])).eval x := by
      intro x
      rw [← evalIn_map_rat_eq g ℚ_[p], ← evalIn_map_rat_eq f ℚ_[p], hT]
      exact evalIn_transfer _ _ Sq hSq ℚ_[p] x
    refine IsometricGL.symm ⟨T, fun y => ?_⟩
    apply Subtype.val_injective
    change PadicInt.Coe.ringHom (p := p) _ = PadicInt.Coe.ringHom (p := p) _
    rw [coe_eval_map_padic, coe_eval_map_padic]
    have hmv : (fun i => PadicInt.Coe.ringHom (p := p) ((T.val *ᵥ y) i)) =
        (T.val.map (PadicInt.Coe.ringHom (p := p))) *ᵥ (fun i => PadicInt.Coe.ringHom (p := p) (y i)) :=
      funext fun i => RingHom.map_mulVec _ _ _ i
    rw [hmv]
    exact hx _
  · obtain ⟨S, hS⟩ := h ∅
    let Sq : GL (Fin n) ℚ := Units.map (RingHom.mapMatrix (m := Fin n) (intAway ∅).subtype).toMonoidHom S
    have hSq : ∀ x : Fin n → ℚ, (g.map (Int.castRingHom ℚ)).evalIn ℚ (Sq.val *ᵥ x) =
        (f.map (Int.castRingHom ℚ)).evalIn ℚ x := hS
    let SR : GL (Fin n) ℝ := Units.map (RingHom.mapMatrix (m := Fin n) (algebraMap ℚ ℝ)).toMonoidHom Sq
    refine IsometricGL.symm ⟨SR, fun x => ?_⟩
    rw [← evalIn_map_rat_eq g ℝ, ← evalIn_map_rat_eq f ℝ]
    exact evalIn_transfer _ _ Sq hSq ℝ x

/-- **Cassels, Theorem 1.4** (Ch. 9, p. 130): *two regular integral forms are in the same genus if and only if they
are semi-equivalent.* (Integer-valued forms with $\det H \ne 0$; the "if" part needs no regularity.) -/
@[kb "cassels1978" "Ch. 9, Thm. 1.4, p. 130 (proof: §7, p. 154)"]
theorem sameGenus_iff_semiEquiv (f g : QuadForm ℤ n) (hf : f.hessian.det ≠ 0) :
    SameGenus f g ↔ SemiEquiv f g :=
  ⟨semiEquiv_of_sameGenus f g hf, sameGenus_of_semiEquiv f g⟩

end QuadFormsKB.Siegel
