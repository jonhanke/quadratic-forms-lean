/-
# Cassels, Chapter 11, §4: Lemma 4.5 (a local normal form for lattices with $I_p = p$)

**Layer:** $\mathbb Z$-lattices `Lat ℚ n` with the form $Q$ = `Q : QuadForm ℚ n`; at an odd finite place $v$ with
prime $p$ = `Rat.HeightOneSpectrum.natGenerator v`, the localizations `loc v L.1` in $\mathbb Q_p^n$, the bilinear
form $B(x, y) = Q(x+y) - Q(x) - Q(y) = 2\phi(x, y)$ (`qbil`). Cassels' local index $I(\Lambda_p, \Gamma_p)$ is "the
power of $p$ dividing $I(\Lambda, \Gamma)$" (p. 219), so "$I(\Lambda_p, \Gamma_p) = p$" is stated as
$p \mid I(\Lambda, \Gamma)$, $p^2 \nmid I(\Lambda, \Gamma)$.

**Proves**
* Lemma 4.5 (p. 219) (`exists_hyperbolic_basis_of_casselsI`): if the forms on $\Lambda_p$, $\Gamma_p$ are integral
  with unit determinant and $I(\Lambda_p, \Gamma_p) = p$, there are $b_0, \dots, b_{n-1} \in V_p$ with
  $\phi(b_0) = \phi(b_1) = 0$, $\phi(b_0, b_1) = 1/p$, $\phi(b_i, b_j) = 0$ ($i \le 1 < j$), such that
  $pb_0, b_1, b_2, \dots$ and $b_0, pb_1, b_2, \dots$ are bases of $\Lambda_p$, $\Gamma_p$ (0-based: Cassels'
  $b_1, b_2$ are $b_0, b_1$ here).
* The step of the proof of Theorem 4.1 (p. 220) (`exists_soSub_locAct_eq_of_casselsI`): then the rotation
  $\beta_p$: $b_0 \mapsto p^{-1}b_0$, $b_1 \mapsto pb_1$, $b_j \mapsto b_j$ ($j \ge 2$) maps $\Lambda_p$ onto
  $\Gamma_p$ and $\theta(\beta_p) = p\,(\mathbb Q_p^\times)^2$ (Cassels: by the argument of Ch. 10, Thm. 3.2;
  $\beta_p = \tau_{b_0 - b_1}\tau_{b_0 - pb_1}$ up to the order of the factors).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec4Index
import QuadFormsKB.Literature.Cassels.Ch11Sec3

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Tamagawa.SiegelSpace

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ} (Q : QuadForm ℚ n)

/-! ### Group-theoretic and global-to-local helpers -/

/-- In a finite abelian group $G$ of order $pm$ with $p \nmid m$, every $p$-torsion element is a multiple of a
given element $a$ of order $p$. -/
theorem mem_zmultiples_of_nsmul_eq_zero {G : Type*} [AddCommGroup G] [Finite G] (p m : ℕ) [hp : Fact p.Prime]
    (hcard : Nat.card G = p * m) (hm : ¬ p ∣ m) {a : G} (ha0 : a ≠ 0) (hpa : p • a = 0) {g : G}
    (hg : p • g = 0) : g ∈ AddSubgroup.zmultiples a := by
  by_contra hng
  have hord : addOrderOf a = p := by
    have h1 : addOrderOf a ∣ p := addOrderOf_dvd_of_nsmul_eq_zero hpa
    rcases (Nat.dvd_prime hp.out).mp h1 with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) ha0
    · exact h
  have hH : Nat.card (AddSubgroup.zmultiples a) = p := by rw [Nat.card_zmultiples, hord]
  have hq := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddSubgroup.zmultiples a)
  rw [hH, hcard] at hq
  have hqm : Nat.card (G ⧸ AddSubgroup.zmultiples a) = m := by
    have := hp.out.pos
    exact (Nat.eq_of_mul_eq_mul_left this (hq.trans (mul_comm _ _))).symm
  set q : G ⧸ AddSubgroup.zmultiples a := (g : G ⧸ AddSubgroup.zmultiples a) with hqdef
  have hq0 : q ≠ 0 := fun h => hng ((QuotientAddGroup.eq_zero_iff g).mp h)
  have hqp : p • q = 0 := by
    rw [hqdef, ← QuotientAddGroup.mk_nsmul, hg]; rfl
  have hordq : addOrderOf q = p := by
    have h1 : addOrderOf q ∣ p := addOrderOf_dvd_of_nsmul_eq_zero hqp
    rcases (Nat.dvd_prime hp.out).mp h1 with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hq0
    · exact h
  have : p ∣ Nat.card (G ⧸ AddSubgroup.zmultiples a) := hordq ▸ addOrderOf_dvd_natCard q
  rw [hqm] at this
  exact hm this

section Global

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem asIdeal_eq_span_loc :
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

private theorem natCast_mem_asIdeal_loc (m : ℕ) :
    (m : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ m := by
  rw [asIdeal_eq_span_loc, Ideal.mem_span_singleton, ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)),
    map_natCast, map_natCast, Int.natCast_dvd_natCast]

private theorem natGenerator_notMem_loc {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  intro h
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [asIdeal_eq_span_loc v, Ideal.span_le]; simpa using h
  exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)

/-- **Local-global at one prime:** if $y \in M_\mathfrak p$ and $p\,y \in M$ then $y \in M$. -/
private theorem mem_of_loc_of_smul_mem_loc {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : M.IsLattice ℚ)
    {y : Fin n → ℚ} (h1 : locVec v y ∈ loc v M) (h2 : Rat.HeightOneSpectrum.natGenerator v • y ∈ M) : y ∈ M := by
  rw [mem_iff_forall_loc hM]
  intro w
  rcases eq_or_ne w v with rfl | hw
  · exact h1
  · refine locVec_mem_loc_of_smul_mem w (natGenerator_notMem_loc v hw) ?_
    rwa [Nat.cast_smul_eq_nsmul]

/-- **From the global index to a local generator.** If $p \mid I(X, Y)$ and $p^2 \nmid I(X, Y)$, there is
$b \in X_p \setminus Y_p$ with $pb \in Y_p$ and $X_p \subseteq Y_p + \mathfrak o_p b$. -/
theorem exists_local_gen (X Y : Lat ℚ n)
    (hp : Rat.HeightOneSpectrum.natGenerator v ∣ casselsI X Y)
    (hp2 : ¬ Rat.HeightOneSpectrum.natGenerator v ^ 2 ∣ casselsI X Y) :
    ∃ b ∈ loc v X.1, b ∉ loc v Y.1 ∧
      (Rat.HeightOneSpectrum.natGenerator v : v.adicCompletion ℚ) • b ∈ loc v Y.1 ∧
      ∀ y ∈ loc v X.1, ∃ c : v.adicCompletionIntegers ℚ, y - c • b ∈ loc v Y.1 := by
  classical
  set p := Rat.HeightOneSpectrum.natGenerator v with hpdef
  have hpp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have : Fact p.Prime := ⟨hpp⟩
  set K : Lat ℚ n := ⟨X.1 ⊓ Y.1, isLattice_inf_aux X.2 Y.2⟩ with hK
  have hne : casselsI X Y ≠ 0 := relIndex_ne_zero (L := K) (M := X) inf_le_left
  have hrel : casselsI X Y = K.1.toAddSubgroup.relIndex X.1.toAddSubgroup := rfl
  obtain ⟨a, haX, haK, hpaK⟩ := exists_of_prime_dvd_relIndex (H := K.1.toAddSubgroup)
    (K := X.1.toAddSubgroup) p (hrel ▸ hp) (hrel ▸ hne)
  have haY : a ∉ Y.1 := fun h => haK ⟨haX, h⟩
  have hpaY : p • a ∈ Y.1 := hpaK.2
  have hbY : locVec v a ∉ loc v Y.1 := fun h => haY (mem_of_loc_of_smul_mem_loc v Y.2 h hpaY)
  obtain ⟨m, hm⟩ := hp
  have hmp : ¬ p ∣ m := by
    intro h
    exact hp2 (by rw [hm, pow_two]; exact Nat.mul_dvd_mul_left p h)
  have hpb : (p : v.adicCompletion ℚ) • locVec v a ∈ loc v Y.1 := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul]
    exact locVec_mem_loc v hpaY
  -- generation
  have hgen : ∀ x ∈ X.1, locVec v x ∈ loc v Y.1 ⊔ Submodule.span (v.adicCompletionIntegers ℚ) {locVec v a} := by
    intro x hx
    have : Finite (X.1.toAddSubgroup ⧸ K.1.toAddSubgroup.addSubgroupOf X.1.toAddSubgroup) := by
      have : (K.1.toAddSubgroup.addSubgroupOf X.1.toAddSubgroup).FiniteIndex := ⟨hne⟩
      exact AddSubgroup.finite_quotient_of_finiteIndex
    set G := X.1.toAddSubgroup ⧸ K.1.toAddSubgroup.addSubgroupOf X.1.toAddSubgroup
    have hcard : Nat.card G = p * m := by
      rw [← AddSubgroup.index_eq_card]; exact hm
    set ā : G := QuotientAddGroup.mk ⟨a, haX⟩ with hā
    have hā0 : ā ≠ 0 := by
      intro h
      exact haK (AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h))
    have hāp : p • ā = 0 := by
      rw [hā, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact AddSubgroup.mem_addSubgroupOf.mpr hpaK
    set g : G := QuotientAddGroup.mk ⟨x, hx⟩ with hg
    have hmg : p • (m • g) = 0 := by
      rw [← mul_nsmul', ← hcard]; exact card_nsmul_eq_zero'
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (mem_zmultiples_of_nsmul_eq_zero p m hcard hmp hā0 hāp hmg)
    have hmem : m • x - k • a ∈ K.1 := by
      have h0 : (m • g) - k • ā = 0 := by rw [← hk]; exact sub_self _
      rw [hg, hā, ← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_sub,
        QuotientAddGroup.eq_zero_iff] at h0
      exact (AddSubgroup.mem_addSubgroupOf.mp h0)
    have hmN : (m : 𝓞 ℚ) • x ∈ Y.1 ⊔ Submodule.span (𝓞 ℚ) {a} := by
      have e : (m : 𝓞 ℚ) • x = (m • x - k • a) + (k : 𝓞 ℚ) • a := by
        rw [Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]; abel
      rw [e]
      exact Submodule.add_mem_sup (hmem.2) (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a))
    have hloc := locVec_mem_loc_of_smul_mem v (M := Y.1 ⊔ Submodule.span (𝓞 ℚ) {a}) (t := (m : 𝓞 ℚ))
      (fun h => hmp ((natCast_mem_asIdeal_loc v m).mp h)) hmN
    refine (?_ : loc v (Y.1 ⊔ Submodule.span (𝓞 ℚ) {a}) ≤ _) hloc
    rw [loc, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy2
    rw [map_add, locVec_smul_int]
    exact Submodule.add_mem_sup (locVec_mem_loc v hy1)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  refine ⟨locVec v a, locVec_mem_loc v haX, hbY, hpb, fun y hy => ?_⟩
  have hle : loc v X.1 ≤ loc v Y.1 ⊔ Submodule.span (v.adicCompletionIntegers ℚ) {locVec v a} := by
    rw [loc, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact hgen z hz
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp (hle hy)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy2
  exact ⟨c, by rwa [add_sub_cancel_right]⟩

end Global

/-! ### Local helpers: valuations, unimodular pairing, Hensel -/

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Kv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- $v(p) = e^{-1}$ for the prime $p$ of $v$. -/
theorem valued_natGenerator :
    Valued.v ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : Kv) = WithZero.exp (-1 : ℤ) := by
  have hne : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ≠ 0 := by
    exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero
  have : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : Kv) =
      algebraMap (𝓞 ℚ) Kv (Rat.HeightOneSpectrum.natGenerator v : ℕ) := by simp
  rw [this]
  exact (valued_algebraMap_int (v := v) _).trans
    (HeightOneSpectrum.intValuation_singleton v hne (asIdeal_eq_span_loc v))

variable {v}

/-- Discreteness: $v(t) < 1 \Rightarrow v(t/P) \le 1$ for a uniformizer $P$. -/
theorem loc45_valued_div_le_one {P : Kv} (hP : Valued.v P = WithZero.exp (-1 : ℤ)) {t : Kv}
    (ht : Valued.v t < 1) : Valued.v (t / P) ≤ 1 := by
  have h1 : Valued.v t ≤ WithZero.exp (-1 : ℤ) := HN.valued_le_exp_neg_one v ht
  rw [map_div₀, hP]
  exact div_le_one_of_le₀ h1 zero_le

theorem smul_mem_of_valued_le_one {M : Submodule 𝔬 (Fin n → Kv)} {y : Fin n → Kv} (hy : y ∈ M) {c : Kv}
    (hc : Valued.v c ≤ 1) : c • y ∈ M :=
  M.smul_mem (⟨c, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩ : 𝔬) hy

/-- **Primitive vectors of a unimodular lattice pair to a unit with something.** If $x \in \Lambda$ and
$\lvert B(x, c)\rvert < 1$ for all $c \in \Lambda$ then $x \in P\Lambda$ ($P$ a uniformizer). -/
theorem inv_smul_mem_of_pairing_lt {P : Kv} (hP : Valued.v P = WithZero.exp (-1 : ℤ))
    {Λ : Submodule 𝔬 (Fin n → Kv)} (hint : ∀ x ∈ Λ, Valued.v (Q.evalIn Kv x) ≤ 1)
    {γ : GL (Fin n) Kv} (hγ : Λ = locAct v γ (std v)) (hdet : Valued.v (locGram Q v γ).det = 1)
    {x : Fin n → Kv} (hx : x ∈ Λ) (h : ∀ c ∈ Λ, Valued.v (qbil Q Kv x c) < 1) : P⁻¹ • x ∈ Λ := by
  classical
  set G := locGram Q v γ with hG
  have hmem : ∀ k, γ.val *ᵥ Pi.single k 1 ∈ Λ := fun k => by
    rw [hγ, mem_locAct]; exact ⟨_, single_mem_std k (by simp), rfl⟩
  have hGle : ∀ k l, Valued.v (G k l) ≤ 1 := fun k l => by
    rw [hG, ← locGram_apply_eq]; exact qbil_le_one_of_int hint (hmem k) (hmem l)
  rw [hγ, mem_locAct] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  have hd' := mem_std_iff.mp hd
  have hGd : ∀ l, Valued.v ((G *ᵥ d) l) < 1 := fun l => by
    have := h (γ.val *ᵥ Pi.single l 1) (hmem l)
    rw [qbil_comm, qbil_mulVec_locGram] at this
    simpa using this
  have hadj : ∀ k l, Valued.v (G.adjugate k l) ≤ 1 := by
    intro k l
    let G₀ : Matrix (Fin n) (Fin n) 𝔬 := Matrix.of fun k l =>
      ⟨G k l, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hGle k l)⟩
    have hmap : G = G₀.map (algebraMap 𝔬 Kv) := by ext k l; rfl
    have : G.adjugate = (G₀.adjugate).map (algebraMap 𝔬 Kv) := by
      rw [hmap]
      exact ((algebraMap 𝔬 Kv).map_adjugate G₀).symm
    rw [this]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (G₀.adjugate k l).2
  have hdk : ∀ k, Valued.v (d k) < 1 := by
    intro k
    have e : G.det * d k = ∑ l, G.adjugate k l * (G *ᵥ d) l := by
      have h1 : G.adjugate *ᵥ (G *ᵥ d) = G.det • d := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      have := congrFun h1 k
      simpa [Matrix.mulVec, dotProduct] using this.symm
    have hlt : Valued.v (G.det * d k) < 1 := by
      rw [e]
      refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
      rw [map_mul]
      exact (mul_le_mul' (hadj k l) le_rfl |>.trans_lt (by rw [one_mul]; exact hGd l))
    rwa [map_mul, hdet, one_mul] at hlt
  rw [hγ, mem_locAct]
  refine ⟨P⁻¹ • d, mem_std_iff.mpr fun i => ?_, by rw [Matrix.mulVec_smul]⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [inv_mul_eq_div]
  exact loc45_valued_div_le_one hP (hdk i)

theorem qbil_smul_right_loc {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (c : K) (x z : Fin n → K) :
    qbil Q K x (c • z) = c * qbil Q K x z := by
  rw [qbil_comm, qbil_smul_left, qbil_comm]

theorem evalIn_add_loc {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (y z : Fin n → K) :
    Q.evalIn K (y + z) = Q.evalIn K y + Q.evalIn K z + qbil Q K y z := by
  rw [qbil_eq_polar]; ring

theorem evalIn_smul_loc {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (r : K) (y : Fin n → K) :
    Q.evalIn K (r • y) = r ^ 2 * Q.evalIn K y := by
  apply mul_left_cancel₀ (two_ne_zero : (2 : K) ≠ 0)
  rw [← qbil_self, qbil_smul_left, qbil_smul_right_loc, qbil_self]; ring

/-- **Hensel for $A s^2 + u s + e$** over $\mathfrak o_v$ with $A \in \mathfrak m$, $u$ and $2$ units. -/
theorem exists_root_quad (A u e : 𝔬) (hA : A ∈ IsLocalRing.maximalIdeal 𝔬) (hu : IsUnit u)
    (h2 : IsUnit (2 : 𝔬)) : ∃ s : 𝔬, A * s ^ 2 + u * s + e = 0 := by
  classical
  set D : 𝔬 := u ^ 2 - 4 * A * e with hD
  let f : Polynomial 𝔬 := Polynomial.X ^ 2 - Polynomial.C D
  have hf : f.Monic := by unfold f; monicity!
  have hev : f.eval u ∈ IsLocalRing.maximalIdeal 𝔬 := by
    have : f.eval u = 4 * A * e := by
      simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, hD]; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hA)
  have hder : IsUnit (f.derivative.eval u) := by
    have : f.derivative.eval u = 2 * u := by
      simp only [f, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_zero]
      push_cast; ring
    rw [this]; exact h2.mul hu
  obtain ⟨w, hw, hwu⟩ := HenselianLocalRing.is_henselian f hf u hev hder
  have hw2 : w ^ 2 = D := by
    have : w ^ 2 - D = 0 := by simpa [f, Polynomial.IsRoot] using hw
    linear_combination this
  have huw : IsUnit (u + w) := by
    by_contra hnu
    have h1 : u + w ∈ IsLocalRing.maximalIdeal 𝔬 := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h3 : 2 * u ∈ IsLocalRing.maximalIdeal 𝔬 := by
      have := (IsLocalRing.maximalIdeal 𝔬).sub_mem h1 hwu
      rwa [show u + w - (w - u) = 2 * u by ring] at this
    exact ((IsLocalRing.mem_maximalIdeal _).mp h3) (h2.mul hu)
  obtain ⟨q, hq⟩ := huw.exists_right_inv
  refine ⟨-2 * e * q, ?_⟩
  linear_combination (e * q ^ 2) * hw2 + (-e * (1 + q * (w - u))) * hq

theorem valued_exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

/-- **The isotropic pair $b_0, b_1$ of Lemma 4.5** (Cassels' Hensel step): from $b \in \Gamma \setminus \Lambda$ with
$Pb \in \Lambda$ and $\Gamma \subseteq \Lambda + \mathfrak o b$, find isotropic $b_0 \in \Gamma$ (same properties) and
$b_1 \in \Lambda$ with $B(b_0, b_1) = 2/P$. -/
theorem exists_isotropic_pair_loc {P : Kv} (hP : Valued.v P = WithZero.exp (-1 : ℤ))
    (h2 : Valued.v (2 : Kv) = 1)
    {Λ Γ : Submodule 𝔬 (Fin n → Kv)} (hΛ : ∀ x ∈ Λ, Valued.v (Q.evalIn Kv x) ≤ 1)
    (hΓ : ∀ x ∈ Γ, Valued.v (Q.evalIn Kv x) ≤ 1)
    {γ : GL (Fin n) Kv} (hγ : Λ = locAct v γ (std v)) (hdet : Valued.v (locGram Q v γ).det = 1)
    (hPΛ : ∀ y ∈ Λ, P • y ∈ Γ) {b : Fin n → Kv} (hbΓ : b ∈ Γ) (hbΛ : b ∉ Λ) (hpb : P • b ∈ Λ)
    (hgen : ∀ y ∈ Γ, ∃ c : 𝔬, y - c • b ∈ Λ) :
    ∃ b0 b1 : Fin n → Kv, b0 ∈ Γ ∧ b1 ∈ Λ ∧ Q.evalIn Kv b0 = 0 ∧ Q.evalIn Kv b1 = 0 ∧
      qbil Q Kv b0 b1 = 2 / P ∧ P • b0 ∈ Λ ∧ (∀ y ∈ Γ, ∃ c : 𝔬, y - c • b0 ∈ Λ) := by
  classical
  have hP0 : P ≠ 0 := fun h => by
    rw [h, map_zero] at hP; exact WithZero.exp_ne_zero hP.symm
  have hPlt : Valued.v P < 1 := by rw [hP]; exact valued_exp_neg_one_lt_one
  have hPle : Valued.v P ≤ 1 := hPlt.le
  have h20 : (2 : Kv) ≠ 0 := two_ne_zero
  -- a primitive pairing partner
  obtain ⟨c, hcΛ, hc1⟩ : ∃ c ∈ Λ, Valued.v (qbil Q Kv (P • b) c) = 1 := by
    by_contra hcon
    push_neg at hcon
    apply hbΛ
    have := inv_smul_mem_of_pairing_lt Q hP hΛ hγ hdet hpb
      (fun c hc => lt_of_le_of_ne (qbil_le_one_of_int hΛ hpb hc) (hcon c hc))
    rwa [smul_smul, inv_mul_cancel₀ hP0, one_smul] at this
  set x : Fin n → Kv := P • b with hx
  have hQx : Q.evalIn Kv x = P ^ 2 * Q.evalIn Kv b := by rw [hx, evalIn_smul_loc]
  have hQxlt : Valued.v (Q.evalIn Kv x) < 1 := by
    rw [hQx, map_mul, map_pow]
    calc Valued.v P ^ 2 * Valued.v (Q.evalIn Kv b) ≤ Valued.v P ^ 2 * 1 :=
          mul_le_mul' le_rfl (hΓ b hbΓ)
      _ = Valued.v P ^ 2 := mul_one _
      _ < 1 := pow_lt_one₀ zero_le hPlt two_ne_zero
  -- Hensel
  have hunit : ∀ y : Kv, ∀ hy : Valued.v y = 1, IsUnit (toO v y hy.le) := fun y hy =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hy
  have h2O : IsUnit (2 : 𝔬) :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr (by
      show Valued.v ((2 : 𝔬) : Kv) = 1
      exact h2)
  have hAmax : toO v (Q.evalIn Kv x) (hQxlt.le) ∈ IsLocalRing.maximalIdeal 𝔬 := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hu
    exact absurd this (ne_of_lt hQxlt)
  obtain ⟨s, hs⟩ := exists_root_quad (toO v (Q.evalIn Kv x) hQxlt.le) (toO v _ hc1.le)
    (toO v (Q.evalIn Kv c) (hΛ c hcΛ)) hAmax (hunit _ hc1) h2O
  have hs' : Q.evalIn Kv x * (s : Kv) ^ 2 + qbil Q Kv x c * (s : Kv) + Q.evalIn Kv c = 0 := by
    have := congrArg (fun z : 𝔬 => (z : Kv)) hs
    simpa [toO] using this
  have hsle : Valued.v (s : Kv) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp s.2
  have hxΛ : x ∈ Λ := hpb
  set c1 : Fin n → Kv := c + (s : Kv) • x with hc1def
  have hc1Λ : c1 ∈ Λ := Λ.add_mem hcΛ (smul_mem_of_valued_le_one hxΛ hsle)
  have hQc1 : Q.evalIn Kv c1 = 0 := by
    rw [hc1def, evalIn_add_loc, evalIn_smul_loc, qbil_smul_right_loc, qbil_comm Q Kv c x]
    linear_combination hs'
  have hBxc1 : qbil Q Kv x c1 = qbil Q Kv x c + 2 * (s : Kv) * Q.evalIn Kv x := by
    rw [hc1def, qbil_add_right, qbil_smul_right_loc, qbil_self]; ring
  have hu1 : Valued.v (qbil Q Kv x c1) = 1 := by
    rw [hBxc1]
    have : Valued.v (2 * (s : Kv) * Q.evalIn Kv x) < Valued.v (qbil Q Kv x c) := by
      rw [hc1, map_mul, map_mul, h2, one_mul]
      calc Valued.v (s : Kv) * Valued.v (Q.evalIn Kv x) ≤ 1 * Valued.v (Q.evalIn Kv x) :=
            mul_le_mul' hsle le_rfl
        _ < 1 := by rw [one_mul]; exact hQxlt
    rw [Valuation.map_add_eq_of_lt_left _ this, hc1]
  have hu10 : qbil Q Kv x c1 ≠ 0 := fun h => by rw [h, map_zero] at hu1; exact zero_ne_one hu1
  set r : Kv := 2 / qbil Q Kv x c1 with hr
  have hrv : Valued.v r = 1 := by rw [hr, map_div₀, h2, hu1, div_one]
  set b1 : Fin n → Kv := r • c1 with hb1def
  have hb1Λ : b1 ∈ Λ := smul_mem_of_valued_le_one hc1Λ hrv.le
  have hQb1 : Q.evalIn Kv b1 = 0 := by rw [hb1def, evalIn_smul_loc, hQc1, mul_zero]
  have hxb1 : qbil Q Kv x b1 = 2 := by
    rw [hb1def, qbil_smul_right_loc, hr]; field_simp
  have hbb1 : qbil Q Kv b b1 = 2 / P := by
    have : qbil Q Kv x b1 = P * qbil Q Kv b b1 := by rw [hx, qbil_smul_left]
    rw [hxb1] at this
    field_simp; linear_combination -this
  -- the isotropic b0
  set t : Kv := P * (-(Q.evalIn Kv b / 2)) with ht
  have htv : Valued.v (-(Q.evalIn Kv b / 2)) ≤ 1 := by
    rw [Valuation.map_neg, map_div₀, h2, div_one]; exact hΓ b hbΓ
  have htb1 : t • b1 ∈ Λ := by
    rw [ht, mul_smul]
    exact smul_mem_of_valued_le_one (smul_mem_of_valued_le_one hb1Λ htv) hPle
  have htb1Γ : t • b1 ∈ Γ := by
    rw [ht, mul_smul]
    exact hPΛ _ (smul_mem_of_valued_le_one hb1Λ htv)
  have hb11 : qbil Q Kv b1 b1 = 0 := by rw [qbil_self, hQb1, mul_zero]
  refine ⟨b + t • b1, b1, Γ.add_mem hbΓ htb1Γ, hb1Λ, ?_, hQb1, ?_, ?_, ?_⟩
  · rw [evalIn_add_loc, evalIn_smul_loc, hQb1, qbil_smul_right_loc, hbb1, ht]
    field_simp
    ring
  · rw [qbil_add_left, qbil_smul_left, hb11, hbb1]; ring
  · rw [smul_add]
    exact Λ.add_mem hpb (smul_mem_of_valued_le_one htb1 hPle)
  · intro y hy
    obtain ⟨c', hc'⟩ := hgen y hy
    refine ⟨c', ?_⟩
    have : y - c' • (b + t • b1) = (y - c' • b) - (c' • t) • b1 := by
      rw [smul_add, smul_assoc]; abel
    rw [this]
    refine Λ.sub_mem hc' ?_
    rw [smul_assoc]; exact Λ.smul_mem c' htb1

/-- **The splitting of $\Lambda$ and $\Gamma$ along the hyperbolic plane** (the orthogonal-complement step of
Cassels' proof of Lemma 4.5): with $x_0 = Pb_0$, $\Lambda = \mathfrak o x_0 + \mathfrak o b_1 + T$ and
$\Gamma = \mathfrak o b_0 + \mathfrak o Pb_1 + T$ where $T = \Lambda \cap \langle b_0, b_1\rangle^\perp$. -/
theorem exists_split_loc {P : Kv} (hP : Valued.v P = WithZero.exp (-1 : ℤ))
    (h2 : Valued.v (2 : Kv) = 1)
    {Λ Γ : Submodule 𝔬 (Fin n → Kv)} (hΛ : ∀ x ∈ Λ, Valued.v (Q.evalIn Kv x) ≤ 1)
    (hΓ : ∀ x ∈ Γ, Valued.v (Q.evalIn Kv x) ≤ 1)
    {b0 b1 b' : Fin n → Kv} (hb0Γ : b0 ∈ Γ) (hb1Λ : b1 ∈ Λ) (hQ0 : Q.evalIn Kv b0 = 0)
    (hQ1 : Q.evalIn Kv b1 = 0) (hB01 : qbil Q Kv b0 b1 = 2 / P) (hPb0 : P • b0 ∈ Λ)
    (hgenΓ : ∀ y ∈ Γ, ∃ c : 𝔬, y - c • b0 ∈ Λ)
    (hb'Λ : b' ∈ Λ) (hPb' : P • b' ∈ Γ) (hgenΛ : ∀ y ∈ Λ, ∃ c : 𝔬, y - c • b' ∈ Γ) :
    ∃ T : Submodule 𝔬 (Fin n → Kv), (∀ t ∈ T, t ∈ Λ ∧ qbil Q Kv t b0 = 0 ∧ qbil Q Kv t b1 = 0) ∧
      Λ = Submodule.span 𝔬 {P • b0, b1} ⊔ T ∧ Γ = Submodule.span 𝔬 {b0, P • b1} ⊔ T := by
  classical
  have hP0 : P ≠ 0 := fun h => by
    rw [h, map_zero] at hP; exact WithZero.exp_ne_zero hP.symm
  have hPlt : Valued.v P < 1 := by rw [hP]; exact valued_exp_neg_one_lt_one
  have hPle : Valued.v P ≤ 1 := hPlt.le
  have h20 : (2 : Kv) ≠ 0 := two_ne_zero
  have hB00 : qbil Q Kv b0 b0 = 0 := by rw [qbil_self, hQ0, mul_zero]
  have hB11 : qbil Q Kv b1 b1 = 0 := by rw [qbil_self, hQ1, mul_zero]
  have hB10 : qbil Q Kv b1 b0 = 2 / P := by rw [qbil_comm]; exact hB01
  have hx0b1 : qbil Q Kv (P • b0) b1 = 2 := by
    rw [qbil_smul_left, hB01]; field_simp
  have hPΛΓ : ∀ y ∈ Λ, P • y ∈ Γ := by
    intro y hy
    obtain ⟨c, hc⟩ := hgenΛ y hy
    have : P • y = P • (y - c • b') + c • (P • b') := by
      rw [smul_sub, smul_comm c P b']; abel
    rw [this]
    exact Γ.add_mem (smul_mem_of_valued_le_one hc hPle) (Γ.smul_mem c hPb')
  have hPb1Γ : P • b1 ∈ Γ := hPΛΓ b1 hb1Λ
  -- the criterion for membership in Γ
  have hcrit : ∀ y ∈ Λ, Valued.v (qbil Q Kv y (P • b0)) < 1 → y ∈ Γ := by
    intro y hy hlt
    have hg : ∀ g ∈ Γ, Valued.v (qbil Q Kv g (P • b0)) < 1 := fun g hg => by
      rw [qbil_smul_right_loc, map_mul]
      calc Valued.v P * Valued.v (qbil Q Kv g b0) ≤ Valued.v P * 1 :=
            mul_le_mul' le_rfl (qbil_le_one_of_int hΓ hg hb0Γ)
        _ < 1 := by rw [mul_one]; exact hPlt
    have hb'x0 : Valued.v (qbil Q Kv b' (P • b0)) = 1 := by
      by_contra hne
      have hlt' : Valued.v (qbil Q Kv b' (P • b0)) < 1 :=
        lt_of_le_of_ne (qbil_le_one_of_int hΛ hb'Λ hPb0) hne
      obtain ⟨c1, hc1⟩ := hgenΛ b1 hb1Λ
      have e : qbil Q Kv b1 (P • b0) =
          qbil Q Kv (b1 - c1 • b') (P • b0) + (c1 : Kv) * qbil Q Kv b' (P • b0) := by
        rw [show c1 • b' = (c1 : Kv) • b' from rfl, qbil_sub_left, qbil_smul_left]; ring
      have c1le : Valued.v (c1 : Kv) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c1.2
      have : Valued.v (qbil Q Kv b1 (P • b0)) < 1 := by
        rw [e]
        refine Valuation.map_add_lt _ (hg _ hc1) ?_
        rw [map_mul]
        exact (mul_le_mul' c1le le_rfl).trans_lt (by rw [one_mul]; exact hlt')
      rw [qbil_comm, hx0b1, h2] at this
      exact lt_irrefl _ this
    obtain ⟨c, hc⟩ := hgenΛ y hy
    have e : qbil Q Kv y (P • b0) = qbil Q Kv (y - c • b') (P • b0) + (c : Kv) * qbil Q Kv b' (P • b0) := by
      rw [show c • b' = (c : Kv) • b' from rfl, qbil_sub_left, qbil_smul_left]; ring
    have hcv : Valued.v (c : Kv) < 1 := by
      have h1 : Valued.v ((c : Kv) * qbil Q Kv b' (P • b0)) < 1 := by
        have : (c : Kv) * qbil Q Kv b' (P • b0) =
            qbil Q Kv y (P • b0) - qbil Q Kv (y - c • b') (P • b0) := by rw [e]; ring
        rw [this]
        exact Valuation.map_sub_lt _ hlt (hg _ hc)
      rwa [map_mul, hb'x0, mul_one] at h1
    have hcb : (c : Kv) • b' ∈ Γ := by
      have : (c : Kv) • b' = ((c : Kv) / P) • (P • b') := by
        rw [smul_smul, div_mul_cancel₀ _ hP0]
      rw [this]
      exact smul_mem_of_valued_le_one hPb' (loc45_valued_div_le_one hP hcv)
    have : y = (y - (c : Kv) • b') + (c : Kv) • b' := by abel
    rw [this]
    exact Γ.add_mem (by exact hc) hcb
  -- the complement T
  let T : Submodule 𝔬 (Fin n → Kv) :=
    { carrier := {t | t ∈ Λ ∧ qbil Q Kv t b0 = 0 ∧ qbil Q Kv t b1 = 0}
      add_mem' := by
        rintro a b ⟨ha, ha0, ha1⟩ ⟨hb, hb0, hb1⟩
        exact ⟨Λ.add_mem ha hb, by rw [qbil_add_left, ha0, hb0, add_zero],
          by rw [qbil_add_left, ha1, hb1, add_zero]⟩
      zero_mem' := ⟨Λ.zero_mem, by simp [qbil], by simp [qbil]⟩
      smul_mem' := by
        rintro c t ⟨ht, ht0, ht1⟩
        refine ⟨Λ.smul_mem c ht, ?_, ?_⟩
        · show qbil Q Kv ((c : Kv) • t) b0 = 0
          rw [qbil_smul_left, ht0, mul_zero]
        · show qbil Q Kv ((c : Kv) • t) b1 = 0
          rw [qbil_smul_left, ht1, mul_zero] }
  have hTΛ : T ≤ Λ := fun t ht => ht.1
  have hTΓ : T ≤ Γ := fun t ht => hcrit t ht.1 (by
    rw [qbil_smul_right_loc, ht.2.1, mul_zero, map_zero]; exact zero_lt_one)
  -- decomposition of Λ
  have hα : ∀ y ∈ Λ, Valued.v (qbil Q Kv y b1 / 2) ≤ 1 := fun y hy => by
    rw [map_div₀, h2, div_one]; exact qbil_le_one_of_int hΛ hy hb1Λ
  have hβ : ∀ y ∈ Λ, Valued.v (qbil Q Kv y (P • b0) / 2) ≤ 1 := fun y hy => by
    rw [map_div₀, h2, div_one]; exact qbil_le_one_of_int hΛ hy hPb0
  have hD1 : ∀ y ∈ Λ, y - (qbil Q Kv y b1 / 2) • (P • b0) - (qbil Q Kv y (P • b0) / 2) • b1 ∈ T := by
    intro y hy
    have hyb0 : qbil Q Kv y (P • b0) = P * qbil Q Kv y b0 := qbil_smul_right_loc Q _ _ _
    refine ⟨Λ.sub_mem (Λ.sub_mem hy (smul_mem_of_valued_le_one hPb0 (hα y hy)))
      (smul_mem_of_valued_le_one hb1Λ (hβ y hy)), ?_, ?_⟩
    · simp only [qbil_sub_left, qbil_smul_left, hB00, hB10, hyb0]
      field_simp; ring
    · simp only [qbil_sub_left, qbil_smul_left, hB11, hB01, hyb0]
      field_simp; ring
  have hΛeq : Λ = Submodule.span 𝔬 {P • b0, b1} ⊔ T := by
    apply le_antisymm
    · intro y hy
      have : y = ((qbil Q Kv y b1 / 2) • (P • b0) + (qbil Q Kv y (P • b0) / 2) • b1) +
          (y - (qbil Q Kv y b1 / 2) • (P • b0) - (qbil Q Kv y (P • b0) / 2) • b1) := by abel
      rw [this]
      refine Submodule.add_mem_sup (Submodule.add_mem _ ?_ ?_) (hD1 y hy)
      · exact smul_mem_of_valued_le_one (Submodule.subset_span (by simp)) (hα y hy)
      · exact smul_mem_of_valued_le_one (Submodule.subset_span (by simp)) (hβ y hy)
    · refine sup_le (Submodule.span_le.mpr ?_) hTΛ
      intro z hz
      rcases hz with rfl | rfl
      · exact hPb0
      · simpa using hb1Λ
  have hΓeq : Γ = Submodule.span 𝔬 {b0, P • b1} ⊔ T := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, hc⟩ := hgenΓ y hy
      have hc' : y - (c : Kv) • b0 ∈ Λ := hc
      have hB : qbil Q Kv (y - (c : Kv) • b0) b0 = qbil Q Kv y b0 := by
        rw [qbil_sub_left, qbil_smul_left, hB00]; ring
      have hβ1 : qbil Q Kv (y - (c : Kv) • b0) (P • b0) / 2 = qbil Q Kv y b0 / 2 * P := by
        rw [qbil_smul_right_loc, hB]; ring
      have ht := hD1 _ hc'
      rw [hβ1] at ht
      have hcle : Valued.v (c : Kv) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2
      have hγ0 : Valued.v (qbil Q Kv y b0 / 2) ≤ 1 := by
        rw [map_div₀, h2, div_one]; exact qbil_le_one_of_int hΓ hy hb0Γ
      have hcoef : Valued.v ((c : Kv) + qbil Q Kv (y - (c : Kv) • b0) b1 / 2 * P) ≤ 1 :=
        Valuation.map_add_le _ hcle (by
          rw [map_mul]; exact (mul_le_mul' (hα _ hc') hPle).trans (by rw [one_mul]))
      have : y = (((c : Kv) + qbil Q Kv (y - (c : Kv) • b0) b1 / 2 * P) • b0 +
          (qbil Q Kv y b0 / 2) • (P • b1)) +
          ((y - (c : Kv) • b0) - (qbil Q Kv (y - (c : Kv) • b0) b1 / 2) • (P • b0) -
            (qbil Q Kv y b0 / 2 * P) • b1) := by module
      rw [this]
      exact Submodule.add_mem_sup (Submodule.add_mem _
        (smul_mem_of_valued_le_one (Submodule.subset_span (by simp)) hcoef)
        (smul_mem_of_valued_le_one (Submodule.subset_span (by simp)) hγ0)) ht
    · refine sup_le (Submodule.span_le.mpr ?_) hTΓ
      intro z hz
      rcases hz with rfl | rfl
      · exact hb0Γ
      · simpa using hPb1Γ
  exact ⟨T, fun t ht => ht, hΛeq, hΓeq⟩

/-- A submodule of a finitely generated $\mathfrak o_v$-lattice has a finite basis (inside $K_v^n$). -/
theorem exists_free_basis_loc {Λ T : Submodule 𝔬 (Fin n → Kv)} (hΛfg : Λ.FG) (hTΛ : T ≤ Λ) :
    ∃ (κ : Type) (_ : Fintype κ) (τ : κ → Fin n → Kv), LinearIndependent 𝔬 τ ∧
      Submodule.span 𝔬 (Set.range τ) = T := by
  classical
  haveI : Module.Finite 𝔬 Λ := Module.Finite.iff_fg.mpr hΛfg
  haveI : IsNoetherian 𝔬 Λ := isNoetherian_of_isNoetherianRing_of_finite 𝔬 Λ
  have hTfg : T.FG := by
    have h1 := IsNoetherian.noetherian (T.comap Λ.subtype)
    have h2 := h1.map Λ.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hTΛ] at h2
  haveI : Module.Finite 𝔬 T := Module.Finite.iff_fg.mpr hTfg
  haveI : Module.Free 𝔬 T := inferInstance
  let tb := Module.Free.chooseBasis 𝔬 T
  refine ⟨Module.Free.ChooseBasisIndex 𝔬 T, inferInstance, fun j => (tb j : Fin n → Kv), ?_, ?_⟩
  · exact tb.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  · have h := tb.span_eq
    have h2 := congrArg (Submodule.map T.subtype) h
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h2
    refine Eq.trans ?_ h2
    congr 1
    ext x; simp

/-- $w \mapsto B(w, z)$ as a $K_v$-linear map. -/
def qbilL (z : Fin n → Kv) : (Fin n → Kv) →ₗ[Kv] Kv where
  toFun w := qbil Q Kv w z
  map_add' a b := qbil_add_left Q Kv a b z
  map_smul' c a := by simp [qbil_smul_left]

theorem range_vec2 (x y : Fin n → Kv) : Set.range ![x, y] = {x, y} := by
  ext z; simp [Fin.exists_fin_two, eq_comm]; tauto

/-- **Assembling the basis $b$ of Lemma 4.5** from the splitting $\Lambda = \mathfrak o x_0 + \mathfrak o b_1 + T$,
$\Gamma = \mathfrak o b_0 + \mathfrak o Pb_1 + T$. -/
theorem exists_basis_of_split_loc {P : Kv} (hP : Valued.v P = WithZero.exp (-1 : ℤ)) (hn : 2 ≤ n)
    {Λ Γ : Submodule 𝔬 (Fin n → Kv)} (hΛfg : Λ.FG) (hΛtop : Submodule.span Kv (Λ : Set (Fin n → Kv)) = ⊤)
    {b0 b1 : Fin n → Kv} (hQ0 : Q.evalIn Kv b0 = 0) (hQ1 : Q.evalIn Kv b1 = 0)
    (hB01 : qbil Q Kv b0 b1 = 2 / P)
    {T : Submodule 𝔬 (Fin n → Kv)} (hT : ∀ t ∈ T, t ∈ Λ ∧ qbil Q Kv t b0 = 0 ∧ qbil Q Kv t b1 = 0)
    (hΛeq : Λ = Submodule.span 𝔬 {P • b0, b1} ⊔ T) (hΓeq : Γ = Submodule.span 𝔬 {b0, P • b1} ⊔ T) :
    ∃ b : Fin n → Fin n → Kv,
      Q.evalIn Kv (b ⟨0, by omega⟩) = 0 ∧ Q.evalIn Kv (b ⟨1, by omega⟩) = 0 ∧
      qbil Q Kv (b ⟨0, by omega⟩) (b ⟨1, by omega⟩) = 2 / P ∧
      (∀ i j : Fin n, i.1 ≤ 1 → 2 ≤ j.1 → qbil Q Kv (b i) (b j) = 0) ∧
      LinearIndependent Kv b ∧
      Λ = Submodule.span 𝔬 (Set.range fun j : Fin n => if j.1 = 0 then P • b j else b j) ∧
      Γ = Submodule.span 𝔬 (Set.range fun j : Fin n => if j.1 = 1 then P • b j else b j) := by
  classical
  have hP0 : P ≠ 0 := fun h => by
    rw [h, map_zero] at hP; exact WithZero.exp_ne_zero hP.symm
  have hTΛ : T ≤ Λ := fun t ht => (hT t ht).1
  obtain ⟨κ, _, τ, hτ𝔬, hτspan⟩ := exists_free_basis_loc hΛfg hTΛ
  have hτK : LinearIndependent Kv τ := hτ𝔬.localization Kv (nonZeroDivisors 𝔬)
  have hτT : ∀ j, τ j ∈ T := fun j => hτspan ▸ Submodule.subset_span ⟨j, rfl⟩
  have hτ0 : ∀ j, qbil Q Kv (τ j) b0 = 0 := fun j => (hT _ (hτT j)).2.1
  have hτ1 : ∀ j, qbil Q Kv (τ j) b1 = 0 := fun j => (hT _ (hτT j)).2.2
  have hB00 : qbil Q Kv b0 b0 = 0 := by rw [qbil_self, hQ0, mul_zero]
  have hB11 : qbil Q Kv b1 b1 = 0 := by rw [qbil_self, hQ1, mul_zero]
  have hB10 : qbil Q Kv b1 b0 = 2 / P := by rw [qbil_comm]; exact hB01
  have hz : ∀ z : Fin n → Kv, qbil Q Kv 0 z = 0 := fun z => by simp [qbil]
  let Gb : Fin 2 ⊕ κ → Fin n → Kv := Sum.elim ![b0, b1] τ
  let Gx : Fin 2 ⊕ κ → Fin n → Kv := Sum.elim ![P • b0, b1] τ
  let Gy : Fin 2 ⊕ κ → Fin n → Kv := Sum.elim ![b0, P • b1] τ
  have h2P : (2 / P : Kv) ≠ 0 := div_ne_zero two_ne_zero hP0
  -- linear independence over K
  have hGb : LinearIndependent Kv Gb := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Gb, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hg
    set w : Fin n → Kv := ∑ j, g (Sum.inr j) • τ j with hw
    have hw0 : qbil Q Kv w b0 = 0 := by
      have := map_sum (qbilL Q b0) (fun j => g (Sum.inr j) • τ j) Finset.univ
      simp only [qbilL, LinearMap.coe_mk, AddHom.coe_mk, qbil_smul_left, hτ0, mul_zero,
        Finset.sum_const_zero] at this
      exact this
    have hw1 : qbil Q Kv w b1 = 0 := by
      have := map_sum (qbilL Q b1) (fun j => g (Sum.inr j) • τ j) Finset.univ
      simp only [qbilL, LinearMap.coe_mk, AddHom.coe_mk, qbil_smul_left, hτ1, mul_zero,
        Finset.sum_const_zero] at this
      exact this
    have e1 := congrArg (fun z => qbil Q Kv z b1) hg
    have e0 := congrArg (fun z => qbil Q Kv z b0) hg
    simp only [qbil_add_left, qbil_smul_left, hB01, hB11, hB10, hB00, hw0, hw1, hz] at e1 e0
    have ha : g (Sum.inl 0) = 0 := by
      have : g (Sum.inl 0) * (2 / P) = 0 := by linear_combination e1
      exact (mul_eq_zero.mp this).resolve_right h2P
    have hc : g (Sum.inl 1) = 0 := by
      have : g (Sum.inl 1) * (2 / P) = 0 := by linear_combination e0
      exact (mul_eq_zero.mp this).resolve_right h2P
    rw [ha, hc, zero_smul, zero_smul, zero_add, zero_add] at hg
    have hrest := Fintype.linearIndependent_iff.mp hτK (fun j => g (Sum.inr j)) hg
    rintro (a | j)
    · fin_cases a
      · exact ha
      · exact hc
    · exact hrest j
  -- spanning over K
  have hspan : Submodule.span Kv (Set.range Gb) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hΛtop]
    refine Submodule.span_le.mpr fun y hy => ?_
    have hTK : T ≤ (Submodule.span Kv (Set.range τ)).restrictScalars 𝔬 :=
      hτspan ▸ Submodule.span_le_restrictScalars 𝔬 Kv _
    have hpair : Submodule.span 𝔬 {P • b0, b1} ≤ (Submodule.span Kv {P • b0, b1}).restrictScalars 𝔬 :=
      Submodule.span_le_restrictScalars 𝔬 Kv _
    have h1 : Submodule.span Kv {P • b0, b1} ≤ Submodule.span Kv (Set.range Gb) := by
      refine Submodule.span_le.mpr ?_
      intro z hz
      rcases hz with rfl | rfl
      · exact Submodule.smul_mem _ P (Submodule.subset_span ⟨Sum.inl 0, rfl⟩)
      · exact Submodule.subset_span ⟨Sum.inl 1, rfl⟩
    have h2 : Submodule.span Kv (Set.range τ) ≤ Submodule.span Kv (Set.range Gb) := by
      refine Submodule.span_mono ?_
      rintro _ ⟨j, rfl⟩
      exact ⟨Sum.inr j, rfl⟩
    have hy' : y ∈ Submodule.span 𝔬 {P • b0, b1} ⊔ T := hΛeq ▸ hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hy'
    exact Submodule.add_mem _ (h1 (hpair hy1)) (h2 (hTK hy2))
  -- the cardinality
  have hcard : Fintype.card (Fin 2 ⊕ κ) = n := by
    have h := linearIndependent_iff_card_eq_finrank_span.mp hGb
    rw [h]
    unfold Set.finrank
    rw [hspan, finrank_top, Module.finrank_fin_fun]
  have hr : 2 + Fintype.card κ = n := by simpa [Fintype.card_sum] using hcard
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let σ : Fin 2 ⊕ κ ≃ Fin n :=
    (Equiv.sumCongr (Equiv.refl _) e).trans (finSumFinEquiv.trans (finCongr hr))
  have hσl : ∀ a : Fin 2, (σ (Sum.inl a)).1 = a.1 := by
    intro a; simp [σ, finSumFinEquiv_apply_left]
  have hσr : ∀ j, 2 ≤ (σ (Sum.inr j)).1 := by
    intro j; simp [σ, finSumFinEquiv_apply_right]
  have hσ0 : σ.symm ⟨0, by omega⟩ = Sum.inl 0 := by
    rw [Equiv.symm_apply_eq]; exact Fin.ext (by rw [hσl]; rfl)
  have hσ1 : σ.symm ⟨1, by omega⟩ = Sum.inl 1 := by
    rw [Equiv.symm_apply_eq]; exact Fin.ext (by rw [hσl]; rfl)
  have hinl : ∀ i : Fin n, i.1 ≤ 1 → ∃ a : Fin 2, σ.symm i = Sum.inl a := by
    intro i hi
    rcases hs : σ.symm i with a | k
    · exact ⟨a, rfl⟩
    · have := hσr k
      rw [← hs, Equiv.apply_symm_apply] at this
      omega
  have hinr : ∀ j : Fin n, 2 ≤ j.1 → ∃ k : κ, σ.symm j = Sum.inr k := by
    intro j hj
    rcases hs : σ.symm j with a | k
    · have := hσl a
      rw [← hs, Equiv.apply_symm_apply] at this
      have := a.2
      omega
    · exact ⟨k, rfl⟩
  have hrange : ∀ G : Fin 2 ⊕ κ → Fin n → Kv, Set.range (G ∘ σ.symm) = Set.range G := fun G =>
    Function.Surjective.range_comp σ.symm.surjective G
  refine ⟨fun i => Gb (σ.symm i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hσ0, Gb, Sum.elim_inl]; exact hQ0
  · simp only [hσ1, Gb, Sum.elim_inl]; exact hQ1
  · simp only [hσ0, hσ1, Gb, Sum.elim_inl]; exact hB01
  · intro i j hi hj
    obtain ⟨a, ha⟩ := hinl i hi
    obtain ⟨k, hk⟩ := hinr j hj
    simp only [ha, hk, Gb, Sum.elim_inl, Sum.elim_inr]
    fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]; rw [qbil_comm]; exact hτ0 k
    · simp only [Fin.mk_one, Matrix.cons_val_one]; rw [qbil_comm]; exact hτ1 k
  · exact hGb.comp σ.symm σ.symm.injective
  · have hF : (fun j : Fin n => if j.1 = 0 then P • Gb (σ.symm j) else Gb (σ.symm j)) = Gx ∘ σ.symm := by
      funext j
      rcases hs : σ.symm j with a | k
      · have hj : j.1 = a.1 := by
          have := hσl a
          rw [← hs, Equiv.apply_symm_apply] at this
          exact this
        fin_cases a
        · have : j.1 = 0 := hj
          simp [this, Gb, Gx, hs]
        · have : j.1 = 1 := hj
          simp [this, Gb, Gx, hs]
      · have := hσr k
        rw [← hs, Equiv.apply_symm_apply] at this
        have h0 : ¬ j.1 = 0 := by omega
        simp [h0, Gb, Gx, hs]
    rw [hF, hrange, show Gx = Sum.elim ![P • b0, b1] τ from rfl, Set.Sum.elim_range, range_vec2,
      Submodule.span_union, hτspan]
    exact hΛeq
  · have hF : (fun j : Fin n => if j.1 = 1 then P • Gb (σ.symm j) else Gb (σ.symm j)) = Gy ∘ σ.symm := by
      funext j
      rcases hs : σ.symm j with a | k
      · have hj : j.1 = a.1 := by
          have := hσl a
          rw [← hs, Equiv.apply_symm_apply] at this
          exact this
        fin_cases a
        · have : j.1 = 0 := hj
          simp [this, Gb, Gy, hs]
        · have : j.1 = 1 := hj
          simp [this, Gb, Gy, hs]
      · have := hσr k
        rw [← hs, Equiv.apply_symm_apply] at this
        have h0 : ¬ j.1 = 1 := by omega
        simp [h0, Gb, Gy, hs]
    rw [hF, hrange, show Gy = Sum.elim ![b0, P • b1] τ from rfl, Set.Sum.elim_range, range_vec2,
      Submodule.span_union, hτspan]
    exact hΓeq

end Local

/-- **Cassels, Lemma 4.5** (Ch. 11, p. 219): *let $p \ne 2$, let $\Lambda_p, \Gamma_p$ be lattices of the same
determinant in $V_p$ with $I(\Lambda_p, \Gamma_p) = p$. Suppose that $\phi$ induces an integral ($p$-adic) quadratic
form on $\Lambda_p, \Gamma_p$ and that the determinant of these quadratic forms is a $p$-adic unit. Then there are
$b_1, \dots, b_n \in V_p$ such that (i) $\phi(b_1) = \phi(b_2) = 0$, $\phi(b_1, b_2) = 1/p$; (ii)
$\phi(b_1, b_j) = \phi(b_2, b_j) = 0$ ($j > 2$); (iii) $pb_1, b_2, \dots, b_n$ and $b_1, pb_2, b_3, \dots, b_n$ are bases
of $\Lambda_p, \Gamma_p$ respectively.* Here for the localizations of $\mathbb Z$-lattices $\Lambda, \Gamma$ of the
same determinant, 0-based ($b_0, b_1$ for Cassels' $b_1, b_2$), with $\phi(x, y) = \tfrac12B(x, y)$; the unit
determinant is that of the Gram matrix of a basis of $\Lambda_p$ (then also of $\Gamma_p$). -/
@[kb "cassels1978" "Ch. 11, Lemma 4.5, p. 219 (0-based)"]
theorem exists_hyperbolic_basis_of_casselsI (hn : 2 ≤ n) {L M : Lat ℚ n} (h : latIndex L = latIndex M)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal)
    (hp : Rat.HeightOneSpectrum.natGenerator v ∣ casselsI L M)
    (hp2 : ¬ Rat.HeightOneSpectrum.natGenerator v ^ 2 ∣ casselsI L M)
    (hL : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1)
    (hM : ∀ x ∈ loc v M.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1)
    (hdet : ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧
      Valued.v (locGram Q v γ).det = 1) :
    ∃ b : Fin n → Fin n → v.adicCompletion ℚ,
      Q.evalIn (v.adicCompletion ℚ) (b ⟨0, by omega⟩) = 0 ∧ Q.evalIn (v.adicCompletion ℚ) (b ⟨1, by omega⟩) = 0 ∧
      qbil Q (v.adicCompletion ℚ) (b ⟨0, by omega⟩) (b ⟨1, by omega⟩) =
        2 / (Rat.HeightOneSpectrum.natGenerator v : v.adicCompletion ℚ) ∧
      (∀ i j : Fin n, i.1 ≤ 1 → 2 ≤ j.1 → qbil Q (v.adicCompletion ℚ) (b i) (b j) = 0) ∧
      LinearIndependent (v.adicCompletion ℚ) b ∧
      loc v L.1 = Submodule.span (v.adicCompletionIntegers ℚ) (Set.range fun j : Fin n =>
        if j.1 = 0 then (Rat.HeightOneSpectrum.natGenerator v : v.adicCompletion ℚ) • b j else b j) ∧
      loc v M.1 = Submodule.span (v.adicCompletionIntegers ℚ) (Set.range fun j : Fin n =>
        if j.1 = 1 then (Rat.HeightOneSpectrum.natGenerator v : v.adicCompletion ℚ) • b j else b j) := by
  classical
  obtain ⟨γ, hγ, hdet'⟩ := hdet
  have hP := valued_natGenerator v
  have h2v : Valued.v (2 : v.adicCompletion ℚ) = 1 := valued_two h2
  set P : v.adicCompletion ℚ := (Rat.HeightOneSpectrum.natGenerator v : v.adicCompletion ℚ) with hPdef
  have hPle : Valued.v P ≤ 1 := by rw [hP]; exact valued_exp_neg_one_lt_one.le
  have hcomm : casselsI M L = casselsI L M := (casselsI_comm h).symm
  obtain ⟨b, hbΓ, hbΛ, hpb, hgen⟩ := exists_local_gen v M L (hcomm ▸ hp) (hcomm ▸ hp2)
  obtain ⟨b', hb'Λ, -, hPb', hgen'⟩ := exists_local_gen v L M hp hp2
  have hPΛ : ∀ y ∈ loc v L.1, P • y ∈ loc v M.1 := by
    intro y hy
    obtain ⟨c, hc⟩ := hgen' y hy
    have : P • y = P • (y - c • b') + c • (P • b') := by
      rw [smul_sub, smul_comm c P b']; abel
    rw [this]
    exact (loc v M.1).add_mem (smul_mem_of_valued_le_one hc hPle) ((loc v M.1).smul_mem c hPb')
  obtain ⟨b0, b1, hb0Γ, hb1Λ, hQ0, hQ1, hB01, hPb0, hgenΓ⟩ :=
    exists_isotropic_pair_loc Q hP h2v hL hM hγ hdet' hPΛ hbΓ hbΛ hpb hgen
  obtain ⟨T, hT, hΛeq, hΓeq⟩ := exists_split_loc Q hP h2v hL hM hb0Γ hb1Λ hQ0 hQ1 hB01 hPb0 hgenΓ
    hb'Λ hPb' hgen'
  have hlat := loc_isLattice (v := v) L.2
  obtain ⟨b, h1, h2', h3, h4, h5, h6, h7⟩ := exists_basis_of_split_loc Q hP hn hlat.fg hlat.span_eq_top hQ0
    hQ1 hB01 hT hΛeq hΓeq
  exact ⟨b, h1, h2', h3, h4, h5, h6, h7⟩

/-- **The rotation $\beta_p$ of the proof of Theorem 4.1** (Ch. 11, p. 220): under the hypotheses of Lemma 4.5 there
is $\beta_p \in O^+(V_p)$ with $\beta_p\Lambda_p = \Gamma_p$ and $\theta(\beta_p) = p\,(\mathbb Q_p^\times)^2$
(Cassels: "by the argument at the beginning of the proof of Theorem 3.2 of Chapter 10"). -/
@[kb "cassels1978" "Ch. 11, proof of Thm. 4.1, p. 220 (β_q with θ(β_q) = q)"]
theorem exists_soSub_locAct_eq_of_casselsI (hQ : Q.Nondegenerate) (hn : 2 ≤ n) {L M : Lat ℚ n}
    (h : latIndex L = latIndex M) (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal)
    (hp : Rat.HeightOneSpectrum.natGenerator v ∣ casselsI L M)
    (hp2 : ¬ Rat.HeightOneSpectrum.natGenerator v ^ 2 ∣ casselsI L M)
    (hL : ∀ x ∈ loc v L.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1)
    (hM : ∀ x ∈ loc v M.1, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1)
    (hdet : ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧
      Valued.v (locGram Q v γ).det = 1) :
    ∃ β : orthGroup Q (v.adicCompletion ℚ), β ∈ Tamagawa.soSub Q (v.adicCompletion ℚ) ∧
      locAct v (β : GL (Fin n) (v.adicCompletion ℚ)) (loc v L.1) = loc v M.1 ∧
      spinorNorm Q (v.adicCompletion ℚ) β =
        sqClassOf (Rat.HeightOneSpectrum.natGenerator v : v.adicCompletion ℚ) := by
  classical
  obtain ⟨b, hb0, hb1, hb01, horth, -, hΛ, hΓ⟩ :=
    exists_hyperbolic_basis_of_casselsI Q hn h v h2 hp hp2 hL hM hdet
  set p : v.adicCompletion ℚ := (Rat.HeightOneSpectrum.natGenerator v : v.adicCompletion ℚ) with hpdef
  have hp0 : p ≠ 0 := by
    have := (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero
    rw [hpdef]; exact Nat.cast_ne_zero.mpr this
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  set x0 := b i0 with hx0
  set x1 := b i1 with hx1
  have hB01 : qbil Q (v.adicCompletion ℚ) x0 x1 = 2 / p := hb01
  have hB10 : qbil Q (v.adicCompletion ℚ) x1 x0 = 2 / p := by rw [qbil_comm]; exact hb01
  have hB00 : qbil Q (v.adicCompletion ℚ) x0 x0 = 0 := by rw [qbil_self, hb0, mul_zero]
  have hB11 : qbil Q (v.adicCompletion ℚ) x1 x1 = 0 := by rw [qbil_self, hb1, mul_zero]
  have hsr : ∀ (c : v.adicCompletion ℚ) (x z : Fin n → v.adicCompletion ℚ),
      qbil Q (v.adicCompletion ℚ) x (c • z) = c * qbil Q (v.adicCompletion ℚ) x z := fun c x z => by
    rw [qbil_comm, qbil_smul_left, qbil_comm]
  set w : Fin n → v.adicCompletion ℚ := x0 - x1 with hw
  set u : Fin n → v.adicCompletion ℚ := x0 - p • x1 with hu
  have hqww : qbil Q (v.adicCompletion ℚ) w w = -4 / p := by
    simp only [hw, qbil_sub_left, qbil_sub_right, hB00, hB01, hB10, hB11]; ring
  have hquu : qbil Q (v.adicCompletion ℚ) u u = -4 := by
    simp only [hu, qbil_sub_left, qbil_sub_right, hsr, qbil_smul_left, hB00, hB01, hB10, hB11]
    field_simp; ring
  have hQw : Q.evalIn (v.adicCompletion ℚ) w = -2 / p := by
    have := qbil_self Q (v.adicCompletion ℚ) w
    rw [hqww] at this
    field_simp at this
    rw [eq_div_iff hp0]
    linear_combination (-1 / 2 : v.adicCompletion ℚ) * this
  have hQu : Q.evalIn (v.adicCompletion ℚ) u = -2 := by
    have := qbil_self Q (v.adicCompletion ℚ) u
    rw [hquu] at this
    linear_combination (-1 / 2 : v.adicCompletion ℚ) * this
  have hQw0 : Q.evalIn (v.adicCompletion ℚ) w ≠ 0 := by
    rw [hQw]; exact div_ne_zero (by norm_num) hp0
  have hQu0 : Q.evalIn (v.adicCompletion ℚ) u ≠ 0 := by rw [hQu]; norm_num
  obtain ⟨hso, hsp⟩ := symm_mul_symm_spec hQ (K := v.adicCompletion ℚ) (x := u) (y := w) hQw0 hp0
    (by rw [hQu, hQw]; field_simp)
  refine ⟨symm Q (v.adicCompletion ℚ) u * symm Q (v.adicCompletion ℚ) w, hso, ?_, hsp⟩
  -- action on the basis
  have hτw0 : ((symm Q (v.adicCompletion ℚ) w : GL (Fin n) (v.adicCompletion ℚ)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)) *ᵥ x0 = x1 := by
    rw [symm_mulVec_bil Q _ hQw0]
    have : qbil Q (v.adicCompletion ℚ) w x0 = -2 / p := by
      simp only [hw, qbil_sub_left, hB00, hB10]; ring
    rw [this, hQw, div_self (div_ne_zero (by norm_num) hp0), one_smul, hw]; abel
  have hτw1 : ((symm Q (v.adicCompletion ℚ) w : GL (Fin n) (v.adicCompletion ℚ)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)) *ᵥ x1 = x0 := by
    rw [symm_mulVec_bil Q _ hQw0]
    have : qbil Q (v.adicCompletion ℚ) w x1 = 2 / p := by
      simp only [hw, qbil_sub_left, hB01, hB11]; ring
    have h3 : (2 / p) / (-2 / p) = (-1 : v.adicCompletion ℚ) := by field_simp
    rw [this, hQw, h3, neg_one_smul, hw]; abel
  have hτu0 : ((symm Q (v.adicCompletion ℚ) u : GL (Fin n) (v.adicCompletion ℚ)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)) *ᵥ x0 = p • x1 := by
    rw [symm_mulVec_bil Q _ hQu0]
    have : qbil Q (v.adicCompletion ℚ) u x0 = -2 := by
      simp only [hu, qbil_sub_left, qbil_smul_left, hB00, hB10]; field_simp; ring
    rw [this, hQu, div_self (by norm_num), one_smul, hu]; abel
  have hτu1 : ((symm Q (v.adicCompletion ℚ) u : GL (Fin n) (v.adicCompletion ℚ)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)) *ᵥ x1 = p⁻¹ • x0 := by
    rw [symm_mulVec_bil Q _ hQu0]
    have : qbil Q (v.adicCompletion ℚ) u x1 = 2 / p := by
      simp only [hu, qbil_sub_left, qbil_smul_left, hB01, hB11]; ring
    have h3 : (2 / p) / (-2 : v.adicCompletion ℚ) = -p⁻¹ := by field_simp
    rw [this, hQu, h3, neg_smul, sub_neg_eq_add, hu, smul_sub, smul_smul, inv_mul_cancel₀ hp0, one_smul]; abel
  have hβ : ∀ j : Fin n, ((symm Q (v.adicCompletion ℚ) u * symm Q (v.adicCompletion ℚ) w :
      orthGroup Q (v.adicCompletion ℚ)) : GL (Fin n) (v.adicCompletion ℚ)).val *ᵥ
      (if j.1 = 0 then p • b j else b j) = (if j.1 = 1 then p • b j else b j) := by
    intro j
    simp only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    by_cases h0 : j.1 = 0
    · have : j = i0 := Fin.ext h0
      subst this
      rw [if_pos h0, if_neg (by simp [i0]), Matrix.mulVec_smul, hτw0, Matrix.mulVec_smul, hτu1, smul_smul,
        mul_inv_cancel₀ hp0, one_smul]
    by_cases h1 : j.1 = 1
    · have : j = i1 := Fin.ext h1
      subst this
      rw [if_neg h0, if_pos h1, hτw1, hτu0]
    · rw [if_neg h0, if_neg h1]
      have hj : 2 ≤ j.1 := by omega
      have hwj : qbil Q (v.adicCompletion ℚ) w (b j) = 0 := by
        simp only [hw, qbil_sub_left]
        rw [horth i0 j (by simp [i0]) hj, horth i1 j (by simp [i1]) hj]; ring
      have huj : qbil Q (v.adicCompletion ℚ) u (b j) = 0 := by
        simp only [hu, qbil_sub_left, qbil_smul_left]
        rw [horth i0 j (by simp [i0]) hj, horth i1 j (by simp [i1]) hj]; ring
      rw [symm_fix Q _ hwj, symm_fix Q _ huj]
  rw [hΛ, locAct, Submodule.map_span, ← Set.range_comp]
  rw [hΓ]
  congr 1
  ext y
  simp only [Set.mem_range, Function.comp]
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨j, (hβ j).symm⟩
  · rintro ⟨j, rfl⟩; exact ⟨j, hβ j⟩

end QuadFormsKB.Lattices
