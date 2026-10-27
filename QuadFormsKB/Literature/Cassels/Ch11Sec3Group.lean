/-
# Cassels, Chapter 11, §3: the group $G = R/ST$ and Lemmas 3.4, 3.5

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n` (Cassels: $F = \mathbb Q$);
a lattice $\Lambda$ = `L : Lat F n`; a finite set $P$ of finite primes, `P : Finset (HeightOneSpectrum (𝓞 F))`;
$\theta(\Lambda_p) = \theta(O^+(L_\mathfrak p))$ = `localSpinorNormGroup`, $\theta(V) = \theta(O^+(V))$ =
`spinorNormGroup`; the finite adelic orthogonal group `OAf Q` acting on lattices by `latSMul`; Cassels' spinor genus is
the proper spinor genus `SameProperSpinorGenus` (`Ch11Sec1.lean`).

**Defines** Cassels' groups of (3.8)–(3.15) (pp. 208–209):
* `CasselsR P` $= R = \prod_{p \in P}\mathbb Q_p^\times$ (3.8), (3.9);
* `casselsS` $= S = \prod_{p \in P}\theta(\Lambda_p)$ (3.10);
* `casselsT` $= T$, the $t \in \theta(V)$ with $\lvert t\rvert_p = 1$ for all $p \notin P$ (3.12), embedded diagonally
  by `casselsDiag` (3.14); over $\mathbb Q$ (Lemma 3.2) $\theta(V)$ is $\mathbb Q^\times$ or, for definite $V$, the
  positive rationals, so $T$ is Cassels' $T$ ((3.12), (3.13); `mem_casselsT_rat_iff`);
* `CasselsG` $= G = R/ST$ (3.15).

Cassels' conditions on $P$ are (3.6) $2 \in P$ and (3.7) $\theta(\Lambda_p) = U_p(\mathbb Q_p^\times)^2$ for $p \notin P$;
(3.7) is the hypothesis `hP` below ((3.6) is not used in Lemmas 3.4 and 3.5).

**Proves**
* (3.11): $R^2 \subseteq S$ (`sq_mem_casselsS`).
* Lemma 3.4 (p. 209) (`exists_isProperIsometric_casselsForm`): every lattice of the genus is properly equivalent to a
  lattice $\Upsilon = \beta\Lambda$ with $\beta_p \in O^+(V_p)$, $\theta(\beta_p) \in U_p(\mathbb Q_p^\times)^2$ for
  $p \in P$ and $\theta(\beta_p) = 1$ for $p \notin P$ ((3.17)–(3.19)).
* Lemma 3.4, Corollary (p. 210) (`exists_sameProperSpinorGenus_casselsForm`): every spinor genus of the genus contains
  such a lattice with moreover $\Gamma_p = \Lambda_p$ for $p \notin P$.
* Lemma 3.5 (p. 210) (`sameProperSpinorGenus_smul_iff_casselsG`): for $\Gamma = \beta\Lambda$, $\Delta = \delta\Lambda$
  with $\beta_p, \delta_p \in O^+(V_p)$ for all $p$ and $\beta_p, \delta_p \in \Theta(V_p)$ for $p \notin P$, the lattices
  are in the same spinor genus iff $\{\theta(\beta_p)\}_{p\in P}$ and $\{\theta(\delta_p)\}_{p \in P}$ lie in one coset of
  $R$ modulo $ST$.
* Lemma 3.5, Corollary (p. 211) (`sameProperSpinorGenus_casselsShift`): the spinor genus of the lattice $\Delta$ with
  $\Delta_p = \alpha_p\Gamma_p$ ($p \in P$), $\Delta_p = \Gamma_p$ ($p \notin P$) depends only on the spinor genus of
  $\Gamma$ and the image of $\{\theta(\alpha_p)\}_{p \in P}$ in $G$.

Over a number field the statements need $\mathcal O_F$ to be a principal ideal domain (Cassels: $\mathbb Z$), and
Lemma 3.4 needs Cassels' Lemma 3.2 in the form `hval` (every nonzero $a_0 \in \mathcal O_F$ is a unit times an element of
$\theta(V)$; over $\mathbb Q$ this is `exists_unit_mul_mem_spinorNormGroup_rat`). The versions over $\mathbb Q$ are
`exists_isProperIsometric_casselsForm_rat` and `exists_sameProperSpinorGenus_casselsForm_rat`.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3
import QuadFormsKB.Literature.Cassels.Ch11Sec1Criterion

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### The groups $R$, $S$, $T$ and $G$ -/

section Groups

variable (hQ : Q.Nondegenerate) (L : Lat F n) (P : Finset (HeightOneSpectrum (𝓞 F)))

/-- **Cassels' group $R$** (Ch. 11, (3.8)–(3.9), p. 208): $R = \prod_{p \in P}\mathbb Q_p^\times$, the families
$\{c(p)\}_{p \in P}$ with $c(p) \in F_p^\times$, with componentwise multiplication. -/
abbrev CasselsR : Type := (v : P) → (v.1.adicCompletion F)ˣ

/-- **Cassels' group $S$** (Ch. 11, (3.10), p. 209): $S = \prod_{p \in P}\theta(\Lambda_p) \subseteq R$, with
$\theta(\Lambda_p) = \theta(O^+(\Lambda_p))$ (`localSpinorNormGroup`, which contains $(F_p^\times)^2$). -/
def casselsS : Subgroup (CasselsR P) :=
  Subgroup.pi Set.univ fun v => localSpinorNormGroup Q hQ v.1 L

/-- **Cassels' group $T$** (Ch. 11, (3.12)–(3.13), p. 209): the $t \in \theta(V)$ with $\lvert t\rvert_p = 1$ for all
$p \notin P$. Cassels takes the $t \in \mathbb Q^\times$ with $\lvert t\rvert_p = 1$ ($p \notin P$) and $t > 0$ if $V$ is
definite, which is the same group by Lemma 3.2 (`mem_casselsT_rat_iff`). -/
def casselsT : Subgroup Fˣ where
  carrier := {t | t ∈ spinorNormGroup Q hQ ∧
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ P → Valued.v (algebraMap F (v.adicCompletion F) (t : F)) = 1}
  mul_mem' {a b} ha hb := ⟨(spinorNormGroup Q hQ).mul_mem ha.1 hb.1, fun v hv => by
    rw [Units.val_mul, map_mul, map_mul, ha.2 v hv, hb.2 v hv, one_mul]⟩
  one_mem' := ⟨(spinorNormGroup Q hQ).one_mem, fun v _ => by simp⟩
  inv_mem' {a} ha := ⟨(spinorNormGroup Q hQ).inv_mem ha.1, fun v hv => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, ha.2 v hv, inv_one]⟩

/-- **The diagonal map** $F^\times \to R$, $t \mapsto \{t\}_{p \in P}$ (Cassels (3.14), p. 209). -/
def casselsDiag : Fˣ →* CasselsR P :=
  Pi.monoidHom fun v => Units.map (algebraMap F (v.1.adicCompletion F) : F →* v.1.adicCompletion F)

theorem casselsDiag_apply (t : Fˣ) (v : P) :
    ((casselsDiag P t v : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F) =
      algebraMap F (v.1.adicCompletion F) (t : F) := rfl

/-- The subgroup $ST$ of $R$ (Cassels (3.15), p. 209). -/
def casselsST : Subgroup (CasselsR P) := casselsS Q hQ L P ⊔ (casselsT Q hQ P).map (casselsDiag P)

/-- **Cassels' group $G = R/ST$** (Ch. 11, (3.15), p. 209). -/
abbrev CasselsG : Type := CasselsR P ⧸ casselsST Q hQ L P

/-- **Cassels (3.11)** (p. 209): $R^2 \subseteq S$. -/
theorem sq_mem_casselsS (r : CasselsR P) : r ^ 2 ∈ casselsS Q hQ L P := by
  rw [casselsS, Subgroup.mem_pi]
  intro v _
  rw [Pi.pow_apply, localSpinorNormGroup, Subgroup.mem_comap, map_pow, sq, SqClass.mul_self]
  exact Subgroup.one_mem _

end Groups

/-- Over $\mathbb Q$ the two `Algebra ℚ` structures on a completion agree on elements. -/
theorem algebraMap_adic_eq_rat (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) :
    @algebraMap ℚ (v.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v) x =
      algebraMap ℚ (v.adicCompletion ℚ) x :=
  (eq_ratCast (@algebraMap ℚ (v.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v)) x).trans
    (eq_ratCast (algebraMap ℚ (v.adicCompletion ℚ)) x).symm

/-- **$T$ over $\mathbb Q$** (Cassels (3.12)–(3.13), p. 209): for $n \ge 3$, $t \in T$ iff $\lvert t\rvert_p = 1$ for all
$p \notin P$ and, if $V$ is definite, $t > 0$ (by Lemma 3.2, `mem_spinorNormGroup_rat_iff`). -/
@[kb "cassels1978" "Ch. 11, (3.12)–(3.13), p. 209"]
theorem mem_casselsT_rat_iff {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (t : ℚˣ) :
    t ∈ casselsT Q hQ P ↔ (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P →
      Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (t : ℚ)) = 1) ∧ (¬ IsIndefinite Q → 0 < (t : ℚ)) := by
  change (t ∈ spinorNormGroup Q hQ ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P →
    Valued.v (@algebraMap ℚ (v.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v)
      (t : ℚ)) = 1) ↔ _
  simp only [algebraMap_adic_eq_rat]
  rw [mem_spinorNormGroup_rat_iff Q hQ hn]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact ⟨h2, fun h => absurd h1 h⟩
    · exact ⟨h2, fun _ => h1⟩
  · rintro ⟨h2, h1⟩
    by_cases h : IsIndefinite Q
    · exact ⟨Or.inl h, h2⟩
    · exact ⟨Or.inr (h1 h), h2⟩

/-- **Cassels' Lemma 3.2 in the form used in Lemmas 3.4 and 3.6** (over $\mathbb Q$, $n \ge 3$): every nonzero
$a_0 \in \mathbb Z$ is $\pm1$ times an element of $\theta(V)$ (namely $\lvert a_0\rvert$). -/
theorem exists_unit_mul_mem_spinorNormGroup_rat {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (a₀ : 𝓞 ℚ) (ha₀ : a₀ ≠ 0) : ∃ u : (𝓞 ℚ)ˣ, ∃ a ∈ spinorNormGroup Q hQ,
      (a : ℚ) = algebraMap (𝓞 ℚ) ℚ ((u : 𝓞 ℚ) * a₀) := by
  have hq : (algebraMap (𝓞 ℚ) ℚ a₀) ≠ 0 := by
    intro h
    exact ha₀ ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) ℚ)).mp h)
  by_cases hpos : 0 < algebraMap (𝓞 ℚ) ℚ a₀
  · refine ⟨1, Units.mk0 (algebraMap (𝓞 ℚ) ℚ a₀) hq, ?_, by simp⟩
    exact (mem_spinorNormGroup_rat_iff Q hQ hn _).mpr (Or.inr hpos)
  · have hneg : 0 < -(algebraMap (𝓞 ℚ) ℚ a₀) := by
      rcases lt_or_gt_of_ne hq with h | h
      · linarith
      · exact absurd h hpos
    refine ⟨-1, Units.mk0 (-(algebraMap (𝓞 ℚ) ℚ a₀)) (neg_ne_zero.mpr hq), ?_, by simp⟩
    exact (mem_spinorNormGroup_rat_iff Q hQ hn _).mpr (Or.inr hneg)

/-! ### Lemma 3.5 and its Corollary -/

/-! ### Helpers for Lemma 3.5 -/

section Lemma35Helpers

/-- A rotation in the spinor kernel has spinor norm $1$. -/
theorem spinorNorm_eq_one_of_mem_spinorKernel (hQ : Q.Nondegenerate) (K : Type) [Field K] [Algebra F K]
    [CharZero K] {g : orthGroup Q K} (h : g ∈ spinorKernel Q K) : spinorNorm Q K g = 1 := by
  rw [spinorKernel_eq_ker Q K hQ, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker,
    spinorNormHom_apply] at h
  exact h.1

/-- The class of a square is trivial. -/
theorem sqClass_mk_sq {K : Type} [Field K] [Algebra F K] [CharZero K] (a : Kˣ) :
    (SqClass.mk (a ^ 2) : SqClass K) = 1 :=
  (SqClass.mk_eq_one_iff _).mpr ⟨a, rfl⟩

/-- $a^{-1}bc^{-1} \equiv bac$ modulo squares. -/
theorem sqClass_mk_aux {K : Type} [Field K] [Algebra F K] [CharZero K] (a b c : Kˣ) :
    (SqClass.mk (a⁻¹ * b * c⁻¹) : SqClass K) = SqClass.mk (b * a * c) := by
  have : b * a * c = (a⁻¹ * b * c⁻¹) * (a * c) ^ 2 := by
    apply Units.ext
    have ha := a.ne_zero
    have hc := c.ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  rw [this, SqClass.mk_mul (a⁻¹ * b * c⁻¹) ((a * c) ^ 2), sqClass_mk_sq (F := F), mul_one]

theorem comm_group_aux {G : Type*} [CommGroup G] (X A B : G) : X * A⁻¹ * B ^ 2 * (A * (B⁻¹) ^ 2) = X := by
  have h : A⁻¹ * B ^ 2 * (A * B⁻¹ ^ 2) = 1 := by
    rw [mul_mul_mul_comm, inv_mul_cancel, inv_pow, mul_inv_cancel, one_mul]
  calc X * A⁻¹ * B ^ 2 * (A * (B⁻¹) ^ 2) = X * (A⁻¹ * B ^ 2 * (A * B⁻¹ ^ 2)) := by simp only [mul_assoc]
    _ = X := by rw [h, mul_one]

/-- **A unit square class has even valuation.** -/
theorem exists_valued_eq_exp_two_mul (v : HeightOneSpectrum (𝓞 F)) {z : v.adicCompletion F} (hz : z ≠ 0)
    (h : IsUnitSqClass v (sqClassOf z)) : ∃ m : ℤ, Valued.v z = WithZero.exp (2 * m) := by
  obtain ⟨u, hu1, hu⟩ := h
  have hu0 : u ≠ 0 := by rintro rfl; rw [map_zero] at hu1; exact zero_ne_one hu1
  have hzu : IsSquare (z * u) := (sqClassOf_eq_one_iff (mul_ne_zero hz hu0)).mp (by
    rw [sqClassOf_mul hz hu0, ← hu, SqClass.mul_self])
  obtain ⟨w, hw⟩ := hzu
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hz hu0 (by simpa using hw)
  refine ⟨WithZero.log (Valued.v w), ?_⟩
  have h1 : Valued.v (z * u) = Valued.v w * Valued.v w := by rw [hw, map_mul]
  rw [map_mul, hu1, mul_one] at h1
  have hvw : Valued.v w ≠ 0 := by simpa using hw0
  have hew := (WithZero.exp_log hvw).symm
  rw [h1]
  conv_lhs => rw [hew]
  rw [← WithZero.exp_add]
  congr 1
  ring

variable [IsPrincipalIdealRing (𝓞 F)]

/-- **Halving an even divisor** ($\mathcal O_F$ a PID): if $v(a)$ is a square (even exponent) at every $v \notin P$,
there is $s \in F^\times$ with $v(a) = v(s)^2$ at every $v \notin P$. -/
theorem exists_sq_scalar (P : Finset (HeightOneSpectrum (𝓞 F))) (a : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ P →
      ∃ m : ℤ, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = WithZero.exp (2 * m)) :
    ∃ s : Fˣ, ∀ v : HeightOneSpectrum (𝓞 F), v ∉ P →
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) =
        Valued.v (algebraMap F (v.adicCompletion F) (s : F)) ^ 2 := by
  classical
  let k : HeightOneSpectrum (𝓞 F) → ℤ :=
    fun v => WithZero.log (Valued.v (algebraMap F (v.adicCompletion F) (a : F))) / 2
  have hk : ∀ v, v ∉ P → Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = WithZero.exp (2 * k v) := by
    intro v hv
    obtain ⟨m, hm⟩ := h v hv
    simp only [k]
    rw [hm, WithZero.log_exp]
    congr 1
    omega
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 := by
    filter_upwards [eventually_valuation_le_one (F := F) (a : F), eventually_valuation_le_one (F := F) (a : F)⁻¹]
      with v h1 h2
    rw [valued_algebraMap v]
    rw [map_inv₀] at h2
    have h0 : v.valuation F (a : F) ≠ 0 := by simp
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v ∉ P ∧
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≠ 1}.Finite :=
    (Filter.eventually_cofinite.mp hev).subset fun v hv => hv.2
  set B := hfin.toFinset
  let s0 : F := ∏ w ∈ B, (algebraMap (𝓞 F) F (primeGen w)) ^ (-(k w))
  have hs0 : s0 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ =>
    zpow_ne_zero _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr (primeGen_ne_zero w))
  refine ⟨Units.mk0 s0 hs0, fun v hv => ?_⟩
  have hvs : Valued.v (algebraMap F (v.adicCompletion F) s0) =
      ∏ w ∈ B, (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (primeGen w))) ^ (-(k w)) := by
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_zpow₀, map_zpow₀, ← IsScalarTower.algebraMap_apply]
  have hother : ∀ w ∈ B, w ≠ v →
      (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (primeGen w))) ^ (-(k w)) = 1 := by
    intro w _ hwv
    rw [valued_algebraMap_int, intValuation_primeGen_of_ne v (Ne.symm hwv), _root_.one_zpow]
  by_cases hvB : v ∈ B
  · have h1 : Valued.v (algebraMap F (v.adicCompletion F) s0) = WithZero.exp (k v) := by
      rw [hvs, Finset.prod_eq_single_of_mem v hvB hother, valued_algebraMap_int, intValuation_primeGen_self,
        ← WithZero.exp_zsmul]
      congr 1
      simp
    simp only [Units.val_mk0]
    rw [h1, hk v hv, sq, ← WithZero.exp_add]
    congr 1
    ring
  · have h1 : Valued.v (algebraMap F (v.adicCompletion F) s0) = 1 := by
      rw [hvs]
      exact Finset.prod_eq_one fun w hw => hother w hw (fun hwv => hvB (hwv ▸ hw))
    have h2 : Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 := by
      by_contra hne
      exact hvB (hfin.mem_toFinset.mpr ⟨hv, hne⟩)
    simp only [Units.val_mk0]
    rw [h1, h2, one_pow]

variable {Q} in
/-- **Rotations with trivial components off $P$:** a lattice $\Gamma$ of the genus of $L$ with $\Gamma_v = L_v$ for
$v \notin P$ is $\beta L$ with rotation components and $\beta_v = 1$ for $v \notin P$. -/
theorem exists_oaf_soSub_one (hQ : Q.Nondegenerate) (L : Lat F n) (P : Finset (HeightOneSpectrum (𝓞 F)))
    {Γ : Lat F n} (hΓ : SameGenus Q L.1 Γ.1) (hΓP : ∀ v, v ∉ P → loc v Γ.1 = loc v L.1) :
    ∃ β : OAf Q, (∀ v, β v ∈ Tamagawa.soSub Q (v.adicCompletion F)) ∧ (∀ v, v ∉ P → β v = 1) ∧
      latSMul Q β L = Γ := by
  classical
  obtain ⟨h, hrot, hh⟩ := exists_oaf_soSub hQ L hΓ
  have hnP : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v ∉ P := by
    rw [Filter.eventually_cofinite]
    simp
  let b : OAf Q := ⟨fun v => if v ∈ P then h v else 1, by
    filter_upwards [hnP] with v hv
    rw [if_neg hv]
    exact (stdStab Q v).one_mem⟩
  refine ⟨b, fun v => ?_, fun v hv => ?_, Lat.ext (loc_injective (latSMul Q b L).2 Γ.2 fun v => ?_)⟩
  · by_cases hv : v ∈ P
    · change (if v ∈ P then h v else 1) ∈ _
      rw [if_pos hv]; exact hrot v
    · change (if v ∈ P then h v else 1) ∈ _
      rw [if_neg hv]; exact (Tamagawa.soSub Q _).one_mem
  · change (if v ∈ P then h v else 1) = 1
    rw [if_neg hv]
  · rw [loc_latSMul]
    by_cases hv : v ∈ P
    · have hb : b v = h v := if_pos hv
      rw [hb]
      have := congrArg (fun M : Lat F n => loc v M.1) hh
      simp only [loc_latSMul] at this
      exact this
    · have hb : b v = 1 := if_neg hv
      rw [hb, hΓP v hv]
      exact locAct_one _

end Lemma35Helpers

/-- **Cassels, Lemma 3.5** (Ch. 11, p. 210): *let $\Gamma, \Delta$ be in the genus of $\Lambda$ with
$\Gamma_p = \beta_p\Lambda_p$, $\Delta_p = \delta_p\Lambda_p$, $\beta_p, \delta_p \in O^+(V_p)$, and
$\beta_p, \delta_p \in \Theta(V_p)$ ($p \notin P$). Then a necessary and sufficient condition that $\Gamma, \Delta$ be
in the same spinor genus is that $\{\theta(\beta_p)\}_{p\in P}$ and $\{\theta(\delta_p)\}_{p \in P}$ should be in the
same coset of $R$ modulo $ST$.* Here $\Gamma = \beta\Lambda$, $\Delta = \delta\Lambda$ with $\beta, \delta \in
O(V)(\mathbb A_f)$; as in Cassels' note, $\{\theta(\beta_p)\}$ is represented by any $x \in R$ with
$x_p(\mathbb Q_p^\times)^2 = \theta(\beta_p)$. Over a number field with $\mathcal O_F$ a principal ideal domain and
Cassels' condition (3.7) on $P$ (`hP`). -/
@[kb "cassels1978" "Ch. 11, Lemma 3.5, p. 210 (over a number field, h_F = 1)"]
theorem sameProperSpinorGenus_smul_iff_casselsG [IsPrincipalIdealRing (𝓞 F)] (hQ : Q.Nondegenerate)
    (L : Lat F n) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (hP : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ P → ∀ u : (v.adicCompletion F)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    (β δ : OAf Q) (hβ : ∀ v, β v ∈ Tamagawa.soSub Q (v.adicCompletion F))
    (hδ : ∀ v, δ v ∈ Tamagawa.soSub Q (v.adicCompletion F))
    (hβP : ∀ v, v ∉ P → β v ∈ spinorKernel Q (v.adicCompletion F))
    (hδP : ∀ v, v ∉ P → δ v ∈ spinorKernel Q (v.adicCompletion F))
    (x y : CasselsR P) (hx : ∀ v : P, SqClass.mk (x v) = spinorNorm Q (v.1.adicCompletion F) (β v))
    (hy : ∀ v : P, SqClass.mk (y v) = spinorNorm Q (v.1.adicCompletion F) (δ v)) :
    SameProperSpinorGenus Q (latSMul Q β L) (latSMul Q δ L) ↔
      (QuotientGroup.mk x : CasselsG Q hQ L P) = QuotientGroup.mk y := by
  classical
  rw [sameProperSpinorGenus_smul_iff Q hQ L β δ hβ hδ, QuotientGroup.eq]
  constructor
  · rintro ⟨γ, hγ, H⟩
    obtain ⟨a, ha⟩ : ∃ a : Fˣ, spinorNorm Q F γ = SqClass.mk a :=
      SqClass.ind (P := fun c => ∃ a : Fˣ, c = SqClass.mk a) (fun x => ⟨x, rfl⟩) _
    have haD : a ∈ spinorNormGroup Q hQ := (mem_spinorNormGroup Q hQ).mpr ⟨γ, hγ, ha⟩
    have ha' : spinorNorm Q F γ = sqClassOf (a : F) := by
      rw [ha, sqClassOf_of_ne_zero a.ne_zero]; exact congrArg SqClass.mk (Units.ext rfl)
    let au : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ :=
      fun v => Units.map (algebraMap F (v.adicCompletion F) : F →* v.adicCompletion F) a
    have he : ∀ v : HeightOneSpectrum (𝓞 F),
        sqClassOf (algebraMap F (v.adicCompletion F) (a : F)) = SqClass.mk (au v) := fun v => by
      rw [sqClassOf_of_ne_zero ((map_ne_zero _).mpr a.ne_zero)]
      exact congrArg SqClass.mk (Units.ext rfl)
    have hγv : ∀ v : HeightOneSpectrum (𝓞 F),
        spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ) = SqClass.mk (au v) := fun v => by
      rw [spinorNorm_orthMap_of hQ v γ a.ne_zero ha', he]
    have hev : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ P →
        ∃ m : ℤ, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = WithZero.exp (2 * m) := by
      intro v hv
      obtain ⟨ρ, hρ, hρθ⟩ := H v
      rw [spinorNorm_eq_one_of_mem_spinorKernel Q hQ _ (hδP v hv),
        spinorNorm_eq_one_of_mem_spinorKernel Q hQ _ (hβP v hv), one_mul, one_mul, hγv] at hρθ
      have hmem : au v ∈ localSpinorNormGroup Q hQ v L :=
        (mem_localSpinorNormGroup Q hQ v L).mpr ⟨ρ, hρ, hρθ⟩
      have hu := (hP v hv (au v)).mp hmem
      refine exists_valued_eq_exp_two_mul v ((map_ne_zero _).mpr a.ne_zero) ?_
      rw [he]
      exact hu
    obtain ⟨s, hs⟩ := exists_sq_scalar P a hev
    have ht' : a * s⁻¹ ^ 2 ∈ casselsT Q hQ P := by
      refine ⟨(spinorNormGroup Q hQ).mul_mem haD (sq_mem_spinorNormGroup Q hQ _), fun v hv => ?_⟩
      have hne : Valued.v (algebraMap F (v.adicCompletion F) (s : F)) ≠ 0 := by
        simp
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_mul, map_pow, map_inv₀]
      rw [hs v hv, ← mul_pow, mul_inv_cancel₀ hne, one_pow]
    have hSmem : x⁻¹ * y * (casselsDiag P a)⁻¹ ∈ casselsS Q hQ L P := by
      rw [casselsS, Subgroup.mem_pi]
      rintro ⟨v, hvP⟩ -
      obtain ⟨ρ, hρ, hρθ⟩ := H v
      have h1 : SqClass.mk (y ⟨v, hvP⟩) = spinorNorm Q (v.adicCompletion F) (δ v) := hy ⟨v, hvP⟩
      have h2 : SqClass.mk (x ⟨v, hvP⟩) = spinorNorm Q (v.adicCompletion F) (β v) := hx ⟨v, hvP⟩
      rw [← h1, ← h2, hγv, ← SqClass.mk_mul, ← SqClass.mk_mul] at hρθ
      refine (mem_localSpinorNormGroup Q hQ v L).mpr ⟨ρ, hρ, ?_⟩
      rw [hρθ]
      exact (sqClass_mk_aux (F := F) (x ⟨v, hvP⟩) (y ⟨v, hvP⟩) (au v)).symm
    refine Subgroup.mem_sup.mpr ⟨_, (casselsS Q hQ L P).mul_mem hSmem
      (sq_mem_casselsS Q hQ L P (casselsDiag P s)), _, ⟨a * s⁻¹ ^ 2, ht', rfl⟩, ?_⟩
    simp only [map_mul, map_pow, map_inv]
    exact comm_group_aux _ _ _
  · intro h
    obtain ⟨s0, hs0, z, hz, hst⟩ := Subgroup.mem_sup.mp h
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨γ, hγ, hγθ⟩ := (mem_spinorNormGroup Q hQ).mp ht.1
    have hγθ' : spinorNorm Q F γ = sqClassOf (t : F) := by
      rw [hγθ, sqClassOf_of_ne_zero t.ne_zero]; exact congrArg SqClass.mk (Units.ext rfl)
    have hs0eq : s0 = x⁻¹ * y * (casselsDiag P t)⁻¹ := eq_mul_inv_of_mul_eq hst
    refine ⟨γ, hγ, fun v => ?_⟩
    rw [spinorNorm_orthMap_of hQ v γ t.ne_zero hγθ']
    by_cases hvP : v ∈ P
    · have h1 : SqClass.mk (y ⟨v, hvP⟩) = spinorNorm Q (v.adicCompletion F) (δ v) := hy ⟨v, hvP⟩
      have h2 : SqClass.mk (x ⟨v, hvP⟩) = spinorNorm Q (v.adicCompletion F) (β v) := hx ⟨v, hvP⟩
      have hm : s0 ⟨v, hvP⟩ ∈ localSpinorNormGroup Q hQ v L :=
        (by rw [casselsS, Subgroup.mem_pi] at hs0; exact hs0 ⟨v, hvP⟩ (Set.mem_univ _))
      obtain ⟨ρ, hρ, hρθ⟩ := (mem_localSpinorNormGroup Q hQ v L).mp hm
      refine ⟨ρ, hρ, ?_⟩
      rw [hρθ, ← h1, ← h2, sqClassOf_of_ne_zero ((map_ne_zero _).mpr t.ne_zero), ← SqClass.mk_mul,
        ← SqClass.mk_mul]
      have e : s0 ⟨v, hvP⟩ = (x ⟨v, hvP⟩)⁻¹ * y ⟨v, hvP⟩ *
          (Units.map (algebraMap F (v.adicCompletion F) : F →* v.adicCompletion F) t)⁻¹ :=
        congrFun hs0eq ⟨v, hvP⟩
      rw [e, sqClass_mk_aux (F := F)]
      exact congrArg SqClass.mk (by congr 1; exact Units.ext rfl)
    · rw [spinorNorm_eq_one_of_mem_spinorKernel Q hQ _ (hδP v hvP),
        spinorNorm_eq_one_of_mem_spinorKernel Q hQ _ (hβP v hvP), one_mul, one_mul]
      have hu : Units.map (algebraMap F (v.adicCompletion F) : F →* v.adicCompletion F) t ∈
          localSpinorNormGroup Q hQ v L := by
        refine (hP v hvP _).mpr ⟨algebraMap F (v.adicCompletion F) (t : F), ht.2 v hvP, ?_⟩
        rw [sqClassOf_of_ne_zero ((map_ne_zero _).mpr t.ne_zero)]
        exact congrArg SqClass.mk (Units.ext rfl)
      obtain ⟨ρ, hρ, hρθ⟩ := (mem_localSpinorNormGroup Q hQ v L).mp hu
      refine ⟨ρ, hρ, ?_⟩
      rw [hρθ, sqClassOf_of_ne_zero ((map_ne_zero _).mpr t.ne_zero)]
      exact congrArg SqClass.mk (Units.ext rfl)

/-- **Cassels, Lemma 3.5, Corollary** (Ch. 11, p. 211): *let $\Gamma$ be a lattice in the genus of $\Lambda$ with
$\Gamma_p = \Lambda_p$ ($p \notin P$) and let $\Delta$ be the lattice determined by $\Delta_p = \alpha_p\Gamma_p$
($p \in P$), $\Delta_p = \Gamma_p$ ($p \notin P$), where $\alpha_p \in O^+(V_p)$. Then the spinor genus of $\Delta$
depends only on the spinor genus of $\Gamma$ and the image $g$ of $\{\theta(\alpha_p)\}_{p\in P}$ in $G = R/ST$.*
(The condition (3.31) on $\alpha_p$ is lost in the scan; $\alpha_p \in O^+(V_p)$ is reconstructed from the proof of
Theorem 3.1.) Here $\Delta = \alpha\Gamma$ with $\alpha \in O(V)(\mathbb A_f)$, $\alpha_p \in O^+(V_p)$ for $p \in P$
and $\alpha_p = 1$ for $p \notin P$; likewise $\Delta' = \alpha'\Gamma'$; $x, x' \in R$ represent the spinor norms. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.5, Cor., p. 211 (over a number field, h_F = 1; (3.31) reconstructed)"]
theorem sameProperSpinorGenus_casselsShift [IsPrincipalIdealRing (𝓞 F)] (hQ : Q.Nondegenerate)
    (L : Lat F n) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (hP : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ P → ∀ u : (v.adicCompletion F)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    {Γ Γ' : Lat F n} (hΓ : SameGenus Q L.1 Γ.1) (hΓP : ∀ v, v ∉ P → loc v Γ.1 = loc v L.1)
    (hΓ'P : ∀ v, v ∉ P → loc v Γ'.1 = loc v L.1) (hΓΓ' : SameProperSpinorGenus Q Γ Γ')
    (α α' : OAf Q) (hα : ∀ v, α v ∈ Tamagawa.soSub Q (v.adicCompletion F))
    (hα' : ∀ v, α' v ∈ Tamagawa.soSub Q (v.adicCompletion F))
    (hαP : ∀ v, v ∉ P → α v = 1) (hα'P : ∀ v, v ∉ P → α' v = 1)
    (x x' : CasselsR P) (hx : ∀ v : P, SqClass.mk (x v) = spinorNorm Q (v.1.adicCompletion F) (α v))
    (hx' : ∀ v : P, SqClass.mk (x' v) = spinorNorm Q (v.1.adicCompletion F) (α' v))
    (hxx' : (QuotientGroup.mk x : CasselsG Q hQ L P) = QuotientGroup.mk x') :
    SameProperSpinorGenus Q (latSMul Q α Γ) (latSMul Q α' Γ') := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  have hΓ' : SameGenus Q L.1 Γ'.1 :=
    SameGenus.trans Q hΓ (SameSpinorGenus.sameGenus Q (SameProperSpinorGenus.sameSpinorGenus Q hΓΓ'))
  obtain ⟨β, hβ, hβ1, rfl⟩ := exists_oaf_soSub_one hQ L P hΓ hΓP
  obtain ⟨β', hβ', hβ'1, rfl⟩ := exists_oaf_soSub_one hQ L P hΓ' hΓ'P
  have hrep : ∀ g : OAf Q, ∃ z : CasselsR P,
      ∀ v : P, SqClass.mk (z v) = spinorNorm Q (v.1.adicCompletion F) (g v.1) := fun g => by
    choose z hz using fun v : P => SqClass.ind
      (P := fun c : SqClass (v.1.adicCompletion F) => ∃ a : (v.1.adicCompletion F)ˣ, SqClass.mk a = c)
      (fun a => ⟨a, rfl⟩) (spinorNorm Q (v.1.adicCompletion F) (g v.1))
    exact ⟨z, hz⟩
  obtain ⟨z, hz⟩ := hrep β
  obtain ⟨z', hz'⟩ := hrep β'
  have hker : ∀ g : OAf Q, (∀ v, v ∉ P → g v = 1) →
      ∀ v, v ∉ P → g v ∈ spinorKernel Q (v.adicCompletion F) := fun g hg v hv => by
    rw [hg v hv]; exact (spinorKernel Q _).one_mem
  have h1 := (sameProperSpinorGenus_smul_iff_casselsG Q hQ L P hP β β' hβ hβ' (hker β hβ1) (hker β' hβ'1)
    z z' hz hz').mp hΓΓ'
  have e1 : latSMul Q α (latSMul Q β L) = latSMul Q (α * β) L := (mul_smul α β L).symm
  have e2 : latSMul Q α' (latSMul Q β' L) = latSMul Q (α' * β') L := (mul_smul α' β' L).symm
  rw [e1, e2]
  have hmul1 : ∀ v, v ∉ P → (α * β) v = 1 := fun v hv => by
    change α v * β v = 1
    rw [hαP v hv, hβ1 v hv, mul_one]
  have hmul2 : ∀ v, v ∉ P → (α' * β') v = 1 := fun v hv => by
    change α' v * β' v = 1
    rw [hα'P v hv, hβ'1 v hv, mul_one]
  refine (sameProperSpinorGenus_smul_iff_casselsG Q hQ L P hP (α * β) (α' * β')
    (fun v => (Tamagawa.soSub Q _).mul_mem (hα v) (hβ v))
    (fun v => (Tamagawa.soSub Q _).mul_mem (hα' v) (hβ' v)) (hker _ hmul1) (hker _ hmul2)
    (x * z) (x' * z') ?_ ?_).mpr ?_
  · intro v
    change SqClass.mk (x v * z v) = spinorNorm Q (v.1.adicCompletion F) (α v * β v)
    rw [SqClass.mk_mul, hx v, hz v]
    exact (map_mul (spinorNormHom Q (v.1.adicCompletion F) hQ) (α v) (β v)).symm
  · intro v
    change SqClass.mk (x' v * z' v) = spinorNorm Q (v.1.adicCompletion F) (α' v * β' v)
    rw [SqClass.mk_mul, hx' v, hz' v]
    exact (map_mul (spinorNormHom Q (v.1.adicCompletion F) hQ) (α' v) (β' v)).symm
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hxx', h1]

end QuadFormsKB.Lattices
