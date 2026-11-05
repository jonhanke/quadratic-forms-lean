/-
# O'Meara §93D, Example 93:18 (v): unimodular lattices of dimension $\ge 5$

**Setting** as in `Sec93D18Q.lean`: $R$ a Henselian discrete valuation ring with finite residue field, fraction field
$F$ of characteristic $0$ satisfying the Hilbert-symbol axioms `PadicClass.LocalHilbertField`, $F$ dyadic.

**Page image read** (O'Meara 1973 printing, p. 261): "(v) If $\dim L \ge 5$ we claim that
$L \cong \langle A(0,0)\rangle \perp \cdots$, and so $\mathfrak gL = Q(L)$. We can assume that
$\operatorname{ord}_{\mathfrak p} a + \operatorname{ord}_{\mathfrak p} b$ is odd. First we take a quaternary unimodular
sublattice of $L$ which has norm $a\mathfrak o$. If this quaternary lattice has weight $b\mathfrak p^{2r+1}$
$(r \ge 0)$ it will have the form $\langle A(0,0)\rangle \perp \cdots$ by (ii) and we will be through. Otherwise it will
have weight $b\mathfrak p^{2r}$ $(r \ge 0)$ in which case we obtain $L \cong \langle A(b\pi^{2r}, 2\alpha)\rangle \perp K$
for some $\alpha$ in $\mathfrak o$ by (iii). Here $\mathfrak nK$ is still $a\mathfrak o$. If we repeat the above
procedure on a suitable ternary or quaternary sublattice of $K$ we either obtain $K \cong \langle A(0,0)\rangle \perp
\cdots$, or else $L \cong \langle A(b\pi^{2r}, 2\alpha)\rangle \perp \langle A(b\pi^{2t}, 2\beta)\rangle \perp \cdots$
for some $t \ge 0$ and some $\beta$ in $\mathfrak o$. In the first event we are through. Otherwise we can assume that
$r \ge t$, say. Then $L \cong \langle A(2b\pi^{2r}, 2\alpha)\rangle \perp \cdots \cong \langle A(0,0)\rangle \perp
\cdots$."

**Proves**
* `mem_right_of_orth`: in $L = N \perp K$ with $N$ regular, a vector of $L$ orthogonal to $N$ lies in $K$;
* `hyp_or_block` (the step "by (ii) ... by (iii)" of the proof, also for ternary lattices by (iv)): a unimodular
  lattice $M$ of rank $3$ or $4$ with norm generator $Q(z)$ and $\mathfrak wM \subseteq b\mathfrak o$,
  $\operatorname{ord} Q(z) + \operatorname{ord} b$ odd, contains a hyperbolic pair, or a pair $x, y$ with
  $Q(x) = b\pi^{2r}$, $B(x,y) = 1$, $Q(y) \in 2\mathfrak o$, and a vector $z' \perp x, y$ with
  $Q(z')\mathfrak o = Q(z)\mathfrak o$;
* `omeara93_18_v` (**93:18 (v)**): a unimodular lattice of rank $\ge 5$ contains $x, y$ with $Q(x) = Q(y) = 0$,
  $B(x, y) = 1$; `omeara93_18_v_splitting`: $L = (\mathfrak ox + \mathfrak oy) \perp K$, i.e.
  $L \cong \langle A(0,0)\rangle \perp K$; `omeara93_18_v_normGroup`: $\mathfrak gL = Q(L)$.

The argument is O'Meara's. Two details are made explicit: the sublattices are taken carrying a vector $z$ with
$Q(z)\mathfrak o = \mathfrak nL$ (`exists_small_sublattice`), which keeps track of "$\mathfrak nK$ is still
$a\mathfrak o$" (for a ternary sublattice, the block $\langle -d\rangle$ of (iv) plays this role); and the weight
generator $b\pi^{2r}$ is used as the weight generator in (iii)/(iv), which those results allow.
-/
import QuadFormsKB.Literature.OMeara.Sec93D18Aux

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.D18

section Orth

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- In an orthogonal splitting $L = N \perp K$ with $N$ regular, a vector of $L$ orthogonal to $N$ lies in $K$. -/
theorem mem_right_of_orth {L N K : Submodule R V} (h : IsOrthSum Q L N K) (hN : IsRegular Q N) {w : V}
    (hw : w ∈ L) (horth : ∀ n ∈ N, bil Q w n = 0) : w ∈ K := by
  rw [← h.sup_eq] at hw
  obtain ⟨n, hn, k, hk, rfl⟩ := Submodule.mem_sup.mp hw
  have hn0 : n = 0 := hN n hn fun y hy => by
    have h1 := horth y hy
    rw [bil_add_left] at h1
    have h2 : bil Q k y = 0 := by rw [bil_comm]; exact h.orth y hy k hk
    linear_combination h1 - h2
  rw [hn0, zero_add]
  exact hk

end Orth

section Block

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **The step "by (ii) ... by (iii)" of O'Meara's proof of 93:18 (v)** (p. 261): let $M$ be a unimodular lattice of
rank $3$ or $4$ with norm generator $Q(z)$, and $b \ne 0$ with $\mathfrak wM \subseteq b\mathfrak o$ and
$\operatorname{ord} Q(z) + \operatorname{ord} b$ odd. Then either $M$ contains $x, y$ with $Q(x) = Q(y) = 0$,
$B(x, y) = 1$ (93:18 (ii)), or $M$ contains $x, y$ with $Q(x) = b\pi^{2r}$ for some $r \ge 0$, $B(x, y) = 1$,
$Q(y) \in 2\mathfrak o$, and a vector $z'$ orthogonal to $x, y$ with $Q(z')\mathfrak o = Q(z)\mathfrak o$
(93:18 (iii) with the weight generator $b\pi^{2r}$; 93:18 (iv) in rank $3$). -/
theorem hyp_or_block (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {ρ : R}
    (hρ : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)}) {M : Submodule R V} (hfg : M.FG)
    (hU : IsUnimodular Q M) (hrk : finrank R M = 3 ∨ finrank R M = 4) {z : V}
    (hzn : IsNormGenerator Q M (Q z)) {b : F} (hb0 : b ≠ 0) (hwb : weight Q M ≤ R ∙ b)
    (hodd : Odd (dord hπ (Q z) + dord hπ b)) :
    (∃ x ∈ M, ∃ y ∈ M, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1) ∨
      ∃ r : ℕ, ∃ x ∈ M, ∃ y ∈ M, Q x = b * algebraMap R F π ^ (2 * r) ∧ bil Q x y = 1 ∧
        (∃ γ : R, Q y = 2 * algebraMap R F γ) ∧
        ∃ z' ∈ M, R ∙ Q z' = R ∙ Q z ∧ bil Q z' x = 0 ∧ bil Q z' y = 0 := by
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q M := IsModular.isRegular Q hU hfg
  have ha0 := hzn.ne_zero Q hreg hne
  obtain ⟨b', hb'⟩ := exists_isWeightGenerator Q h2p hfg hU
  have hb'0 := weight_gen_ne_zero Q hzn ha0 hb'
  by_cases hev : Even (dord hπ (Q z) + dord hπ b')
  · left
    exact Uni93.exists_hyperbolic_pair_of_even Q h2p hπ hfg hU (by omega) hzn hb' hev
  right
  have hb'b : b' ∈ R ∙ b := hwb (hb' ▸ mem_span_singleton_self b')
  have hle := (mem_span_iff hπ hb'0 hb0).mp hb'b
  obtain ⟨m, hm⟩ := Int.not_even_iff_odd.mp hev
  obtain ⟨m', hm'⟩ := hodd
  obtain ⟨k, hk⟩ : ∃ k : ℕ, dord hπ b' = dord hπ b + 2 * k := ⟨(m - m').toNat, by omega⟩
  have hπ0 := alg_pi_ne_zero (R := R) (F := F) hπ
  set b'' := b * algebraMap R F π ^ (2 * k) with hb''def
  have hb''0 : b'' ≠ 0 := mul_ne_zero hb0 (pow_ne_zero _ hπ0)
  have hdb'' : dord hπ b'' = dord hπ b' := by
    rw [hb''def, dord_mul hπ hb0 (pow_ne_zero _ hπ0), ← zpow_natCast, dord_zpow, hk]
    push_cast; ring
  have hb'' : IsWeightGenerator Q M b'' := (span_eq_of_dord_eq hπ hb''0 hb'0 hdb'').trans hb'
  have hodd'' : Odd (dord hπ (Q z) + dord hπ b'') := by
    rw [hdb'']; exact Int.not_even_iff_odd.mp hev
  -- `2 = t b''`, so `4ρ/b'' = 2 (tρ)`
  have h1L : (1 : F) ∈ scale Q M := by rw [hU.2.1]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have h2b : (2 : F) ∈ R ∙ b'' := two_smul_scale_le_weight_gen Q hb''
    (by simpa using smul_mem_pointwise_smul (1 : F) (2 : F) _ h1L)
  obtain ⟨t, ht⟩ := mem_span_singleton.mp h2b
  rw [Algebra.smul_def] at ht
  have h4 : 4 * algebraMap R F ρ / b'' = 2 * algebraMap R F (t * ρ) := by
    rw [map_mul]; field_simp; linear_combination (-(2 * algebraMap R F ρ)) * ht
  have h2m : (2 : R) ∈ maximalIdeal R := Uni93.two_mem_maximalIdeal h2p
  have h4m : 4 * ρ ∈ maximalIdeal R := by
    rw [show (4 : R) * ρ = 2 * (2 * ρ) by ring]; exact Ideal.mul_mem_right _ _ h2m
  rcases hrk with h3 | h4'
  · -- ternary: 93:18 (iv)
    obtain ⟨e₀⟩ := exists_basis (R := R) (F := F) hfg
    let e1 : Basis (Fin 3) R M := e₀.reindex (finCongr h3)
    obtain ⟨u, hu, hdet⟩ := Eng93.isUnit_det_of_isUnimodular Q hU e1
    have key := omeara93_18_iv_sub Q hK h2p hπ hfg hU h3 hzn hb'' hodd'' ⟨e1, hdet⟩ hρ
    have ext : ∀ {γ c : F}, HasBlk1 Q M b'' γ c → (∃ γ₀ : R, γ = 2 * algebraMap R F γ₀) →
        (∃ c₀ : R, IsUnit c₀ ∧ c = algebraMap R F c₀) →
        ∃ r : ℕ, ∃ x ∈ M, ∃ y ∈ M, Q x = b * algebraMap R F π ^ (2 * r) ∧ bil Q x y = 1 ∧
          (∃ γ : R, Q y = 2 * algebraMap R F γ) ∧
          ∃ z' ∈ M, R ∙ Q z' = R ∙ Q z ∧ bil Q z' x = 0 ∧ bil Q z' y = 0 := by
      rintro γ c ⟨e, he⟩ ⟨γ₀, hγ₀⟩ ⟨c₀, hc₀, rfl⟩
      have hQe : ∀ i j, bil Q (e i : V) (e j : V) = blk1 b'' γ (algebraMap R F c₀) i j := fun i j => by
        simpa [gram] using congrFun (congrFun he i) j
      have hQ2 : Q (e 2 : V) = algebraMap R F c₀ := by rw [← bil_self, hQe]; simp [blk1]
      refine ⟨k, e 0, (e 0).2, e 1, (e 1).2, ?_, ?_, ⟨γ₀, ?_⟩, e 2, (e 2).2, ?_, ?_, ?_⟩
      · rw [← bil_self, hQe]; simp [blk1, hb''def]
      · rw [hQe]; simp [blk1]
      · rw [← bil_self, hQe]; simpa [blk1] using hγ₀
      · rw [hQ2, hzn.2]
        apply le_antisymm
        · rw [span_singleton_le_iff_mem, ← hQ2]; exact Q_mem_normIdeal Q (e 2).2
        · refine (normIdeal_le_scale Q M).trans ?_
          rw [hU.2.1, u93_span_unit hc₀]
      · rw [hQe]; simp [blk1]
      · rw [hQe]; simp [blk1]
    rcases key with ⟨hJ, -⟩ | ⟨hK', -⟩
    · exact ext hJ ⟨0, by simp⟩ ⟨-u, hu.neg, by rw [map_neg]⟩
    · have heu : IsUnit (1 - 4 * ρ) := by
        simpa [sub_eq_add_neg] using isUnit_one_add_aux (neg_mem h4m)
      exact ext hK' ⟨t * ρ, h4⟩ ⟨-(u * (1 - 4 * ρ)), (hu.mul heu).neg, by
        simp only [map_neg, map_mul, map_sub, map_one, map_ofNat]⟩
  · -- quaternary: 93:18 (iii)
    obtain ⟨α, hd, hdef⟩ := exists_basis_det_one_add Q h2p hfg hU h4'
    have key := (omeara93_18_iii_sub Q hK h2p hπ hfg hU h4' hzn hb'' hodd'' hd hdef hρ).2
    have ext : ∀ {q s : F}, HasBlk Q M (Q z) q b'' s → (∃ γ₀ : R, s = 2 * algebraMap R F γ₀) →
        ∃ r : ℕ, ∃ x ∈ M, ∃ y ∈ M, Q x = b * algebraMap R F π ^ (2 * r) ∧ bil Q x y = 1 ∧
          (∃ γ : R, Q y = 2 * algebraMap R F γ) ∧
          ∃ z' ∈ M, R ∙ Q z' = R ∙ Q z ∧ bil Q z' x = 0 ∧ bil Q z' y = 0 := by
      rintro q s ⟨e, he⟩ ⟨γ₀, hγ₀⟩
      have hQe : ∀ i j, bil Q (e i : V) (e j : V) = blk2 (Q z) q b'' s i j := fun i j => by
        simpa [gram] using congrFun (congrFun he i) j
      refine ⟨k, e 2, (e 2).2, e 3, (e 3).2, ?_, ?_, ⟨γ₀, ?_⟩, e 0, (e 0).2, ?_, ?_, ?_⟩
      · rw [← bil_self, hQe]; simp [blk2, hb''def]
      · rw [hQe]; simp [blk2]
      · rw [← bil_self, hQe]; simpa [blk2] using hγ₀
      · rw [← bil_self, hQe]; simp [blk2]
      · rw [hQe]; simp [blk2]
      · rw [hQe]; simp [blk2]
    rcases key with ⟨hJ, -⟩ | ⟨hK', -⟩
    · exact ext hJ ⟨0, by simp⟩
    · exact ext hK' ⟨t * ρ, h4⟩

end Block

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **The last step of O'Meara's proof of 93:18 (v)** ("$L \cong \langle A(2b\pi^{2r}, 2\alpha)\rangle \perp \cdots
\cong \langle A(0,0)\rangle \perp \cdots$"): if $u, v, u' \in L$ with $Q(u) = b\pi^{2s}$, $B(u, v) = 1$,
$Q(v) \in 2\mathfrak o$, $Q(u') = b\pi^{2s'}$, $s' \le s$, $u' \perp u, v$ and $b \in \mathfrak p$, then $L$
contains a hyperbolic pair: $Q(u + \pi^{s - s'}u') = 2b\pi^{2s} \in 2\mathfrak p$. -/
theorem exists_hyperbolic_of_two_blocks (h2p : ¬ IsUnit (2 : R)) {π : R} {L : Submodule R V} {u v u' : V}
    (hu : u ∈ L) (hv : v ∈ L) (hu' : u' ∈ L) {b₀ : R} (hb₀ : b₀ ∈ maximalIdeal R) {s s' : ℕ} {γ : R}
    (hQu : Q u = algebraMap R F b₀ * algebraMap R F π ^ (2 * s)) (huv : bil Q u v = 1)
    (hQv : Q v = 2 * algebraMap R F γ) (hQu' : Q u' = algebraMap R F b₀ * algebraMap R F π ^ (2 * s'))
    (huu' : bil Q u u' = 0) (hu'v : bil Q u' v = 0) (hss : s' ≤ s) :
    ∃ x ∈ L, ∃ y ∈ L, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1 := by
  set w : V := u + (π ^ (s - s')) • u' with hw
  have hwL : w ∈ L := L.add_mem hu (L.smul_mem _ hu')
  have hQw : Q w = 2 * algebraMap R F (b₀ * π ^ (2 * s)) := by
    rw [hw, Q_add, Q_rsmul, bil_rsmul_right, huu', hQu, hQu']
    simp only [map_mul, map_pow]
    have hp : (algebraMap R F π ^ (s - s')) ^ 2 * algebraMap R F π ^ (2 * s') = algebraMap R F π ^ (2 * s) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    linear_combination (algebraMap R F b₀) * hp
  have hwv : bil Q w v = 1 := by
    rw [hw, bil_add_left, bil_rsmul_left, huv, hu'v, mul_zero, add_zero]
  obtain ⟨x, hx, y, hy, h1, h2, h3⟩ := Uni93.exists_hyperbolic_of_even_pair Q h2p hQw hQv hwv
    (Ideal.mul_mem_right _ _ hb₀)
  have hsp : span R {w, v} ≤ L := by
    rw [span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact hwL
    · exact hv
  exact ⟨x, hsp hx, y, hsp hy, h1, h2, h3⟩

/-- **Example 93:18 (v)** (O'Meara 1963, §93D, p. 261): a unimodular lattice $L$ of dimension $\ge 5$ over a dyadic
local field contains $x, y$ with $Q(x) = Q(y) = 0$ and $B(x, y) = 1$, i.e. $L \cong \langle A(0,0)\rangle \perp
\cdots$ (see `omeara93_18_v_splitting`; and so $\mathfrak gL = Q(L)$, `omeara93_18_v_normGroup`).

*Form of the statement.* The local field is abstract, as in `omeara93_18_iii`. The lattice $L$ need not be a lattice
on $V$ (any unimodular $L \subseteq V$ of rank $\ge 5$). -/
@[kb "omeara1963" "§93D, 93:18 (v), p. 261"]
theorem omeara93_18_v (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hU : IsUnimodular Q L) (hrk : 5 ≤ finrank R L) :
    ∃ x ∈ L, ∃ y ∈ L, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1 := by
  have hinj := IsFractionRing.injective R F
  have h2R : (2 : R) ≠ 0 := fun h => two_ne_zero (α := F) (by rw [← map_ofNat (algebraMap R F) 2, h, map_zero])
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ρ, -, hρ⟩ := G93.exists_delta (F := F) h2R h2p hπ
  have hne := Uni93.ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  obtain ⟨b, hb⟩ := exists_isWeightGenerator Q h2p hfg hU
  obtain ⟨M, hML, hMfg, hMU, hMrk, z, hzM, hzn⟩ := exists_small_sublattice Q h2p hfg hU (by omega)
  have hzL := hML hzM
  have haL : IsNormGenerator Q L (Q z) := ⟨Q_mem_normGroup Q hzL, hzn⟩
  have ha0 := haL.ne_zero Q hreg hne
  have hb0 := weight_gen_ne_zero Q haL ha0 hb
  by_cases hev : Even (dord hπ (Q z) + dord hπ b)
  · exact Uni93.exists_hyperbolic_pair_of_even Q h2p hπ hfg hU (by omega) haL hb hev
  have hodd : Odd (dord hπ (Q z) + dord hπ b) := Int.not_even_iff_odd.mp hev
  have hwL : ∀ {N : Submodule R V}, N ≤ L → weight Q N ≤ R ∙ b := fun hN => hb ▸ weight_mono Q hN
  have hng : ∀ {N : Submodule R V} {w : V}, N ≤ L → w ∈ N → R ∙ Q w = normIdeal Q L →
      IsNormGenerator Q N (Q w) := fun hN hw hwn =>
    ⟨Q_mem_normGroup Q hw, le_antisymm ((span_singleton_le_iff_mem _ _).mpr (Q_mem_normIdeal Q hw))
      (hwn ▸ Uni93.normIdeal_mono' Q hN)⟩
  rcases hyp_or_block Q hK h2p hπ hρ hMfg hMU hMrk (hng hML hzM hzn) hb0 (hwL hML) hodd with
    ⟨x, hx, y, hy, h⟩ | ⟨r, x₁, hx₁, y₁, hy₁, hQx₁, hxy₁, ⟨γ₁, hγ₁⟩, z₁, hz₁M, hz₁n, hz₁x, hz₁y⟩
  · exact ⟨x, hML hx, y, hML hy, h⟩
  -- `b = b₀ ∈ 𝔭`
  have hbs : b ∈ (1 : Submodule R F) := by
    rw [← hU.2.1]; exact normIdeal_le_scale Q L ((weight_bounds Q L).2.2.2 (hb ▸ mem_span_singleton_self b))
  obtain ⟨b₀, hb₀⟩ := Submodule.mem_one.mp hbs
  have hb₀m : b₀ ∈ maximalIdeal R := by
    by_contra hn
    have hu : IsUnit b₀ := by
      by_contra hu; exact hn ((mem_maximalIdeal _).mpr hu)
    have hdb : dord hπ b = 0 := by rw [← hb₀]; exact dord_unit hπ hu
    have hbz : b ∈ R ∙ Q z := weight_gen_le_norm_gen Q haL hb (mem_span_singleton_self b)
    have h1 := (mem_span_iff hπ hb0 ha0).mp hbz
    obtain ⟨q₀, hq₀⟩ := a10_mem_one Q hU hzL hzL
    rw [bil_self] at hq₀
    have hq₀0 : q₀ ≠ 0 := fun h => ha0 (by rw [← hq₀, h, map_zero])
    have h2 := dord_alg_nonneg (F := F) hπ hq₀0
    rw [hq₀] at h2
    have hz0 : dord hπ (Q z) = 0 := by omega
    rw [hz0, hdb] at hodd
    exact (Int.not_odd_iff_even.mpr ⟨0, rfl⟩) hodd
  -- the first block `N₁ = 𝔬x₁ + 𝔬y₁` splits `L`
  have hx₁L := hML hx₁
  have hy₁L := hML hy₁
  have hqx : ¬ IsUnit (b₀ * π ^ (2 * r)) := fun h =>
    (mem_maximalIdeal _).mp hb₀m (isUnit_of_mul_isUnit_left h)
  have hN₁ := Uni93.span_pair_unimodular Q hqx isUnit_one
    (by rw [hQx₁, ← hb₀]; simp only [map_mul, map_pow])
    (show Q y₁ = algebraMap R F (2 * γ₁) by rw [hγ₁, map_mul, map_ofNat])
    (by rw [hxy₁, map_one])
  have hN₁L : span R {x₁, y₁} ≤ L := by
    rw [span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact hx₁L
    · exact hy₁L
  have hN₁fg : (span R {x₁, y₁}).FG := fg_span (Set.toFinite _)
  obtain ⟨K₁, hK₁⟩ := splits_of_isModular_of_scale_eq Q hN₁L hN₁.1 hN₁fg hU.2.1
  have hrkL := isOrthSum_finrank Q hK₁ hfg
  have hK₁0 : K₁ ≠ ⊥ := by
    rintro rfl
    simp at hrkL; omega
  have hK₁le : K₁ ≤ L := hK₁.sup_eq ▸ le_sup_right
  have hK₁fg : K₁.FG := FG.of_le hfg hK₁le
  have hK₁U := u93_isUnimodular_of_orth Q hfg hU hN₁.1 hK₁ hK₁0
  -- `z₁ ∈ K₁`, so `𝔫K₁ = 𝔫L`
  have hz₁K : z₁ ∈ K₁ := by
    refine mem_right_of_orth Q hK₁ (IsModular.isRegular Q hN₁.1 hN₁fg) (hML hz₁M) ?_
    refine Uni93.bil_zero_on_span Q (S := {x₁, y₁}) ?_
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact hz₁x
    · exact hz₁y
  have hz₁nL : R ∙ Q z₁ = normIdeal Q L := hz₁n.trans hzn
  have hnK₁ : normIdeal Q K₁ = normIdeal Q L :=
    le_antisymm (Uni93.normIdeal_mono' Q hK₁le)
      (hz₁nL ▸ (span_singleton_le_iff_mem _ _).mpr (Q_mem_normIdeal Q hz₁K))
  -- repeat on a ternary or quaternary sublattice of `K₁`
  obtain ⟨M₂, hM₂K, hM₂fg, hM₂U, hM₂rk, z₂, hz₂M, hz₂n⟩ :=
    exists_small_sublattice Q h2p hK₁fg hK₁U (by omega)
  have hM₂L : M₂ ≤ L := hM₂K.trans hK₁le
  have hz₂nL : R ∙ Q z₂ = normIdeal Q L := hz₂n.trans hnK₁
  have hng₂ := hng hM₂L hz₂M hz₂nL
  have hz₂0 : Q z₂ ≠ 0 := hng₂.ne_zero Q (IsModular.isRegular Q hM₂U hM₂fg) (Uni93.ne_bot_of_isUnimodular Q hM₂U)
  have hodd₂ : Odd (dord hπ (Q z₂) + dord hπ b) := by
    rw [dord_eq_of_span_eq hπ hz₂0 ha0 (hz₂nL.trans hzn.symm)]; exact hodd
  rcases hyp_or_block Q hK h2p hπ hρ hM₂fg hM₂U hM₂rk hng₂ hb0 (hwL hM₂L) hodd₂ with
    ⟨x, hx, y, hy, h⟩ | ⟨t, x₂, hx₂, y₂, hy₂, hQx₂, hxy₂, ⟨γ₂, hγ₂⟩, -⟩
  · exact ⟨x, hM₂L hx, y, hM₂L hy, h⟩
  -- the two blocks are orthogonal
  have hx₂K := hM₂K hx₂
  have hy₂K := hM₂K hy₂
  have o1 : bil Q x₁ x₂ = 0 := hK₁.orth x₁ (subset_span (by simp)) x₂ hx₂K
  have o2 : bil Q x₂ y₁ = 0 := by rw [bil_comm]; exact hK₁.orth y₁ (subset_span (by simp)) x₂ hx₂K
  have o3 : bil Q x₂ x₁ = 0 := by rw [bil_comm]; exact o1
  have o4 : bil Q x₁ y₂ = 0 := hK₁.orth x₁ (subset_span (by simp)) y₂ hy₂K
  rw [← hb₀] at hQx₁ hQx₂
  rcases le_total t r with h | h
  · exact exists_hyperbolic_of_two_blocks Q h2p hx₁L hy₁L (hM₂L hx₂) hb₀m hQx₁ hxy₁ hγ₁ hQx₂ o1 o2 h
  · exact exists_hyperbolic_of_two_blocks Q h2p (hM₂L hx₂) (hM₂L hy₂) hx₁L hb₀m hQx₂ hxy₂ hγ₂ hQx₁ o3 o4 h

/-- **93:18 (v), splitting form**: a unimodular lattice of rank $\ge 5$ over a dyadic local field is
$L = (\mathfrak ox + \mathfrak oy) \perp K$ with $Q(x) = Q(y) = 0$, $B(x, y) = 1$, i.e.
$L \cong \langle A(0,0)\rangle \perp K$. -/
@[kb "omeara1963" "§93D, 93:18 (v), p. 261 (splitting form)"]
theorem omeara93_18_v_splitting (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V}
    (hfg : L.FG) (hU : IsUnimodular Q L) (hrk : 5 ≤ finrank R L) :
    ∃ x y : V, ∃ K : Submodule R V, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1 ∧ IsOrthSum Q L (span R {x, y}) K := by
  obtain ⟨x, hx, y, hy, h1, h2, h3⟩ := omeara93_18_v Q hK h2p hfg hU hrk
  have hsub : ∀ w ∈ L, w ∈ subA Q 1 L := fun w hw =>
    ⟨hw, fun l hl => hU.2.1 ▸ bil_mem_scale Q hw hl⟩
  obtain ⟨K, hK'⟩ := exists_isOrthSum_span_hyp Q (hsub x hx) (hsub y hy) h1 h2 h3
  exact ⟨x, y, K, h1, h2, h3, hK'⟩

/-- **93:18 (v), "and so $\mathfrak gL = Q(L)$"** (O'Meara 1963, p. 261, via §93A, p. 252): a unimodular lattice of
rank $\ge 5$ over a dyadic local field has $\mathfrak gL = Q(L)$. -/
@[kb "omeara1963" "§93D, 93:18 (v), p. 261 (gL = Q(L))"]
theorem omeara93_18_v_normGroup (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V}
    (hfg : L.FG) (hU : IsUnimodular Q L) (hrk : 5 ≤ finrank R L) :
    (normGroup Q L : Set F) = Q '' (L : Set V) := by
  obtain ⟨x, hx, y, hy, h1, h2, h3⟩ := omeara93_18_v Q hK h2p hfg hU hrk
  exact normGroup_eq_image Q L hU.2.1 hx hy h1 h2 h3

end Main

end QuadFormsKB.OMeara.D18
