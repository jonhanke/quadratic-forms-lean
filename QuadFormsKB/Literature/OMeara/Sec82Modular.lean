/-
# O'Meara §82G: remarks on modular lattices over a Dedekind domain

**Setting.** $R$ is a Dedekind domain with fraction field $F$, $2 \in F^\times$, and $(V, Q)$ a finite-dimensional
quadratic space over $F$ with O'Meara's bilinear form $B$ = `bil Q`; $\mathfrak a$-modular lattices are `IsModular`
(`Sec82.lean`: $\mathfrak sL = \mathfrak a$ and $\mathfrak vL = \mathfrak a^r$, $r$ the rank).

**Proves** (O'Meara 1963, §82G, p. 231):
* `IsModular.ideal_smul` ($\mathfrak bL$ is $\mathfrak b^2\mathfrak a$-modular; in particular $\alpha L$ is
  $\alpha^2\mathfrak a$-modular);
* `Dedekind.isModular_iff_of_isOrthSum` (a non-trivial splitting $L = J \perp K$ is $\mathfrak a$-modular if and only if
  $J$ and $K$ are);
* `isModular_span_singleton` ($\mathfrak ox$ is $Q(x)$-modular for an anisotropic $x$).
-/
import QuadFormsKB.Literature.OMeara.Sec82Volume

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- A product of a finitely generated non-zero submodule of $F$ with a non-zero one is non-zero. -/
theorem mul_ne_bot_of_fg {p q : Submodule R F} (hp : p.FG) (hp0 : p ≠ ⊥) (hq : q ≠ ⊥) : p * q ≠ ⊥ := by
  intro h
  apply hq
  have h1 := mul_one_div_cancel_of_fg hp hp0
  calc q = (p * (1 / p)) * q := by rw [h1, one_mul]
    _ = (1 / p) * (p * q) := by ring
    _ = ⊥ := by rw [h]; exact Submodule.mul_bot _

/-- Powers of a finitely generated non-zero submodule of $F$ are finitely generated and non-zero. -/
theorem pow_fg_ne_bot {p : Submodule R F} (hp : p.FG) (hp0 : p ≠ ⊥) (n : ℕ) : (p ^ n).FG ∧ p ^ n ≠ ⊥ := by
  induction n with
  | zero => simp [Submodule.one_eq_span, Submodule.fg_span_singleton]
  | succ n ih =>
    rw [pow_succ]
    exact ⟨ih.1.mul hp, mul_ne_bot_of_fg ih.1 ih.2 hp0⟩

/-- If $s \subseteq a$ and $a^n \subseteq s^n$ with $n \ge 1$ then $s = a$ (for $a$ finitely generated, non-zero). -/
theorem eq_of_le_of_pow_le {s a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) (hs : s ≤ a) {n : ℕ}
    (hn : 1 ≤ n) (h : a ^ n ≤ s ^ n) : s = a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨hmfg, hm0⟩ := pow_fg_ne_bot ha ha0 m
  have h1 : a ^ m * a ≤ a ^ m * s := by
    calc a ^ m * a = a ^ (m + 1) := (pow_succ a m).symm
      _ ≤ s ^ (m + 1) := h
      _ = s * s ^ m := pow_succ' s m
      _ ≤ s * a ^ m := mul_le_mul' le_rfl (pow_le_pow_left' hs m)
      _ = a ^ m * s := mul_comm _ _
  have h2 : a ^ m * s ≤ a ^ m * a := mul_le_mul' le_rfl hs
  exact mul_left_cancel_of_fg hmfg hm0 (le_antisymm h2 h1)

/-- If $p \subseteq P$, $q \subseteq Q'$ and $pq = PQ'$ (with $P, Q'$ finitely generated non-zero) then $p = P$
and $q = Q'$. -/
theorem eq_of_le_of_mul_eq {p P q Q' : Submodule R F} (hP : P.FG) (hP0 : P ≠ ⊥) (hQ : Q'.FG) (hQ0 : Q' ≠ ⊥)
    (hp : p ≤ P) (hq : q ≤ Q') (h : p * q = P * Q') : p = P ∧ q = Q' := by
  constructor
  · refine mul_left_cancel_of_fg hQ hQ0 (le_antisymm (mul_le_mul' le_rfl hp) ?_)
    calc Q' * P = p * q := by rw [h, mul_comm]
      _ ≤ p * Q' := mul_le_mul' le_rfl hq
      _ = Q' * p := mul_comm _ _
  · refine mul_left_cancel_of_fg hP hP0 (le_antisymm (mul_le_mul' le_rfl hq) ?_)
    calc P * Q' = p * q := h.symm
      _ ≤ P * q := mul_le_mul' hp le_rfl

/-- The $F$-spans of disjoint lattices are disjoint. -/
theorem disjoint_span_of_disjoint {J K : Submodule R V} (h : Disjoint J K) :
    Disjoint (span F (J : Set V)) (span F (K : Set V)) := by
  have htf := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  rw [disjoint_iff, eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  obtain ⟨d, hd, hdz⟩ := exists_smul_mem_of_mem_span (F := F) hz1
  obtain ⟨d', hd', hdz'⟩ := exists_smul_mem_of_mem_span (F := F) hz2
  have h1 : d' • d • z ∈ J := J.smul_mem d' hdz
  have h2 : d' • d • z ∈ K := by rw [smul_comm]; exact K.smul_mem d hdz'
  have h3 : d' • d • z = 0 := (Submodule.disjoint_def.1 h) _ h1 h2
  have h4 := (smul_eq_zero.1 h3).resolve_left hd'
  exact (mem_bot F).2 ((smul_eq_zero.1 h4).resolve_left hd)

include F in
/-- The rank of a disjoint sum of lattices is the sum of the ranks (Dedekind version). -/
theorem finrank_sup_of_disjoint' {J K : Submodule R V} (h : Disjoint J K) :
    finrank R (J ⊔ K : Submodule R V) = finrank R J + finrank R K := by
  have hspan : span F ((J ⊔ K : Submodule R V) : Set V) = span F (J : Set V) ⊔ span F (K : Set V) := by
    apply le_antisymm
    · rw [span_le]
      intro v hv
      obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hv
      exact add_mem (mem_sup_left (subset_span hj)) (mem_sup_right (subset_span hk))
    · exact sup_le (span_mono (SetLike.coe_subset_coe.2 le_sup_left))
        (span_mono (SetLike.coe_subset_coe.2 le_sup_right))
  rw [finrank_eq_finrank_span (F := F) (J ⊔ K), hspan, finrank_eq_finrank_span (F := F) J,
    finrank_eq_finrank_span (F := F) K]
  have := Submodule.finrank_sup_add_finrank_inf_eq (span F (J : Set V)) (span F (K : Set V))
  rw [disjoint_iff.1 (disjoint_span_of_disjoint (F := F) h)] at this
  simpa using this

include F in
/-- A non-zero lattice has rank at least $1$. -/
theorem one_le_finrank_of_ne_bot {J : Submodule R V} (hJ : J ≠ ⊥) : 1 ≤ finrank R J := by
  rw [finrank_eq_finrank_span (F := F) J]
  refine Submodule.one_le_finrank_iff.2 fun h => hJ (eq_bot_iff.2 fun x hx => ?_)
  have := subset_span (R := F) hx
  rw [h] at this
  simpa using this

/-- A lattice with scale in $\mathfrak a$ and volume $\mathfrak a^r$ is $\mathfrak a$-modular. -/
theorem isModular_of_volume_eq {a : Submodule R F} {M : Submodule R V} (ha : a.FG) (ha0 : a ≠ ⊥)
    (hM0 : M ≠ ⊥) (hs : scale Q M ≤ a) (hv : volume Q M = a ^ finrank R M) : IsModular Q a M := by
  refine ⟨ha0, ?_, hv⟩
  have hv' := volume_le_scale_pow Q M
  rw [hv] at hv'
  exact eq_of_le_of_pow_le ha ha0 hs (one_le_finrank_of_ne_bot (F := F) hM0) hv'

/-- **Scaling a modular lattice** (O'Meara 1963, §82G, p. 231): if $L$ is $\mathfrak a$-modular then $\mathfrak bL$ is
$\mathfrak b^2\mathfrak a$-modular for every fractional ideal $\mathfrak b$ (and $\alpha L$ is
$\alpha^2\mathfrak a$-modular: $\mathfrak b = \alpha\mathfrak o$). -/
@[kb "omeara1963" "§82G, p. 231 (bL is b²a-modular)"]
theorem IsModular.ideal_smul {a : Submodule R F} {L : Submodule R V} (hL : IsModular Q a L) (hLfg : L.FG)
    {b : Submodule R F} (hb : b.FG) (hb0 : b ≠ ⊥) : IsModular Q (b ^ 2 * a) (b • L) := by
  classical
  obtain ⟨hb0a, hs, hv⟩ := hL
  obtain ⟨r, y, hy, -, c, hc, hLeq⟩ := exists_adapted (F := F) hLfg
  have hbc : ∀ i, (b * c i).FG ∧ b * c i ≠ ⊥ := fun i =>
    ⟨hb.mul (hc i).1, mul_ne_bot_of_fg hb hb0 (hc i).2⟩
  have hbL : b • L = ⨆ i, (b * c i) • span R {y i} := by
    rw [hLeq, Submodule.smul_iSup]
    exact iSup_congr fun i => (Submodule.smul_assoc b (c i) (span R {y i})).symm
  have hrk : finrank R L = r := by
    have := finrank_adapted c (fun i => (hc i).2) y hy
    rw [← hLeq] at this
    simpa using this
  have hrk' : finrank R (b • L : Submodule R V) = r := by
    have := finrank_adapted (fun i => b * c i) (fun i => (hbc i).2) y hy
    rw [← hbL] at this
    simpa using this
  have hvol := volume_eq_of_adapted Q y hy c hc
  rw [← hLeq] at hvol
  have hvol' := volume_eq_of_adapted Q y hy (fun i => b * c i) hbc
  rw [← hbL] at hvol'
  rw [hvol, hrk] at hv
  refine ⟨?_, ?_, ?_⟩
  · exact mul_ne_bot_of_fg (hb.pow 2) (by rw [pow_two]; exact mul_ne_bot_of_fg hb hb0 hb0) hb0a
  · rw [scale_smul, hs]
  · rw [hrk', hvol', Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc (b ^ r * ∏ i, c i) ^ 2 * span R {(gram Q y).det}
        = (b ^ r) ^ 2 * ((∏ i, c i) ^ 2 * span R {(gram Q y).det}) := by ring
      _ = (b ^ r) ^ 2 * a ^ r := by rw [hv]
      _ = (b ^ 2 * a) ^ r := by ring

/-- **Modular splittings** (O'Meara 1963, §82G, p. 231): for a non-trivial splitting $L = J \perp K$, $L$ is
$\mathfrak a$-modular if and only if both $J$ and $K$ are. -/
@[kb "omeara1963" "§82G, p. 231 (J ⊥ K is a-modular iff J and K are)"]
theorem Dedekind.isModular_iff_of_isOrthSum {a : Submodule R F} {L J K : Submodule R V} (h : IsOrthSum Q L J K)
    (hJ : J.FG) (hK : K.FG) (hJ0 : J ≠ ⊥) (hK0 : K ≠ ⊥) :
    IsModular Q a L ↔ IsModular Q a J ∧ IsModular Q a K := by
  classical
  have hLfg : L.FG := h.sup_eq ▸ hJ.sup hK
  have hrank : finrank R L = finrank R J + finrank R K := by
    rw [← h.sup_eq]; exact finrank_sup_of_disjoint' (F := F) h.disjoint
  have hvol : volume Q L = volume Q J * volume Q K := Dedekind.volume_eq_mul_of_isOrthSum Q h hJ hK
  have hscale : scale Q L = scale Q J ⊔ scale Q K := by
    rw [← h.sup_eq]; exact scale_sup_of_orth Q h.orth
  constructor
  · rintro ⟨ha0, hs, hv⟩
    have haFG : a.FG := hs ▸ scale_fg Q hLfg
    have hJs : scale Q J ≤ a := hs ▸ scale_mono Q (le_sup_left.trans h.sup_eq.le)
    have hKs : scale Q K ≤ a := hs ▸ scale_mono Q (le_sup_right.trans h.sup_eq.le)
    have hpJ : volume Q J ≤ a ^ finrank R J :=
      (volume_le_scale_pow Q J).trans (pow_le_pow_left' hJs _)
    have hpK : volume Q K ≤ a ^ finrank R K :=
      (volume_le_scale_pow Q K).trans (pow_le_pow_left' hKs _)
    have hprod : volume Q J * volume Q K = a ^ finrank R J * a ^ finrank R K := by
      rw [← hvol, hv, hrank, pow_add]
    obtain ⟨hPf, hP0⟩ := pow_fg_ne_bot haFG ha0 (finrank R J)
    obtain ⟨hQf, hQ0⟩ := pow_fg_ne_bot haFG ha0 (finrank R K)
    obtain ⟨hvJ, hvK⟩ := eq_of_le_of_mul_eq hPf hP0 hQf hQ0 hpJ hpK hprod
    exact ⟨isModular_of_volume_eq Q haFG ha0 hJ0 hJs hvJ, isModular_of_volume_eq Q haFG ha0 hK0 hKs hvK⟩
  · rintro ⟨⟨ha0, hsJ, hvJ⟩, ⟨-, hsK, hvK⟩⟩
    refine ⟨ha0, ?_, ?_⟩
    · rw [hscale, hsJ, hsK, sup_idem]
    · rw [hvol, hvJ, hvK, hrank, pow_add]

/-- **$\mathfrak ox$ is $Q(x)$-modular** (O'Meara 1963, §82G, p. 231) for an anisotropic vector $x$. -/
@[kb "omeara1963" "§82G, p. 231 (ox is Q(x)-modular)"]
theorem isModular_span_singleton {x : V} (hx : Q x ≠ 0) :
    IsModular Q (span R {Q x}) (span R {x}) := by
  have htf := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  have hx0 : x ≠ 0 := fun h => hx (by simp [h])
  have hli : LinearIndependent R (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx0
  let b := Basis.span hli
  have hset : Set.range (fun _ : Fin 1 => x) = {x} := Set.range_const
  have hr : finrank R (span R (Set.range (fun _ : Fin 1 => x))) = 1 := by
    rw [finrank_eq_card_basis b]; simp
  rw [← hset]
  refine ⟨fun h => hx (span_singleton_eq_bot.1 h), ?_, ?_⟩
  · rw [scale_span Q (fun _ : Fin 1 => x)]
    have : Set.range (fun p : Fin 1 × Fin 1 => bil Q x x) = {Q x} := by
      rw [Set.range_const]; simp
    rw [this]
  · rw [volume_eq_span_det Q b, hr, pow_one]
    congr 2
    have : (gram Q fun i => (b i : V)) = Matrix.of fun _ _ => Q x := by
      ext i j; simp [gram, b]
    rw [this, Matrix.det_unique]
    simp

end QuadFormsKB.OMeara
