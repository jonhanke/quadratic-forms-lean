/-
# O'Meara §82H and §91A: maximal lattices inside a subspace (tools for 91:2)

**Setting** (as in `Sec91.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a quadratic
space $(V, Q)$ over $F$, lattices = `Submodule R V`; $W$ an $F$-subspace of $V$.

**Defines** `IsMaxIn Q a W L`: $L$ is an $\mathfrak a$-maximal lattice on the subspace $W$ (O'Meara 1963, §82H, p. 234,
for the quadratic space $W$): $L$ is finitely generated, $FL = W$, $\mathfrak nL \subseteq \mathfrak a$, and no lattice
$M$ with $L \subseteq M \subseteq W$ and $\mathfrak nM \subseteq \mathfrak a$ is larger.

**Proves**
* `isMaxIn_top_iff`: $\mathfrak a$-maximal on $V$ (`IsMaximal`) is `IsMaxIn` for $W = V$;
* `exists_isMaxVec_smul` (Chapter IX, p. 239): every line $Fx$ in $FL$ contains a maximal vector of $L$;
* `mem_iff_of_isMaxIn` (**91:1** for a subspace): on an anisotropic subspace $W$, an $\mathfrak a$-maximal lattice on
  $W$ is $\{x \in W : Q(x) \in \mathfrak a\}$;
* `exists_hyperbolic_split_of_isMaxIn` (**82:20**, p. 235): an $\mathfrak a$-maximal lattice $L$ on a regular subspace
  containing a non-zero isotropic vector splits as $L = J \perp K$ with $J = \mathfrak ox_0 + \mathfrak oy$,
  $Q(x_0) = Q(y) = 0$, $B(x_0, y) = \gamma$ and $2\gamma\mathfrak o = \mathfrak a$.
-/
import QuadFormsKB.Literature.OMeara.Sec91Chain

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Defs

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **$\mathfrak a$-maximal lattice on a subspace $W$** (O'Meara 1963, §82H, p. 234, applied to the quadratic space
$W$): $L$ is finitely generated with $FL = W$, $\mathfrak nL \subseteq \mathfrak a$, and every finitely generated lattice
$M$ with $L \subseteq M \subseteq W$ and $\mathfrak nM \subseteq \mathfrak a$ equals $L$. -/
def IsMaxIn (a : Submodule R F) (W : Submodule F V) (L : Submodule R V) : Prop :=
  L.FG ∧ span F (L : Set V) = W ∧ normIdeal Q L ≤ a ∧
    ∀ M : Submodule R V, M.FG → L ≤ M → (M : Set V) ⊆ W → normIdeal Q M ≤ a → M = L

end Defs

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- $\mathfrak a$-maximal on $V$ is the same as $\mathfrak a$-maximal on the subspace $W = V$. -/
theorem isMaxIn_top_iff {a : Submodule R F} {L : Submodule R V} : IsMaxIn Q a ⊤ L ↔ IsMaximal Q a L := by
  constructor
  · rintro ⟨hfg, hspan, hn, hmax⟩
    exact ⟨⟨hfg, hspan⟩, hn, fun K hK hLK hnK => hmax K hK.fg hLK (fun _ _ => trivial) hnK⟩
  · rintro ⟨hlat, hn, hmax⟩
    refine ⟨hlat.fg, hlat.span_eq_top, hn, fun M hM hLM _ hnM => hmax M ⟨hM, ?_⟩ hLM hnM⟩
    exact le_antisymm le_top (by rw [← hlat.span_eq_top]; exact span_mono hLM)

/-- **Maximal vectors on a line** (O'Meara 1963, §81D, p. 216; Chapter IX, p. 239: "every line $Fx$ in $FL$ contains a
maximal vector of $L$"): if $u \ne 0$ lies in $FL$, then $u = t y$ with $t \in F^\times$ and $y$ maximal in $L$. -/
@[kb "omeara1963" "Chapter IX, p. 239 (every line Fx in FL contains a maximal vector of L)"]
theorem exists_isMaxVec_smul {L : Submodule R V} (hfg : L.FG) {u : V} (hu : u ≠ 0)
    (huL : u ∈ span F (L : Set V)) : ∃ y : V, IsMaxVec F L y ∧ ∃ t : F, t ≠ 0 ∧ u = t • y := by
  classical
  let f : F →ₗ[R] V := (LinearMap.toSpanSingleton F V u).restrictScalars R
  have hf : ∀ c, f c = c • u := fun c => rfl
  have hfinj : Function.Injective f := fun c d h => smul_left_injective F hu h
  let I : Submodule R F := L.comap f
  have hIfg : I.FG :=
    Submodule.fg_of_fg_map_injective f hfinj (FG.of_le hfg (Submodule.map_comap_le f L))
  have hIne : I ≠ ⊥ := by
    obtain ⟨d, hd0, hd⟩ := exists_smul_mem_of_mem_span (S := L) huL
    intro h
    have : algebraMap R F d ∈ I := by
      show f (algebraMap R F d) ∈ L
      rw [hf, algebraMap_smul]; exact hd
    rw [h, mem_bot] at this
    exact hd0 (IsFractionRing.injective R F (this.trans (map_zero _).symm))
  obtain ⟨γ, hγ0, hIγ⟩ := exists_eq_span_singleton hIfg hIne
  have hmem : ∀ c : F, c • u ∈ L ↔ c ∈ R ∙ γ := fun c => by
    rw [← hIγ]; exact Iff.rfl
  refine ⟨γ • u, ⟨(hmem γ).mpr (mem_span_singleton_self γ), fun c hc => ?_⟩, γ⁻¹, inv_ne_zero hγ0,
    by rw [smul_smul, inv_mul_cancel₀ hγ0, one_smul]⟩
  rw [smul_smul] at hc
  obtain ⟨r, hr⟩ := mem_span_singleton.mp ((hmem _).mp hc)
  refine ⟨r, ?_⟩
  rw [Algebra.smul_def] at hr
  exact mul_right_cancel₀ hγ0 hr

/-- Step 1 of 91:1 on an anisotropic subspace $W$: $\{x \in W : Q(x) \in \mathfrak a\}$ is closed under addition
(a copy of `Q_add_mem_of_anisotropic`, anisotropy being used only for vectors of $W$). -/
theorem Q_add_mem_of_aniso_on [HenselianLocalRing R] {W : Submodule F V} (hW : ∀ w ∈ W, Q w = 0 → w = 0)
    {a : Submodule R F} {x y : V} (hxW : x ∈ W) (hyW : y ∈ W) (hx : Q x ∈ a) (hy : Q y ∈ a) :
    Q (x + y) ∈ a := by
  by_contra h
  set b := bil Q x y with hb
  have hc : 2 * b ∉ a := by
    intro hc
    apply h
    rw [Q_add]
    exact add_mem (add_mem hx hc) hy
  obtain ⟨m₁, hm₁, h₁⟩ := exists_maximalIdeal_mul_of_mem_of_notMem hx hc
  obtain ⟨m₂, hm₂, h₂⟩ := exists_maximalIdeal_mul_of_mem_of_notMem hy hc
  have hb0 : b ≠ 0 := by rintro hb0; apply hc; rw [hb0, mul_zero]; exact a.zero_mem
  obtain ⟨s', hs'⟩ := isSquare_one_add_four_mul (R := R) (neg_mem (Ideal.mul_mem_left _ m₁ hm₂))
  set s := b * algebraMap R F s' with hs
  have hss : s ^ 2 = b ^ 2 - Q x * Q y := by
    have := congrArg (algebraMap R F) hs'
    simp only [map_add, map_one, map_mul, map_neg, map_ofNat] at this
    rw [hs, h₁, h₂, mul_pow, _root_.sq (algebraMap R F s'), ← this]
    ring
  have hs0 : s ≠ 0 := by
    rw [hs]
    refine mul_ne_zero hb0 fun h0 => ?_
    have : (1 : R) + 4 * -(m₁ * m₂) = 0 := by
      rw [hs', (IsFractionRing.injective R F) (h0.trans (map_zero _).symm), mul_zero]
    have hu : IsUnit ((1 : R) + 4 * -(m₁ * m₂)) := by
      have : 4 * -(m₁ * m₂) ∈ maximalIdeal R :=
        Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_left _ m₁ hm₂))
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem this)
      rwa [sub_neg_eq_add] at this
    exact hu.ne_zero this
  by_cases hQx : Q x = 0
  · have hx0 : x = 0 := hW x hxW hQx
    apply h; rw [hx0, zero_add]; exact hy
  · set t := (s - b) / Q x with ht
    have hQt : Q (t • x + y) = 0 := by
      rw [Q_add, Q_smul, bil_smul_left, ← hb, ht]
      field_simp
      linear_combination hss
    have hdep : t • x + y = 0 := hW _ (W.add_mem (W.smul_mem t hxW) hyW) hQt
    have hy' : y = -t • x := by rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hdep
    apply hs0
    have hB : b = -t * Q x := by rw [hb, hy', bil_smul_right, bil_self]
    have hQy : Q y = t ^ 2 * Q x := by rw [hy', Q_smul]; ring
    have : s ^ 2 = 0 := by rw [hss, hB, hQy]; ring
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this

/-- The set $\{x \in W : Q(x) \in \mathfrak a\}$ as an $R$-submodule, for an anisotropic subspace $W$. -/
def subOn [HenselianLocalRing R] {W : Submodule F V} (hW : ∀ w ∈ W, Q w = 0 → w = 0)
    (a : Submodule R F) : Submodule R V where
  carrier := {x | x ∈ W ∧ Q x ∈ a}
  add_mem' := by
    rintro x y ⟨hxW, hx⟩ ⟨hyW, hy⟩
    exact ⟨W.add_mem hxW hyW, Q_add_mem_of_aniso_on Q hW hxW hyW hx hy⟩
  zero_mem' := ⟨W.zero_mem, by simp⟩
  smul_mem' := by
    rintro c x ⟨hxW, hx⟩
    refine ⟨by rw [← algebraMap_smul F c x]; exact W.smul_mem _ hxW, ?_⟩
    show Q (c • x) ∈ a
    rw [Q_rsmul, _root_.sq, mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
    exact a.smul_mem _ (a.smul_mem _ hx)

/-- **Theorem 91:1 for a subspace** (O'Meara 1963, p. 239, applied to the quadratic space $W$): if $W$ is anisotropic
and $L$ is $\mathfrak a$-maximal on $W$, then $L = \{x \in W : Q(x) \in \mathfrak a\}$. -/
theorem mem_iff_of_isMaxIn [HenselianLocalRing R] {a : Submodule R F} {W : Submodule F V} {L : Submodule R V}
    (hW : ∀ w ∈ W, Q w = 0 → w = 0) (hL : IsMaxIn Q a W L) {x : V} (hx : x ∈ W) : x ∈ L ↔ Q x ∈ a := by
  obtain ⟨hfg, hspan, hn, hmax⟩ := hL
  have hLW : ∀ z ∈ L, z ∈ W := fun z hz => by rw [← hspan]; exact subset_span hz
  refine ⟨fun hx' => hn (Q_mem_normIdeal Q hx'), fun hxa => ?_⟩
  by_contra hxL
  have hKle : L ⊔ (R ∙ x) ≤ subOn Q hW a := by
    refine sup_le (fun y hy => ⟨hLW y hy, hn (Q_mem_normIdeal Q hy)⟩) ?_
    rw [span_singleton_le_iff_mem]; exact ⟨hx, hxa⟩
  have := hmax (L ⊔ R ∙ x) (hfg.sup (fg_span_singleton x)) le_sup_left (fun z hz => (hKle hz).1) (by
    rw [normIdeal, span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact (hKle hy).2)
  exact hxL (this ▸ (le_sup_right : (R ∙ x) ≤ L ⊔ R ∙ x) (mem_span_singleton_self x))

/-- The complement of a regular component is $\{x \in L : B(x, J) = 0\}$ (a copy of `IsOrthSum.eq_splitComp`,
which lives in a file not imported here). -/
theorem isOrthSum_eq_splitComp_aux {L J K : Submodule R V} (h : IsOrthSum Q L J K) (hJ : IsRegular Q J) :
    K = splitComp Q L J := by
  apply le_antisymm
  · intro k hk
    exact ⟨h.sup_eq ▸ mem_sup_right hk, fun j hj => by rw [bil_comm]; exact h.orth j hj k hk⟩
  · rintro w ⟨hwL, hwJ⟩
    rw [← h.sup_eq] at hwL
    obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.mp hwL
    have hj0 : j = 0 := hJ j hj fun j' hj' => by
      have := hwJ j' hj'
      rw [bil_add_left, bil_comm Q k j', h.orth j' hj' k hk, add_zero] at this
      exact this
    rw [hj0, zero_add]; exact hk

/-- **Proposition 82:20** (O'Meara 1963, p. 235), for a lattice $L$ that is $\mathfrak a$-maximal on a regular subspace
$W$: if $L$ contains a non-zero isotropic vector, then $L = J \perp K$ with $J = \mathfrak ox_0 + \mathfrak oy$,
$Q(x_0) = Q(y) = 0$, $B(x_0, y) = \gamma$ and $\mathfrak a = 2\gamma\mathfrak o$ ($J$ is $\tfrac12\mathfrak a$-modular, a
hyperbolic plane; 82:21). -/
@[kb "omeara1963" "§82H, 82:20, p. 235 (and 82:21)"]
theorem exists_hyperbolic_split_of_isMaxIn {a : Submodule R F} {W : Submodule F V} {L : Submodule R V}
    (hWreg : ∀ w ∈ W, (∀ w' ∈ W, bil Q w w' = 0) → w = 0) (hL : IsMaxIn Q a W L) {x : V} (hx : x ∈ L)
    (hx0 : x ≠ 0) (hQx : Q x = 0) :
    ∃ x₀ ∈ L, ∃ y ∈ L, ∃ γ : F, γ ≠ 0 ∧ a = R ∙ (2 * γ) ∧ Q x₀ = 0 ∧ Q y = 0 ∧ bil Q x₀ y = γ ∧
      IsOrthSum Q L (span R {x₀, y}) (splitComp Q L (span R {x₀, y})) := by
  obtain ⟨hfg, hspan, hn, hmax⟩ := hL
  have hLW : ∀ z ∈ L, z ∈ W := fun z hz => by rw [← hspan]; exact subset_span hz
  -- (i) `L` is regular
  have hLreg : IsRegular Q L := by
    intro z hz hz0
    refine hWreg z (hLW z hz) fun w hw => ?_
    rw [← hspan] at hw
    exact span_induction (p := fun w _ => bil Q z w = 0) (fun w hw => hz0 w hw) (by simp [bil])
      (fun a b _ _ ha hb => by rw [bil_add_right, ha, hb, add_zero])
      (fun c a _ ha => by rw [bil_smul_right, ha, mul_zero]) hw
  -- (ii) `2 sL ⊆ a`
  have h2s : ∀ c ∈ scale Q L, 2 * c ∈ a := fun c hc => hn (two_mul_mem_normIdeal Q hc)
  -- (iii) a maximal isotropic vector
  obtain ⟨x₀, hx₀max, t, ht, hxt⟩ := exists_isMaxVec_smul (F := F) hfg hx0 (subset_span hx)
  have hx₀L : x₀ ∈ L := hx₀max.1
  have hx₀0 : x₀ ≠ 0 := by rintro rfl; apply hx0; rw [hxt, smul_zero]
  have hQx₀ : Q x₀ = 0 := by
    rw [hxt, Q_smul] at hQx
    exact (mul_eq_zero.mp hQx).resolve_left (pow_ne_zero 2 ht)
  -- (iv) the ideal `B(x₀, L)`
  let g : V →ₗ[R] F := (QuadraticMap.associated Q x₀ : V →ₗ[F] F).restrictScalars R
  have hg : ∀ v, g v = bil Q x₀ v := fun v => rfl
  obtain ⟨S, hS⟩ : ∃ S : Submodule R F, S = L.map g := ⟨_, rfl⟩
  have hSfg : S.FG := hS ▸ hfg.map g
  have hSmem : ∀ l ∈ L, bil Q x₀ l ∈ S := fun l hl => by
    rw [hS]; exact Submodule.mem_map.mpr ⟨l, hl, hg l⟩
  have hSne : S ≠ ⊥ := by
    intro h
    apply hx₀0
    refine hLreg x₀ hx₀L fun l hl => ?_
    have := hSmem l hl
    rw [h, mem_bot] at this; exact this
  obtain ⟨γ, hγ0, hSγ⟩ := exists_eq_span_singleton hSfg hSne
  have hBγ : ∀ l ∈ L, bil Q x₀ l ∈ R ∙ γ := fun l hl => hSγ ▸ hSmem l hl
  obtain ⟨y₀, hy₀L, hy₀⟩ : ∃ y₀ ∈ L, bil Q x₀ y₀ = γ := by
    have : γ ∈ S := hSγ ▸ mem_span_singleton_self γ
    rw [hS] at this
    obtain ⟨y₀, hy₀, h⟩ := Submodule.mem_map.mp this
    exact ⟨y₀, hy₀, by rw [← hg]; exact h⟩
  have hA : ∀ δ : F, 2 * δ ∈ a → δ ∈ R ∙ γ := by
    intro δ hδ
    by_contra hδγ
    obtain ⟨τ, hτ⟩ : ∃ τ : F, τ = δ / γ := ⟨_, rfl⟩
    have hτx : τ • x₀ ∉ L := by
      intro h
      obtain ⟨r, hr⟩ := hx₀max.2 τ h
      apply hδγ
      refine mem_span_singleton.mpr ⟨r, ?_⟩
      rw [Algebra.smul_def, hr, hτ]; field_simp
    have hMsub : ∀ l ∈ L, ∀ r : R, Q (l + r • (τ • x₀)) ∈ a := by
      intro l hl r
      obtain ⟨s, hs⟩ := mem_span_singleton.mp (hBγ l hl)
      have e : Q (l + r • (τ • x₀)) = Q l + (r * s) • (2 * δ) := by
        rw [Q_add, Q_rsmul, Q_smul, hQx₀, bil_rsmul_right, bil_smul_right, bil_comm Q l x₀, ← hs, hτ]
        simp only [Algebra.smul_def, map_mul]
        field_simp
        ring
      rw [e]; exact add_mem (hn (Q_mem_normIdeal Q hl)) (a.smul_mem _ hδ)
    have hMfg : (L ⊔ R ∙ (τ • x₀)).FG := hfg.sup (fg_span_singleton _)
    have hMW : ((L ⊔ R ∙ (τ • x₀) : Submodule R V) : Set V) ⊆ W := by
      intro z hz
      obtain ⟨l, hl, w, hw, rfl⟩ := mem_sup.mp hz
      obtain ⟨r, rfl⟩ := mem_span_singleton.mp hw
      refine W.add_mem (hLW l hl) ?_
      rw [← algebraMap_smul F r]
      exact W.smul_mem _ (W.smul_mem _ (hLW _ hx₀L))
    have hMn : normIdeal Q (L ⊔ R ∙ (τ • x₀)) ≤ a := by
      rw [normIdeal, span_le]
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨l, hl, w, hw, rfl⟩ := mem_sup.mp hz
      obtain ⟨r, rfl⟩ := mem_span_singleton.mp hw
      exact hMsub l hl r
    have hM := hmax _ hMfg le_sup_left hMW hMn
    apply hτx
    rw [← hM]
    exact (le_sup_right : (R ∙ (τ • x₀)) ≤ L ⊔ R ∙ (τ • x₀)) (mem_span_singleton_self _)
  have hγs : γ ∈ scale Q L := by rw [← hy₀]; exact bil_mem_scale Q hx₀L hy₀L
  have haeq : a = R ∙ (2 * γ) := by
    apply le_antisymm
    · intro c hc
      have h2 : (2 : F) * (c / 2) = c := by field_simp
      obtain ⟨r, hr⟩ := mem_span_singleton.mp (hA (c / 2) (by rw [h2]; exact hc))
      refine mem_span_singleton.mpr ⟨r, ?_⟩
      rw [Algebra.smul_def] at hr ⊢
      linear_combination 2 * hr + h2
    · rw [span_singleton_le_iff_mem]; exact h2s γ hγs
  have hsc : ∀ c ∈ scale Q L, c ∈ R ∙ γ := fun c hc => hA c (h2s c hc)
  -- (v) the second hyperbolic vector
  obtain ⟨r, hr⟩ := mem_span_singleton.mp (haeq ▸ hn (Q_mem_normIdeal Q hy₀L) : Q y₀ ∈ R ∙ (2 * γ))
  obtain ⟨y, hyL, hQy, hxy⟩ : ∃ y ∈ L, Q y = 0 ∧ bil Q x₀ y = γ := by
    refine ⟨y₀ + (-r) • x₀, L.add_mem hy₀L (L.smul_mem _ hx₀L), ?_, ?_⟩
    · rw [Q_add, Q_rsmul, bil_rsmul_right, bil_comm Q y₀ x₀, hy₀, hQx₀, ← hr, Algebra.smul_def, map_neg]
      ring
    · rw [bil_add_right, bil_rsmul_right, bil_self, hQx₀, hy₀]; simp
  refine ⟨x₀, hx₀L, y, hyL, γ, hγ0, haeq, hQx₀, hQy, hxy, ?_⟩
  -- (vi) the splitting
  let v : Fin 2 → V := ![x₀, y]
  let U : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]
  have hG : gram Q v = γ • U.map (algebraMap R F) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [v, U, gram, hQx₀, hQy, hxy, bil_comm Q y x₀]
  have hU : IsUnit U.det := by simp [U, Matrix.det_fin_two_of]
  obtain ⟨hmod, -⟩ := isModular_span_of_gram Q hγ0 hU hG
  have hv : Set.range v = {x₀, y} := by ext w; simp [v, eq_comm, or_comm]
  rw [hv] at hmod
  have hJL : span R {x₀, y} ≤ L := by
    rw [span_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with h | h <;> rw [h]
    · exact hx₀L
    · exact hyL
  have hJfg : (span R {x₀, y}).FG := fg_span (Set.toFinite _)
  obtain ⟨K, hK⟩ := (splits_iff_of_isModular Q hJL hmod hJfg).mpr
    (fun w hw l hl => hsc _ (bil_mem_scale Q (hJL hw) hl))
  rwa [isOrthSum_eq_splitComp_aux Q hK (hmod.isRegular Q hJfg)] at hK

end DVR

end QuadFormsKB.OMeara
