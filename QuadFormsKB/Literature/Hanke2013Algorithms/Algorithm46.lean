/-
# Hanke 2013, Algorithm 4.6: a maximal $\mathfrak a$-valued quadratic lattice when $2$ is unramified

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), Algorithm 4.6, pp. 16–17.

**Setting.** $R$ is a Dedekind domain with fraction field $F$ ($R = \mathcal O_F$ for a number field $F$), all of whose
quotients $R/I$ by non-zero ideals are finite (`hR`), $2\in F^\times$, $(V, Q)$ a non-degenerate quadratic space over
$F$ and $H(x, y) = Q(x+y) - Q(x) - Q(y)$ its Hessian bilinear form (`QuadraticMap.polar Q`). The Hessian bilinear
space $(V, H)$ is the bilinear space of the quadratic form $2Q$ (`bil_two_smul`), so the bilinear notions of §2–§3
for $(V, H)$ are those of this library for `(2 : F) • Q`. $\mathfrak a$ is a non-zero fractional ideal.
"$2$ is unramified" is $2\notin\mathfrak p^2$ for every maximal ideal $\mathfrak p$ (`h22`).

**Local notions, globally.** The paper's proof uses localizations ("$(L')_{\mathfrak q} = L_{\mathfrak q}$ for
$\mathfrak q\ne\mathfrak p$", "maximal $\mathfrak a$-even at $\mathfrak p$"). Here they are expressed with global lattices:
* $L_1$, $L_2$ *agree at $\mathfrak q$* (`AgreeAt`) if $sL_1\subseteq L_2$ and $sL_2\subseteq L_1$ for some
  $s\in R\setminus\mathfrak q$ (for lattices this is $(L_1)_{\mathfrak q} = (L_2)_{\mathfrak q}$);
* $L$ is *$\mathfrak a$-maximal at $\mathfrak q$* (`IsHMaximalAt`) if it is $\mathfrak a$-valued for $H$ and no
  $\mathfrak a$-valued $N\supsetneq L$ has $\mathfrak q^kN\subseteq L$ (i.e. $N_{\mathfrak q'} = L_{\mathfrak q'}$ for
  $\mathfrak q'\ne\mathfrak q$);
* $L$ is *maximal $\mathfrak a$-even at $\mathfrak q$* (`IsMaxEvenAt`): the same among lattices that are also
  $\mathfrak a$-even at $\mathfrak q$.

**Neighbours.** Step 2 of the algorithm looks for $\mathfrak p$-neighbours of $L$, but there $L$ is not $\mathfrak a$-even at
$\mathfrak p$, so it is not an $\mathfrak a$-valued *quadratic* lattice and Definition 5.1 / Theorem 5.6 (stated for
those) do not apply literally (*Update*). We use Definition 5.1 (with the
correction recorded for it: $\mathfrak pL\subseteq L'$, $\mathfrak pL'\subseteq L$) for lattices that are
$\mathfrak a$-valued for $H$ (`IsHPNeighbor`).

**Main results.**
* `step_index` (the core of the paper's proof): for $L$ $\mathfrak a$-maximal at $\mathfrak p$ and not $\mathfrak a$-even
  at $\mathfrak p$, $M := L^{\mathfrak a\text{-even at }\mathfrak p}$, every $\mathfrak a$-valued $N\supseteq M$ with
  $\mathfrak p^kN\subseteq M$ is $M$ or has $[N : M] = N(\mathfrak p)$ and is $\mathfrak a$-maximal at $\mathfrak p$. The proof is
  the paper's (Lemmas 2.13, 3.17 and 4.5), applied to a maximal lattice $T\supseteq L$.
* `step_neighbor`, `step_no_neighbor`: the two cases of step 2.
* `algorithm46` (the algorithm as a Lean definition: step 2 over a list of primes) and its correctness
  `algorithm_4_6`: the output is a maximal $\mathfrak a$-valued quadratic lattice (`OMeara.IsMaximal`).
-/
import QuadFormsKB.Literature.Hanke2013Algorithms.EvenIndex
import QuadFormsKB.Literature.Hanke2013Algorithms.Uniqueness
import QuadFormsKB.Citation

open QuadraticMap Submodule

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.OMeara

/-! ### Primary elements and indices (general modules) -/

section General

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- If $M\subsetneq N$ and $\mathfrak q^kN\subseteq M$, some $z\in N\setminus M$ has $\mathfrak qz\subseteq M$. -/
theorem exists_mem_smul_mem {q : Ideal R} {M N : Submodule R V} (hk : ∃ k : ℕ, q ^ k • N ≤ M) (hMN : ¬ N ≤ M) :
    ∃ z ∈ N, z ∉ M ∧ ∀ r ∈ q, r • z ∈ M := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨y, hyN, hyM⟩ := Set.not_subset.1 hMN
  have key : ∀ k : ℕ, ∀ y ∈ N, y ∉ M → (∀ r ∈ q ^ k, r • y ∈ M) → ∃ z ∈ N, z ∉ M ∧ ∀ r ∈ q, r • z ∈ M := by
    intro k
    induction k with
    | zero =>
      intro y _ hyM h
      exact absurd (by simpa using h 1 (by simp)) hyM
    | succ k ih =>
      intro y hyN hyM h
      by_cases hq : ∀ r ∈ q, r • y ∈ M
      · exact ⟨y, hyN, hyM, hq⟩
      · push Not at hq
        obtain ⟨r, hr, hry⟩ := hq
        refine ih (r • y) (N.smul_mem r hyN) hry fun r' hr' => ?_
        rw [smul_smul]
        exact h _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hr' hr)
  exact key k y hyN hyM fun r hr => hk (Submodule.smul_mem_smul hr hyN)

/-- The index $[M + Rz : M] = N(\mathfrak q)$ when $z\notin M$ and $\mathfrak qz\subseteq M$ ($\mathfrak q$ maximal). -/
theorem latIndex_sup_span {q : Ideal R} (hq : q.IsMaximal) {M : Submodule R V} {z : V} (hzM : z ∉ M)
    (hqz : ∀ r ∈ q, r • z ∈ M) : latIndex M (M ⊔ span R {z}) = Nat.card (R ⧸ q) := by
  set K := M ⊔ span R {z}
  have hzK : z ∈ K := Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  set m : SubQuot M K := Submodule.Quotient.mk ⟨z, hzK⟩
  set f := LinearMap.toSpanSingleton R (SubQuot M K) m
  have hsurj : Function.Surjective f := by
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨w, hw⟩ := w
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨r, ?_⟩
      rw [LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      show r • z - (x + r • z) ∈ M
      rw [sub_add_cancel_right]; exact neg_mem hx
  have hker : LinearMap.ker f = q := by
    have hle : q ≤ LinearMap.ker f := fun r hr => by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero]
      exact hqz r hr
    have hne : LinearMap.ker f ≠ ⊤ := fun h => hzM (by
      have : (1 : R) ∈ LinearMap.ker f := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul, Submodule.Quotient.mk_eq_zero] at this
      exact this)
    exact (hq.eq_of_le hne hle).symm
  show Nat.card (SubQuot M K) = _
  rw [← Nat.card_congr (f.quotKerEquivOfSurjective hsurj).toEquiv, hker]

/-- **Indices of $\mathfrak q$-primary extensions.** For $M\subseteq N$ with $\mathfrak q^kN\subseteq M$ ($\mathfrak q$ maximal,
$R/\mathfrak q$ finite) and $[N : M]$ dividing $N(\mathfrak q)$: $[N : M]\in\{1, N(\mathfrak q)\}$, and in the second case
$\mathfrak qN\subseteq M$. -/
theorem latIndex_eq_one_or {q : Ideal R} (hq : q.IsMaximal) [Finite (R ⧸ q)] {M N : Submodule R V} (hMN : M ≤ N)
    (hk : ∃ k : ℕ, q ^ k • N ≤ M) (hdvd : latIndex M N ∣ Nat.card (R ⧸ q)) :
    N = M ∨ (latIndex M N = Nat.card (R ⧸ q) ∧ q • N ≤ M) := by
  by_cases h : N ≤ M
  · exact Or.inl (le_antisymm h hMN)
  · right
    obtain ⟨z, hzN, hzM, hqz⟩ := exists_mem_smul_mem hk h
    set K := M ⊔ span R {z}
    have hKN : K ≤ N := sup_le hMN ((Submodule.span_singleton_le_iff_mem _ _).2 hzN)
    have hMK : M ≤ K := le_sup_left
    have hmul := AddSubgroup.relIndex_mul_relIndex M.toAddSubgroup K.toAddSubgroup N.toAddSubgroup hMK hKN
    have hK := latIndex_sup_span hq hzM hqz
    have hpos : 0 < Nat.card (R ⧸ q) := Nat.card_pos
    have hNM : latIndex M N = Nat.card (R ⧸ q) := by
      apply Nat.dvd_antisymm hdvd
      rw [← hK]; exact ⟨_, hmul.symm⟩
    refine ⟨hNM, ?_⟩
    have hKN1 : K.toAddSubgroup.relIndex N.toAddSubgroup = 1 := by
      have : Nat.card (R ⧸ q) * K.toAddSubgroup.relIndex N.toAddSubgroup = Nat.card (R ⧸ q) * 1 := by
        rw [mul_one]
        calc Nat.card (R ⧸ q) * K.toAddSubgroup.relIndex N.toAddSubgroup
            = latIndex M K * K.toAddSubgroup.relIndex N.toAddSubgroup := by rw [hK]
          _ = Nat.card (R ⧸ q) := hmul.trans hNM
      exact Nat.eq_of_mul_eq_mul_left hpos this
    have hNK : N ≤ K := AddSubgroup.relIndex_eq_one.1 hKN1
    rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨m, hm, y, hy, rfl⟩ := Submodule.mem_sup.1 (hNK hx)
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [smul_add, smul_smul, mul_comm, ← smul_smul]
    exact M.add_mem (M.smul_mem r hm) (M.smul_mem t (hqz r hr))

end General

/-! ### Lattices over a Dedekind domain: primary parts -/

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Primary parts of $K/L$.** For lattices $L\subseteq K$ and a maximal ideal $\mathfrak q$: either $sK\subseteq L$ for some
$s\notin\mathfrak q$ (i.e. $K_{\mathfrak q} = L_{\mathfrak q}$), or some $z\in K\setminus L$ has $\mathfrak qz\subseteq L$. *Proof*: write
the ideal $I = \{r : rK\subseteq L\}\ne0$ as $\mathfrak q^eJ$ with $J\not\subseteq\mathfrak q$; if $I\subseteq\mathfrak q$ then
$N = L + JK$ satisfies $\mathfrak q^eN\subseteq L$, $N\not\subseteq L$, and `exists_mem_smul_mem` applies. -/
theorem exists_smul_le_or {q : Ideal R} (hq : q.IsMaximal) {L K : Submodule R V} (hL : L.IsLattice F)
    (hK : K.IsLattice F) (hLK : L ≤ K) :
    (∃ s : R, s ∉ q ∧ ∀ x ∈ K, s • x ∈ L) ∨ ∃ z ∈ K, z ∉ L ∧ ∀ r ∈ q, r • z ∈ L := by
  set I : Ideal R := L.colon (K : Set V)
  by_cases hIq : I ≤ q
  · right
    obtain ⟨c, hc0, hc⟩ := exists_smul_le_of_fg (F := F) hK.fg (by rw [hL.span_eq_top]; intro _ _; trivial)
    have hI0 : I ≠ ⊥ := fun h => hc0 (by
      have : c ∈ I := Submodule.mem_colon.2 hc
      rwa [h, Ideal.mem_bot] at this)
    have := hq
    obtain ⟨J, hqJ, hIJ⟩ := Ideal.eq_prime_pow_mul_coprime hI0 q
    set e := Multiset.count q (UniqueFactorizationMonoid.normalizedFactors I)
    set N := L ⊔ J • K
    have hIK : I • K ≤ L := Submodule.smul_le.2 fun r hr x hx => Submodule.mem_colon.1 hr x hx
    have hN : q ^ e • N ≤ L := by
      rw [Submodule.smul_le]
      intro r hr x hx
      obtain ⟨l, hl, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
      rw [smul_add]
      refine L.add_mem (L.smul_mem r hl) (hIK ?_)
      rw [hIJ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hr hy
    have hNL : ¬ N ≤ L := by
      intro h
      have hJ : J ≤ I := fun r hr => Submodule.mem_colon.2 fun x hx =>
        h (Submodule.mem_sup_right (Submodule.smul_mem_smul hr hx))
      have : q ⊔ J ≤ q := sup_le le_rfl (hJ.trans hIq)
      rw [hqJ] at this
      exact hq.ne_top (top_le_iff.1 this)
    obtain ⟨z, hzN, hzL, hqz⟩ := exists_mem_smul_mem ⟨e, hN⟩ hNL
    exact ⟨z, sup_le hLK Submodule.smul_le_right hzN, hzL, hqz⟩
  · left
    obtain ⟨s, hsI, hsq⟩ := Set.not_subset.1 hIq
    exact ⟨s, hsq, Submodule.mem_colon.1 hsI⟩

/-- A submodule $N$ with $L\subseteq N$ and $cN\subseteq L$ ($c\ne0$) for a lattice $L$ is a lattice. -/
theorem isLattice_of_le_of_smul {L N : Submodule R V} (hL : L.IsLattice F) (hLN : L ≤ N) {c : R} (hc0 : c ≠ 0)
    (hc : ∀ x ∈ N, c • x ∈ L) : N.IsLattice F := by
  refine ⟨?_, eq_top_iff.2 (hL.span_eq_top ▸ Submodule.span_mono (SetLike.coe_subset_coe.2 hLN))⟩
  have hcF : algebraMap R F c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R F)]; exact hc0
  have : IsNoetherian R L := isNoetherian_of_fg_of_noetherian L hL.fg
  set f : V →ₗ[R] V := (LinearMap.lsmul F V (algebraMap R F c)).restrictScalars R
  have hfinj : Function.Injective f := fun x y hxy => by
    simp only [f, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply] at hxy
    exact smul_right_injective V hcF hxy
  have hmap : N.map f ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    show algebraMap R F c • x ∈ L
    rw [algebraMap_smul]; exact hc x hx
  have hfg : (N.map f).FG := by
    have hfg' : ((N.map f).comap L.subtype).FG := IsNoetherian.noetherian _
    have : N.map f = ((N.map f).comap L.subtype).map L.subtype := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hmap]
    rw [this]; exact hfg'.map _
  exact (Submodule.fg_of_fg_map_injective f hfinj hfg)

/-- A submodule $K$ with $cL\subseteq K\subseteq L$ ($c\ne0$) for a lattice $L$ is a lattice. -/
theorem isLattice_of_smul_le {L K : Submodule R V} (hL : L.IsLattice F) (hKL : K ≤ L) {c : R} (hc0 : c ≠ 0)
    (hc : ∀ x ∈ L, c • x ∈ K) : K.IsLattice F := by
  have hcF : algebraMap R F c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R F)]; exact hc0
  refine ⟨?_, ?_⟩
  · have : IsNoetherian R L := isNoetherian_of_fg_of_noetherian L hL.fg
    have hfg : (K.comap L.subtype).FG := IsNoetherian.noetherian _
    have hN : K = (K.comap L.subtype).map L.subtype := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hKL]
    rw [hN]; exact hfg.map _
  · rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have : x = (algebraMap R F c)⁻¹ • (c • x) := by
      rw [← algebraMap_smul F c x, smul_smul, inv_mul_cancel₀ hcF, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hc x hx))

/-! ### Hessian valuedness and evenness: elementary facts -/

theorem polar_rsmul_left (r : R) (x y : V) : polar Q (r • x) y = r • polar Q x y := by
  rw [← algebraMap_smul F r x, polar_smul_left, smul_eq_mul, Algebra.smul_def]

theorem polar_rsmul_right (r : R) (x y : V) : polar Q x (r • y) = r • polar Q x y := by
  rw [polar_comm, polar_rsmul_left, polar_comm]

/-- The Hessian space $(V, H)$ is the bilinear space of $2Q$: $\mathfrak a$-valued for `(2 : F) • Q` (§2) is
$\mathfrak a$-valued for $H$. -/
theorem isAValued_two_smul_iff {a : Submodule R F} {L : Submodule R V} :
    IsAValued ((2 : F) • Q) a L ↔ IsHValued Q a L := by
  constructor
  · intro h x hx y hy
    rw [← bil_two_smul]; exact h (bil_mem_scale _ hx hy)
  · intro h
    rw [IsAValued, scale, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, bil_two_smul]; exact h x hx y hy

/-- The Hessian form of a non-degenerate space is non-degenerate. -/
theorem nondegenerate_two_smul (hV : (QuadraticMap.associated Q).Nondegenerate) :
    (QuadraticMap.associated ((2 : F) • Q)).Nondegenerate := by
  have key : ∀ x y : V, QuadraticMap.associated ((2 : F) • Q) x y = 0 → QuadraticMap.associated Q x y = 0 := by
    intro x y h
    rw [show QuadraticMap.associated ((2 : F) • Q) x y = bil ((2 : F) • Q) x y from rfl, bil_two_smul] at h
    rw [QuadraticMap.associated_apply]
    show ⅟(2 : F) • polar Q x y = 0
    rw [h, smul_zero]
  refine ⟨fun x hx => hV.1 x fun y => key x y (hx y), fun y hy => hV.2 y fun x => key x y (hy x)⟩

theorem IsHValued.mono {a : Submodule R F} {L N : Submodule R V} (h : IsHValued Q a L) (hNL : N ≤ L) :
    IsHValued Q a N := fun x hx y hy => h x (hNL hx) y (hNL hy)

theorem IsAEvenAt.mono {a : Submodule R F} {q : Ideal R} [q.IsPrime] {L N : Submodule R V}
    (h : IsAEvenAt Q a q L) (hNL : N ≤ L) : IsAEvenAt Q a q N := fun x hx => h x (hNL hx)

theorem isHValued_sup {a : Submodule R F} {L₁ L₂ : Submodule R V} (h₁ : IsHValued Q a L₁)
    (h₂ : IsHValued Q a L₂) (h₁₂ : ∀ x ∈ L₁, ∀ y ∈ L₂, polar Q x y ∈ a) : IsHValued Q a (L₁ ⊔ L₂) := by
  intro x hx y hy
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
  have e3 : polar Q x₂ y₁ ∈ a := by rw [polar_comm]; exact h₁₂ _ hy₁ _ hx₂
  simp only [polar_add_left, polar_add_right]
  exact a.add_mem (a.add_mem (h₁ _ hx₁ _ hy₁) e3) (a.add_mem (h₁₂ _ hx₁ _ hy₂) (h₂ _ hx₂ _ hy₂))

theorem isAEvenAt_sup {a : Submodule R F} {q : Ideal R} [q.IsPrime] {L₁ L₂ : Submodule R V}
    (h : IsHValued Q a (L₁ ⊔ L₂)) (h₁ : IsAEvenAt Q a q L₁) (h₂ : IsAEvenAt Q a q L₂) :
    IsAEvenAt Q a q (L₁ ⊔ L₂) := by
  intro x hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
  rw [polar_add_self]
  exact (locAt q _).add_mem ((locAt q _).add_mem (h₁ _ hx₁) (h₂ _ hx₂))
    (le_locAt q _ (two_mul_mem_twoA (h _ (Submodule.mem_sup_left hx₁) _ (Submodule.mem_sup_right hx₂))))

theorem polar_span_singleton {z x y : V} (hx : x ∈ span R {z}) (hy : y ∈ span R {z}) :
    ∃ r : R, polar Q x y = r • polar Q z z := by
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  exact ⟨s * t, by rw [polar_rsmul_left, polar_rsmul_right, smul_smul]⟩

theorem isHValued_span_singleton {a : Submodule R F} {z : V} (h : polar Q z z ∈ a) :
    IsHValued Q a (span R {z}) := fun x hx y hy => by
  obtain ⟨r, hr⟩ := polar_span_singleton Q hx hy
  rw [hr]; exact a.smul_mem r h

theorem isAEvenAt_span_singleton {a : Submodule R F} {q : Ideal R} [q.IsPrime] {z : V}
    (h : polar Q z z ∈ locAt q (twoA a)) : IsAEvenAt Q a q (span R {z}) := fun x hx => by
  obtain ⟨r, hr⟩ := polar_span_singleton Q hx hx
  rw [hr]; exact (locAt q _).smul_mem r h

theorem mem_locAt_of_smul {q : Ideal R} [q.IsPrime] {I : Submodule R F} {s : R} (hs : s ∉ q) {x : F}
    (h : s • x ∈ locAt q I) : x ∈ locAt q I := by
  obtain ⟨t, ht, htx⟩ := h
  exact ⟨t * s, fun h' => (Ideal.IsPrime.mem_or_mem ‹_› h').elim ht hs, by rw [mul_smul]; exact htx⟩

/-- $\mathfrak q(L + Rz)\subseteq L$ when $\mathfrak qz\subseteq L$. -/
theorem smul_sup_span_le {q : Ideal R} {L : Submodule R V} {z : V} (hqz : ∀ r ∈ q, r • z ∈ L) :
    q ^ 1 • (L ⊔ span R {z}) ≤ L := by
  rw [pow_one, Submodule.smul_le]
  intro r hr x hx
  obtain ⟨l, hl, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [smul_add, smul_comm r t]
  exact L.add_mem (L.smul_mem r hl) (L.smul_mem t (hqz r hr))

/-! ### Local notions, expressed globally -/

/-- **$L_1$ and $L_2$ agree at $\mathfrak q$**: $sL_1\subseteq L_2$ and $sL_2\subseteq L_1$ for some $s\in R\setminus\mathfrak q$.
For lattices this is $(L_1)_{\mathfrak q} = (L_2)_{\mathfrak q}$ (the paper's "$(L')_{\mathfrak q} = L_{\mathfrak q}$", Algorithm 4.6,
proof, p. 16). -/
@[kb "hanke2013algorithms" "Algorithm 4.6, proof, p. 16 ((L')_q = L_q, globally)"]
def AgreeAt (q : Ideal R) (L₁ L₂ : Submodule R V) : Prop :=
  ∃ s : R, s ∉ q ∧ (∀ x ∈ L₁, s • x ∈ L₂) ∧ ∀ x ∈ L₂, s • x ∈ L₁

theorem AgreeAt.refl {q : Ideal R} (hq : q ≠ ⊤) (L : Submodule R V) : AgreeAt q L L :=
  ⟨1, fun h => hq ((Ideal.eq_top_iff_one _).2 h), fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩

theorem AgreeAt.symm {q : Ideal R} {L₁ L₂ : Submodule R V} (h : AgreeAt q L₁ L₂) : AgreeAt q L₂ L₁ :=
  let ⟨s, hs, h₁, h₂⟩ := h; ⟨s, hs, h₂, h₁⟩

theorem AgreeAt.trans {q : Ideal R} [q.IsPrime] {L₁ L₂ L₃ : Submodule R V} (h : AgreeAt q L₁ L₂)
    (h' : AgreeAt q L₂ L₃) : AgreeAt q L₁ L₃ := by
  obtain ⟨s, hs, h₁, h₂⟩ := h
  obtain ⟨t, ht, h₃, h₄⟩ := h'
  refine ⟨t * s, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht hs, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]; exact h₃ _ (h₁ x hx)
  · rw [mul_comm, mul_smul]; exact h₂ _ (h₄ x hx)

/-- If $\mathfrak pL_2\subseteq L_1\subseteq L_2$, then $L_1$, $L_2$ agree at every maximal $\mathfrak q\ne\mathfrak p$. -/
theorem agreeAt_of_smul_le {p q : Ideal R} (hp : p.IsMaximal) (hq : q.IsMaximal) (hpq : p ≠ q)
    {L₁ L₂ : Submodule R V} (h₁₂ : ∀ x ∈ L₁, x ∈ L₂) (h₂₁ : p • L₂ ≤ L₁) : AgreeAt q L₁ L₂ := by
  have : ¬ p ≤ q := fun h => hpq (hp.eq_of_le hq.ne_top h)
  obtain ⟨s, hsp, hsq⟩ := Set.not_subset.1 this
  exact ⟨s, hsq, fun x hx => L₂.smul_mem s (h₁₂ x hx), fun x hx => h₂₁ (Submodule.smul_mem_smul hsp hx)⟩

/-- **$\mathfrak a$-maximal at $\mathfrak q$** for the Hessian form (Hanke 2013, Algorithm 4.6, proof, p. 16: "maximal
$\mathfrak a$-valued at $\mathfrak q$"): $L$ is $\mathfrak a$-valued for $H$ and every $\mathfrak a$-valued $N\supseteq L$ with
$\mathfrak q^kN\subseteq L$ for some $k$ (i.e. $N_{\mathfrak q'} = L_{\mathfrak q'}$ for all $\mathfrak q'\ne\mathfrak q$) equals $L$. -/
@[kb "hanke2013algorithms" "Algorithm 4.6, proof, p. 16 (maximal a-valued at q, globally)"]
def IsHMaximalAt (a : Submodule R F) (q : Ideal R) (L : Submodule R V) : Prop :=
  IsHValued Q a L ∧ ∀ N : Submodule R V, L ≤ N → (∃ k : ℕ, q ^ k • N ≤ L) → IsHValued Q a N → N = L

/-- **Maximal $\mathfrak a$-even at $\mathfrak q$** (Hanke 2013, Algorithm 4.6, proof, p. 16): $L$ is $\mathfrak a$-valued for $H$
and $\mathfrak a$-even at $\mathfrak q$, and every $N\supseteq L$ with the same two properties and $\mathfrak q^kN\subseteq L$ for some
$k$ equals $L$. -/
@[kb "hanke2013algorithms" "Algorithm 4.6, proof, p. 16 (maximal a-even at p, globally)"]
def IsMaxEvenAt (a : Submodule R F) (q : Ideal R) [q.IsPrime] (L : Submodule R V) : Prop :=
  IsHValued Q a L ∧ IsAEvenAt Q a q L ∧
    ∀ N : Submodule R V, L ≤ N → (∃ k : ℕ, q ^ k • N ≤ L) → IsHValued Q a N → IsAEvenAt Q a q N → N = L

theorem IsHMaximalAt.not_sup {a : Submodule R F} {q : Ideal R} {L : Submodule R V} (h : IsHMaximalAt Q a q L)
    {z : V} (hz : z ∉ L) (hqz : ∀ r ∈ q, r • z ∈ L) : ¬ IsHValued Q a (L ⊔ span R {z}) := fun hv =>
  hz (h.2 _ le_sup_left ⟨1, smul_sup_span_le hqz⟩ hv ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))

theorem IsMaxEvenAt.not_sup {a : Submodule R F} {q : Ideal R} [q.IsPrime] {L : Submodule R V}
    (h : IsMaxEvenAt Q a q L) {z : V} (hz : z ∉ L) (hqz : ∀ r ∈ q, r • z ∈ L)
    (hv : IsHValued Q a (L ⊔ span R {z})) : ¬ IsAEvenAt Q a q (L ⊔ span R {z}) := fun he =>
  hz (h.2.2 _ le_sup_left ⟨1, smul_sup_span_le hqz⟩ hv he ▸
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))

theorem isHMaximalAt_of_forall {a : Submodule R F} {q : Ideal R} {L : Submodule R V} (hL : IsHValued Q a L)
    (h : ∀ z, z ∉ L → (∀ r ∈ q, r • z ∈ L) → ¬ IsHValued Q a (L ⊔ span R {z})) : IsHMaximalAt Q a q L := by
  refine ⟨hL, fun N hLN hk hN => ?_⟩
  by_contra hne
  obtain ⟨z, hzN, hzL, hqz⟩ := exists_mem_smul_mem hk fun h' => hne (le_antisymm h' hLN)
  exact h z hzL hqz (hN.mono Q (sup_le hLN ((Submodule.span_singleton_le_iff_mem _ _).2 hzN)))

theorem isMaxEvenAt_of_forall {a : Submodule R F} {q : Ideal R} [q.IsPrime] {L : Submodule R V}
    (hL : IsHValued Q a L) (he : IsAEvenAt Q a q L)
    (h : ∀ z, z ∉ L → (∀ r ∈ q, r • z ∈ L) → IsHValued Q a (L ⊔ span R {z}) →
      ¬ IsAEvenAt Q a q (L ⊔ span R {z})) : IsMaxEvenAt Q a q L := by
  refine ⟨hL, he, fun N hLN hk hN hNe => ?_⟩
  by_contra hne
  obtain ⟨z, hzN, hzL, hqz⟩ := exists_mem_smul_mem hk fun h' => hne (le_antisymm h' hLN)
  have hle := sup_le hLN ((Submodule.span_singleton_le_iff_mem _ _).2 hzN)
  exact h z hzL hqz (hN.mono Q hle) (hNe.mono Q hle)

/-- $\mathfrak a$-maximal at $\mathfrak q$ and $\mathfrak a$-even at $\mathfrak q$ gives maximal $\mathfrak a$-even at $\mathfrak q$. -/
theorem IsHMaximalAt.isMaxEvenAt {a : Submodule R F} {q : Ideal R} [q.IsPrime] {L : Submodule R V}
    (h : IsHMaximalAt Q a q L) (he : IsAEvenAt Q a q L) : IsMaxEvenAt Q a q L :=
  ⟨h.1, he, fun N hLN hk hN _ => h.2 N hLN hk hN⟩

/-- A (globally) $\mathfrak a$-maximal lattice of the Hessian space is $\mathfrak a$-maximal at every $\mathfrak q$. -/
theorem isHMaximalAt_of_isAMaximal {a : Submodule R F} (q : Ideal R) {L : Submodule R V}
    (h : IsAMaximal ((2 : F) • Q) a L) : IsHMaximalAt Q a q L :=
  ⟨(isAValued_two_smul_iff Q).1 h.1, fun N hLN _ hN => h.2 N hLN ((isAValued_two_smul_iff Q).2 hN)⟩

/-- Transport of $L_2 + Rz$ to $L_1 + R(sz)$ along an agreement at $\mathfrak q$: valuedness. -/
theorem isHValued_sup_smul {a : Submodule R F} {L₁ L₂ : Submodule R V} {s : R} (hs : ∀ x ∈ L₁, s • x ∈ L₂)
    (h₁ : IsHValued Q a L₁) {z : V} (h : IsHValued Q a (L₂ ⊔ span R {z})) :
    IsHValued Q a (L₁ ⊔ span R {s • z}) := by
  have hz : z ∈ L₂ ⊔ span R {z} := Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  refine isHValued_sup Q h₁ (isHValued_span_singleton Q ?_) fun x hx y hy => ?_
  · rw [polar_rsmul_left, polar_rsmul_right]; exact a.smul_mem _ (a.smul_mem _ (h z hz z hz))
  · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [polar_rsmul_right, polar_rsmul_right, ← polar_rsmul_left]
    exact a.smul_mem _ (h _ (Submodule.mem_sup_left (hs x hx)) z hz)

/-- Transport of $L_2 + Rz$ to $L_1 + R(sz)$ along an agreement at $\mathfrak q$: evenness at $\mathfrak q$. -/
theorem isAEvenAt_sup_smul {a : Submodule R F} {q : Ideal R} [q.IsPrime] {L₁ L₂ : Submodule R V} {s : R}
    (h₁ : IsAEvenAt Q a q L₁) {z : V} (hv : IsHValued Q a (L₁ ⊔ span R {s • z}))
    (h : IsAEvenAt Q a q (L₂ ⊔ span R {z})) : IsAEvenAt Q a q (L₁ ⊔ span R {s • z}) := by
  have hz : z ∈ L₂ ⊔ span R {z} := Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  refine isAEvenAt_sup Q hv h₁ (isAEvenAt_span_singleton Q ?_)
  rw [polar_rsmul_left, polar_rsmul_right]
  exact (locAt q _).smul_mem _ ((locAt q _).smul_mem _ (h z hz))

/-- The vector $sz$ ($s\notin\mathfrak q$, $\mathfrak qz\subseteq L_2$, $z\notin L_2$) is not in $L_1$ when $sL_1\subseteq L_2$. -/
theorem smul_not_mem_of_agree {q : Ideal R} (hq : q.IsMaximal) {L₁ L₂ : Submodule R V} {s : R} (hsq : s ∉ q)
    (hs : ∀ x ∈ L₁, s • x ∈ L₂) {z : V} (hz : z ∉ L₂) (hqz : ∀ r ∈ q, r • z ∈ L₂) : s • z ∉ L₁ := by
  intro h
  have h2 : (s * s) • z ∈ L₂ := by rw [mul_smul]; exact hs _ h
  have hss : s * s ∉ q := fun h' => (hq.isPrime.mem_or_mem h').elim hsq hsq
  obtain ⟨u, i, hi, hui⟩ := hq.exists_inv hss
  apply hz
  have : z = u • (s * s) • z + i • z := by rw [smul_smul, ← add_smul, hui, one_smul]
  rw [this]
  exact L₂.add_mem (L₂.smul_mem u h2) (hqz i hi)

/-- Evenness at $\mathfrak q$ is local: it passes along an agreement at $\mathfrak q$. -/
theorem AgreeAt.isAEvenAt {a : Submodule R F} {q : Ideal R} [q.IsPrime] {L₁ L₂ : Submodule R V}
    (h : AgreeAt q L₁ L₂) (h₁ : IsAEvenAt Q a q L₁) : IsAEvenAt Q a q L₂ := by
  obtain ⟨s, hs, -, h₂₁⟩ := h
  intro x hx
  have := h₁ _ (h₂₁ x hx)
  rw [polar_rsmul_left, polar_rsmul_right] at this
  exact mem_locAt_of_smul hs (mem_locAt_of_smul hs this)

/-- $\mathfrak a$-maximality at $\mathfrak q$ is local: it passes along an agreement at $\mathfrak q$. -/
theorem AgreeAt.isHMaximalAt {a : Submodule R F} {q : Ideal R} (hq : q.IsMaximal) {L₁ L₂ : Submodule R V}
    (h : AgreeAt q L₁ L₂) (h₂ : IsHValued Q a L₂) (h₁ : IsHMaximalAt Q a q L₁) : IsHMaximalAt Q a q L₂ := by
  obtain ⟨s, hs, h₁₂, h₂₁⟩ := h
  refine isHMaximalAt_of_forall Q h₂ fun z hz hqz hv => ?_
  refine h₁.not_sup Q (smul_not_mem_of_agree hq hs h₁₂ hz hqz) (fun r hr => ?_) (isHValued_sup_smul Q h₁₂ h₁.1 hv)
  rw [smul_comm]; exact h₂₁ _ (hqz r hr)

/-- Maximal evenness at $\mathfrak q$ is local: it passes along an agreement at $\mathfrak q$. -/
theorem AgreeAt.isMaxEvenAt {a : Submodule R F} {q : Ideal R} [q.IsPrime] (hq : q.IsMaximal) {L₁ L₂ : Submodule R V}
    (h : AgreeAt q L₁ L₂) (h₂ : IsHValued Q a L₂) (h₁ : IsMaxEvenAt Q a q L₁) : IsMaxEvenAt Q a q L₂ := by
  have he₂ : IsAEvenAt Q a q L₂ := h.isAEvenAt Q h₁.2.1
  obtain ⟨s, hs, h₁₂, h₂₁⟩ := h
  refine isMaxEvenAt_of_forall Q h₂ he₂ fun z hz hqz hv he => ?_
  have hv' := isHValued_sup_smul Q h₁₂ h₁.1 hv
  refine h₁.not_sup Q (smul_not_mem_of_agree hq hs h₁₂ hz hqz) (fun r hr => ?_) hv'
    (isAEvenAt_sup_smul Q h₁.2.1 hv' he)
  rw [smul_comm]; exact h₂₁ _ (hqz r hr)

/-- $\mathfrak a$-maximal at $\mathfrak q$ and $T\supseteq L$ $\mathfrak a$-valued lattices: $T$ and $L$ agree at $\mathfrak q$. -/
theorem IsHMaximalAt.agreeAt {a : Submodule R F} {q : Ideal R} (hq : q.IsMaximal) {L T : Submodule R V}
    (hL : L.IsLattice F) (hT : T.IsLattice F) (hLT : L ≤ T) (hTv : IsHValued Q a T) (h : IsHMaximalAt Q a q L) :
    AgreeAt q L T := by
  rcases exists_smul_le_or hq hL hT hLT with ⟨s, hs, hsT⟩ | ⟨z, hzT, hzL, hqz⟩
  · exact ⟨s, hs, fun x hx => T.smul_mem s (hLT hx), hsT⟩
  · exact absurd (hTv.mono Q (sup_le hLT ((Submodule.span_singleton_le_iff_mem _ _).2 hzT))) (h.not_sup Q hzL hqz)

/-! ### The core of the proof of Algorithm 4.6 -/

/-- If $s\notin\mathfrak p$ and $\mathfrak p^k$ both send $x$ into a submodule $I$ ($\mathfrak p$ maximal), then $x\in I$. -/
theorem mem_of_smul_mem_of_pow {M : Type*} [AddCommGroup M] [Module R M] {p : Ideal R} (hp : p.IsMaximal)
    {I : Submodule R M} {x : M} {s : R} (hs : s ∉ p) (hsx : s • x ∈ I) {k : ℕ} (hk : ∀ r ∈ p ^ k, r • x ∈ I) :
    x ∈ I := by
  set J := I.colon ({x} : Set M)
  have hJ : J = ⊤ := by
    by_contra hJ
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
    have hpk : p ^ k ≤ m := fun r hr => hJm (Submodule.mem_colon_singleton.2 (hk r hr))
    have := (hp.eq_of_le hm.ne_top (Ideal.IsPrime.le_of_pow_le hpk))
    exact hs (this ▸ hJm (Submodule.mem_colon_singleton.2 hsx))
  have : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
  simpa using Submodule.mem_colon_singleton.1 this

theorem two_ne_zero_R (F : Type*) [Field F] [Algebra R F] [Invertible (2 : F)] : (2 : R) ≠ 0 := fun h => by
  have h0 : (2 : F) = 0 := by rw [← map_ofNat (algebraMap R F) 2, h, map_zero]
  exact (isUnit_of_invertible (2 : F)).ne_zero h0

/-- $\mathfrak pL\subseteq L^{\mathfrak a\text{-even at }\mathfrak p}$ when $e_{\mathfrak p}\le1$ and $\mathfrak p\mid2$. -/
theorem smul_le_evenAtSub {a : Submodule R F} {p : Ideal R} [hp : p.IsMaximal] (h2 : (2 : R) ∈ p)
    (h22 : (2 : R) ∉ p ^ 2) {L : Submodule R V} (hL : IsHValued Q a L) : p • L ≤ evenAtSub Q p hL := by
  rw [Submodule.smul_le]
  intro r hr x hx
  refine ⟨L.smul_mem r hx, ?_⟩
  rw [polar_rsmul_left, polar_rsmul_right]
  exact (locAt p _).smul_mem r (smul_le_locAt hp h2 h22 (Submodule.smul_mem_smul hr (hL x hx x hx)))

/-- $L^{\mathfrak a\text{-even at }\mathfrak p}$ is a lattice ($e_{\mathfrak p}\le1$, $\mathfrak p\mid2$). -/
theorem isLattice_evenAtSub {a : Submodule R F} {p : Ideal R} [hp : p.IsMaximal] (h2 : (2 : R) ∈ p)
    (h22 : (2 : R) ∉ p ^ 2) {L : Submodule R V} (hL : IsHValued Q a L) (hLl : L.IsLattice F) :
    (evenAtSub Q p hL).IsLattice F :=
  isLattice_of_smul_le hLl (fun _ hx => hx.1) (two_ne_zero_R F)
    fun _ hx => smul_le_evenAtSub Q h2 h22 hL (Submodule.smul_mem_smul h2 hx)

/-- A maximal $\mathfrak a$-valued lattice containing a lattice $L$ of a non-degenerate space is a lattice. -/
theorem isLattice_of_isAMaximal (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L T : Submodule R V} (hL : L.IsLattice F) (hLT : L ≤ T) (hT : IsAMaximal Q a T) :
    T.IsLattice F :=
  isLattice_of_le_of_le hL (isLattice_aDual Q hV ha ha0 hL) hLT
    (((lemma_2_2 Q).1 hT.1).trans (aDual_anti Q hLT))

/-- **The core of the proof of Algorithm 4.6, for a maximal lattice** (Hanke 2013, p. 16–17). Let $T$ be a maximal
$\mathfrak a$-valued lattice of the Hessian space $(V, H)$, $\mathfrak p$ a maximal ideal with $2\notin\mathfrak p^2$ at which $T$ is
not $\mathfrak a$-even, $M = T^{\mathfrak a\text{-even at }\mathfrak p}$, and $N\supseteq M$ an $\mathfrak a$-valued lattice with
$\mathfrak p^kN\subseteq M$. Then $N = M$, or $[N : M] = N(\mathfrak p)$ and $N$ is a maximal $\mathfrak a$-valued lattice.
*Proof* (the paper's): for a maximal $N'\supseteq N$, Lemma 2.13 gives
$[T : M]^2|D(T)| = |D(M)| = [N' : M]^2|D(N')|$, Lemma 3.17 gives $|D(T)| = |D(N')|$, so
$[N' : M] = [T : M] = N(\mathfrak p)$ (Lemma 4.5); and $[N : M]$, a divisor of $N(\mathfrak p)$ for a $\mathfrak p$-primary
extension, is $1$ or $N(\mathfrak p)$ (`latIndex_eq_one_or`; the paper: "its annihilator is $\mathfrak p^k$ ... so $k = 1$"). -/
@[kb "hanke2013algorithms" "Algorithm 4.6, proof, pp. 16–17 ([L'_Max : L^{a-even at p}] = N(p))"]
theorem step_index_of_isAMaximal (hR : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I))
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    {p : Ideal R} [hp : p.IsMaximal] (h22 : (2 : R) ∉ p ^ 2) {T : Submodule R V} (hT : T.IsLattice F)
    (hTm : IsAMaximal ((2 : F) • Q) a T) (hnot : ¬ IsAEvenAt Q a p T) {N : Submodule R V} (hN : N.IsLattice F)
    (hMN : evenAtSub Q p ((isAValued_two_smul_iff Q).1 hTm.1) ≤ N)
    (hk : ∃ k : ℕ, p ^ k • N ≤ evenAtSub Q p ((isAValued_two_smul_iff Q).1 hTm.1)) (hNv : IsHValued Q a N) :
    N = evenAtSub Q p ((isAValued_two_smul_iff Q).1 hTm.1) ∨
      (latIndex (evenAtSub Q p ((isAValued_two_smul_iff Q).1 hTm.1)) N = Nat.card (R ⧸ p) ∧
        IsAMaximal ((2 : F) • Q) a N) := by
  have hTv := (isAValued_two_smul_iff Q).1 hTm.1
  set M := evenAtSub Q p hTv with hMdef
  have hV2 := nondegenerate_two_smul Q hV
  have h2 : (2 : R) ∈ p := by
    by_contra h2
    exact hnot fun x hx => by rw [← remark_4_3_odd Q hTv p h2] at hx; exact hx.2
  have hp0 : p ≠ ⊥ := fun h => two_ne_zero_R F (by rw [h] at h2; exact (Ideal.mem_bot).1 h2)
  have : Finite (R ⧸ p) := hR p hp0
  obtain ⟨-, hidx⟩ := lemma_4_5 Q ha ha0 hp h22 hTv hnot
  have hMl : M.IsLattice F := isLattice_evenAtSub Q h2 h22 hTv hT
  have hMT : M ≤ T := fun x hx => hx.1
  obtain ⟨N', hNN', hN'm⟩ := exists_isAMaximal ((2 : F) • Q) hV2 ha ha0 hN ((isAValued_two_smul_iff Q).2 hNv)
  have hN'l := isLattice_of_isAMaximal ((2 : F) • Q) hV2 ha ha0 hN hNN' hN'm
  obtain ⟨e, -⟩ := lemma_3_17 ((2 : F) • Q) hR hV2 ha ha0 hT hN'l hTm hN'm
  have hcard := Nat.card_congr e.toEquiv
  have e1 := lemma_2_13 ((2 : F) • Q) hV2 ha ha0 hT hMl hTm.1 hMT
  have e2 := lemma_2_13 ((2 : F) • Q) hV2 ha ha0 hN'l hMl hN'm.1 (hMN.trans hNN')
  have hD0 : Nat.card (DiscModule ((2 : F) • Q) a T) ≠ 0 := by
    rw [card_discModule]; exact latIndex_ne_zero hR hT (isLattice_aDual _ hV2 ha ha0 hT)
  have hsq : latIndex M N' ^ 2 = Nat.card (R ⧸ p) ^ 2 := by
    have : latIndex M N' ^ 2 * Nat.card (DiscModule ((2 : F) • Q) a T) =
        latIndex M T ^ 2 * Nat.card (DiscModule ((2 : F) • Q) a T) := by
      rw [← e1, e2, hcard]
    rw [← hidx]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hD0) this
  have hN'M : latIndex M N' = Nat.card (R ⧸ p) := Nat.pow_left_injective (by norm_num) hsq
  have hmul := AddSubgroup.relIndex_mul_relIndex M.toAddSubgroup N.toAddSubgroup N'.toAddSubgroup hMN hNN'
  have hdvd : latIndex M N ∣ Nat.card (R ⧸ p) := by
    rw [← hN'M]; exact ⟨_, hmul.symm⟩
  rcases latIndex_eq_one_or hp hMN hk hdvd with h | ⟨hNM, -⟩
  · exact Or.inl h
  · refine Or.inr ⟨hNM, ?_⟩
    have h1 : N.toAddSubgroup.relIndex N'.toAddSubgroup = 1 := by
      have hpos : 0 < Nat.card (R ⧸ p) := Nat.card_pos
      have : Nat.card (R ⧸ p) * N.toAddSubgroup.relIndex N'.toAddSubgroup = Nat.card (R ⧸ p) * 1 := by
        rw [mul_one]
        calc Nat.card (R ⧸ p) * N.toAddSubgroup.relIndex N'.toAddSubgroup
            = latIndex M N * N.toAddSubgroup.relIndex N'.toAddSubgroup := by rw [hNM]
          _ = Nat.card (R ⧸ p) := hmul.trans hN'M
      exact Nat.eq_of_mul_eq_mul_left hpos this
    have : N = N' := le_antisymm hNN' (AddSubgroup.relIndex_eq_one.1 h1)
    rw [this]; exact hN'm

/-- **The core of the proof of Algorithm 4.6** (Hanke 2013, pp. 16–17), for a lattice $L$ that is only
$\mathfrak a$-maximal at $\mathfrak p$ (as in the later rounds of step 2). Let $L$ be an $\mathfrak a$-valued lattice of $(V, H)$,
$\mathfrak a$-maximal at $\mathfrak p$ ($2\notin\mathfrak p^2$) and not $\mathfrak a$-even at $\mathfrak p$, $M = L^{\mathfrak a\text{-even at }\mathfrak p}$,
and $N\supseteq M$ an $\mathfrak a$-valued lattice with $\mathfrak p^kN\subseteq M$. Then $N = M$, or $[N : M] = N(\mathfrak p)$ and $N$
is $\mathfrak a$-maximal at $\mathfrak p$. *Proof*: reduce to `step_index_of_isAMaximal` for a maximal $T\supseteq L$, which agrees
with $L$ at $\mathfrak p$, and $N_T = N + T^{\mathfrak a\text{-even at }\mathfrak p}$ (the lattice equal to $N$ at $\mathfrak p$ and to $T$
elsewhere). -/
@[kb "hanke2013algorithms" "Algorithm 4.6, proof, pp. 16–17 ([L' : L^{a-even at p}] = N(p) and L' = L'_Max)"]
theorem step_index (hR : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I))
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    {p : Ideal R} [hp : p.IsMaximal] (h22 : (2 : R) ∉ p ^ 2) {L : Submodule R V} (hL : L.IsLattice F)
    (hLm : IsHMaximalAt Q a p L) (hnot : ¬ IsAEvenAt Q a p L) {N : Submodule R V} (hN : N.IsLattice F)
    (hMN : evenAtSub Q p hLm.1 ≤ N) (hk : ∃ k : ℕ, p ^ k • N ≤ evenAtSub Q p hLm.1) (hNv : IsHValued Q a N) :
    N = evenAtSub Q p hLm.1 ∨
      (latIndex (evenAtSub Q p hLm.1) N = Nat.card (R ⧸ p) ∧ IsHMaximalAt Q a p N) := by
  set M := evenAtSub Q p hLm.1 with hMdef
  have hV2 := nondegenerate_two_smul Q hV
  obtain ⟨k, hk⟩ := hk
  obtain ⟨T, hLT, hTm⟩ := exists_isAMaximal ((2 : F) • Q) hV2 ha ha0 hL ((isAValued_two_smul_iff Q).2 hLm.1)
  have hT := isLattice_of_isAMaximal ((2 : F) • Q) hV2 ha ha0 hL hLT hTm
  have hTv := (isAValued_two_smul_iff Q).1 hTm.1
  obtain ⟨s, hs, -, hsT⟩ := hLm.agreeAt Q hp hL hT hLT hTv
  set MT := evenAtSub Q p hTv with hMTdef
  have hTnot : ¬ IsAEvenAt Q a p T := fun h => hnot (h.mono Q hLT)
  have h2 : (2 : R) ∈ p := by
    by_contra h2
    exact hnot fun x hx => by rw [← remark_4_3_odd Q hLm.1 p h2] at hx; exact hx.2
  have hMMT : M ≤ MT := fun x hx => ⟨hLT hx.1, hx.2⟩
  have hsMT : ∀ m ∈ MT, s • m ∈ M := fun m hm => by
    refine ⟨hsT m hm.1, ?_⟩
    rw [polar_rsmul_left, polar_rsmul_right]
    exact (locAt p _).smul_mem s ((locAt p _).smul_mem s hm.2)
  have hNL : ∀ x ∈ N, ∀ r ∈ p ^ k, r • x ∈ M := fun x hx r hr => hk (Submodule.smul_mem_smul hr hx)
  set NT := N ⊔ MT with hNTdef
  have hNTv : IsHValued Q a NT := by
    refine isHValued_sup Q hNv (hTv.mono Q fun x hx => hx.1) fun l hl m hm => ?_
    refine mem_of_smul_mem_of_pow hp (I := a) hs ?_ (k := k) fun r hr => ?_
    · rw [← polar_rsmul_right]; exact hNv _ hl _ (hMN (hsMT m hm))
    · rw [← polar_rsmul_left]; exact hTv _ (hLT (hNL l hl r hr).1) _ hm.1
  have hNTk : p ^ k • NT ≤ MT := by
    rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact MT.add_mem (hMMT (hNL l hl r hr)) (MT.smul_mem r hm)
  have hMTl := isLattice_evenAtSub Q h2 h22 hTv hT
  have hNTl : NT.IsLattice F := isLattice_sup hN hMTl
  have hinf : N ⊓ MT = M := by
    apply le_antisymm
    · rintro x ⟨hxN, hxMT⟩
      refine ⟨?_, hxMT.2⟩
      exact mem_of_smul_mem_of_pow hp hs (hsMT x hxMT).1 fun r hr => (hNL x hxN r hr).1
    · exact le_inf hMN hMMT
  have hidx : latIndex MT NT = latIndex M N := by
    show MT.toAddSubgroup.relIndex (N ⊔ MT).toAddSubgroup = M.toAddSubgroup.relIndex N.toAddSubgroup
    rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right,
      inf_comm, ← hinf]
    rfl
  rcases step_index_of_isAMaximal Q hR hV ha ha0 h22 hT hTm hTnot hNTl le_sup_right ⟨k, hNTk⟩ hNTv with
    h | ⟨hNTidx, hNTm⟩
  · left
    have : N ≤ MT := fun x hx => by
      have : x ∈ NT := Submodule.mem_sup_left hx
      rwa [h] at this
    rw [← hinf]; exact (inf_eq_left.2 this).symm
  · right
    refine ⟨hidx ▸ hNTidx, ?_⟩
    have hag : AgreeAt p NT N := by
      refine ⟨s, hs, fun x hx => ?_, fun x hx => NT.smul_mem s (Submodule.mem_sup_left hx)⟩
      obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.1 hx
      rw [smul_add]
      exact N.add_mem (N.smul_mem s hl) (hMN (hsMT m hm))
    exact hag.isHMaximalAt Q hp hNv (isHMaximalAt_of_isAMaximal Q p hNTm)

/-! ### Step 2 of Algorithm 4.6 -/

/-- **$\mathfrak p$-neighbours in the Hessian space** (Hanke 2013, Definition 5.1, p. 17, with the correction recorded
for it, read for lattices that are $\mathfrak a$-valued for $H$ as in step 2 of Algorithm 4.6): $L$, $L'$ are $\mathfrak a$-valued
for $H$ (`valued`, `valued'`), $[L : L\cap L'] = [L' : L\cap L'] = N(\mathfrak p)$ (`index`, `index'`),
$\mathfrak pL\subseteq L'$ and $\mathfrak pL'\subseteq L$ (`smul_le`, `smul_le'`; the correction), and $H(L, L')\not\subseteq\mathfrak a$
(`not_valued`). For $\mathfrak a$-valued quadratic lattices this is `IsPNeighbor` plus the correction
(`isHPNeighbor_of_isPNeighbor`). -/
@[kb "hanke2013algorithms" "Definition 5.1, p. 17 (p-neighbours, corrected, for a-valued lattices of (V, H)); Algorithm 4.6, step 2"]
structure IsHPNeighbor (a : Submodule R F) (p : Ideal R) (L L' : Submodule R V) : Prop where
  valued : IsHValued Q a L
  valued' : IsHValued Q a L'
  index : latIndex (L ⊓ L') L = Nat.card (R ⧸ p)
  index' : latIndex (L ⊓ L') L' = Nat.card (R ⧸ p)
  smul_le : p • L ≤ L'
  smul_le' : p • L' ≤ L
  not_valued : ∃ x ∈ L, ∃ y ∈ L', polar Q x y ∉ a

/-- $\mathfrak p$-neighbouring $\mathfrak a$-valued quadratic lattices (Definition 5.1) with $\mathfrak pL\subseteq L'$,
$\mathfrak pL'\subseteq L$ are $\mathfrak p$-neighbours in the Hessian space. -/
theorem isHPNeighbor_of_isPNeighbor {a : Submodule R F} {p : Ideal R} {L L' : Submodule R V}
    (h : IsPNeighbor Q a p L L') (h₁ : p • L ≤ L') (h₂ : p • L' ≤ L) : IsHPNeighbor Q a p L L' where
  valued := fun _ hx _ hy => polar_mem_of_valued Q h.valued hx hy
  valued' := fun _ hx _ hy => polar_mem_of_valued Q h.valued' hx hy
  index := h.index
  index' := h.index'
  smul_le := h₁
  smul_le' := h₂
  not_valued := h.not_valued

/-- A lattice that is not $\mathfrak a$-even at $\mathfrak p$ has $\mathfrak p\mid2$ (Hanke 2013, Algorithm 4.6, step 1:
"Necessarily $\mathfrak p\in S\Rightarrow\mathfrak p\mid2$"; Remark 4.3). -/
@[kb "hanke2013algorithms" "Algorithm 4.6, step 1, p. 16 (p ∈ S ⇒ p | 2)"]
theorem two_mem_of_not_isAEvenAt {a : Submodule R F} {p : Ideal R} [p.IsPrime] {L : Submodule R V}
    (hL : IsHValued Q a L) (hnot : ¬ IsAEvenAt Q a p L) : (2 : R) ∈ p := by
  by_contra h2
  exact hnot fun x hx => by rw [← remark_4_3_odd Q hL p h2] at hx; exact hx.2

theorem one_lt_card_quot {p : Ideal R} [hp : p.IsMaximal] [Finite (R ⧸ p)] : 1 < Nat.card (R ⧸ p) := by
  have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.2 hp.ne_top
  exact Finite.one_lt_card

/-- **Algorithm 4.6, step 2, first case** (Hanke 2013, p. 16, and its proof): if a $\mathfrak p$-neighbour $L'$ of $L$ is
$\mathfrak a$-even at $\mathfrak p$, then $L\cap L' = L^{\mathfrak a\text{-even at }\mathfrak p}$, $L'$ is maximal $\mathfrak a$-even at $\mathfrak p$, and
$L'$ agrees with $L$ at every other maximal ideal. Here $L$ is an $\mathfrak a$-valued lattice of $(V, H)$, $\mathfrak a$-maximal at
$\mathfrak p$ ($2\notin\mathfrak p^2$) and not $\mathfrak a$-even at $\mathfrak p$. -/
@[kb "hanke2013algorithms" "Algorithm 4.6, step 2, p. 16 (an a-even p-neighbour L' replaces L)"]
theorem step_neighbor (hR : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I))
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    {p : Ideal R} [hp : p.IsMaximal] (h22 : (2 : R) ∉ p ^ 2) {L : Submodule R V} (hL : L.IsLattice F)
    (hLm : IsHMaximalAt Q a p L) (hnot : ¬ IsAEvenAt Q a p L) {L' : Submodule R V} (hL' : L'.IsLattice F)
    (hN : IsHPNeighbor Q a p L L') (he : IsAEvenAt Q a p L') :
    L ⊓ L' = evenAtSub Q p hLm.1 ∧ IsMaxEvenAt Q a p L' ∧
      ∀ q : Ideal R, q.IsMaximal → q ≠ p → AgreeAt q L L' := by
  set M := evenAtSub Q p hLm.1 with hMdef
  have h2 := two_mem_of_not_isAEvenAt Q hLm.1 hnot
  have hp0 : p ≠ ⊥ := fun h => two_ne_zero_R F (by rw [h] at h2; exact (Ideal.mem_bot).1 h2)
  have : Finite (R ⧸ p) := hR p hp0
  obtain ⟨-, hidx⟩ := lemma_4_5 Q ha ha0 hp h22 hLm.1 hnot
  have hinfM : L ⊓ L' ≤ M := fun x hx => ⟨hx.1, he x hx.2⟩
  have hML : M ≤ L := fun x hx => hx.1
  have hmul := AddSubgroup.relIndex_mul_relIndex (L ⊓ L').toAddSubgroup M.toAddSubgroup L.toAddSubgroup hinfM hML
  have h1 : (L ⊓ L').toAddSubgroup.relIndex M.toAddSubgroup = 1 := by
    have hpos : 0 < Nat.card (R ⧸ p) := Nat.card_pos
    have : (L ⊓ L').toAddSubgroup.relIndex M.toAddSubgroup * Nat.card (R ⧸ p) = 1 * Nat.card (R ⧸ p) := by
      rw [one_mul]
      calc (L ⊓ L').toAddSubgroup.relIndex M.toAddSubgroup * Nat.card (R ⧸ p)
          = (L ⊓ L').toAddSubgroup.relIndex M.toAddSubgroup * latIndex M L := by rw [hidx]
        _ = Nat.card (R ⧸ p) := hmul.trans hN.index
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hinf : L ⊓ L' = M := le_antisymm hinfM (AddSubgroup.relIndex_eq_one.1 h1)
  have hML' : M ≤ L' := hinf ▸ inf_le_right
  have hk : p ^ 1 • L' ≤ M := by
    rw [pow_one, Submodule.smul_le]
    intro r hr y hy
    refine ⟨hN.smul_le' (Submodule.smul_mem_smul hr hy), ?_⟩
    rw [polar_rsmul_left, polar_rsmul_right]
    exact (locAt p _).smul_mem r ((locAt p _).smul_mem r (he y hy))
  refine ⟨hinf, ?_, fun q hq hqp => ?_⟩
  · rcases step_index Q hR hV ha ha0 h22 hL hLm hnot hL' hML' ⟨1, hk⟩ hN.valued' with h | ⟨-, hmax⟩
    · exfalso
      have := hN.index'
      rw [hinf, h, latIndex, AddSubgroup.relIndex_self] at this
      exact (one_lt_card_quot (p := p)).ne this
    · exact hmax.isMaxEvenAt Q he
  · have : ¬ p ≤ q := fun h => hqp.symm (hp.eq_of_le hq.ne_top h)
    obtain ⟨s, hsp, hsq⟩ := Set.not_subset.1 this
    exact ⟨s, hsq, fun x hx => hN.smul_le (Submodule.smul_mem_smul hsp hx),
      fun y hy => hN.smul_le' (Submodule.smul_mem_smul hsp hy)⟩

/-- **Algorithm 4.6, step 2, second case** (Hanke 2013, p. 16, and its proof): if no $\mathfrak p$-neighbour of $L$ (a lattice)
is $\mathfrak a$-even at $\mathfrak p$, then $M = L^{\mathfrak a\text{-even at }\mathfrak p}$ is a lattice, maximal $\mathfrak a$-even at $\mathfrak p$, and
agrees with $L$ at every other maximal ideal. *Proof*: an $\mathfrak a$-valued, $\mathfrak a$-even at $\mathfrak p$ lattice $N\supsetneq M$
with $\mathfrak p^kN\subseteq M$ would have $[N : M] = N(\mathfrak p)$ (`step_index`), $L\cap N = M$, and be a $\mathfrak p$-neighbour of
$L$ (the paper: "if $H(L, L')\subseteq\mathfrak a$ then the lattice $L + L'$ would be $\mathfrak a$-valued, violating the maximality of
$L$. Therefore $L'$ is a $\mathfrak p$-neighbor of $L$"). -/
@[kb "hanke2013algorithms" "Algorithm 4.6, step 2, p. 16 (otherwise L^{a-even at p} replaces L)"]
theorem step_no_neighbor (hR : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I))
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    {p : Ideal R} [hp : p.IsMaximal] (h22 : (2 : R) ∉ p ^ 2) {L : Submodule R V} (hL : L.IsLattice F)
    (hLm : IsHMaximalAt Q a p L) (hnot : ¬ IsAEvenAt Q a p L)
    (hno : ∀ L' : Submodule R V, L'.IsLattice F → IsHPNeighbor Q a p L L' → ¬ IsAEvenAt Q a p L') :
    (evenAtSub Q p hLm.1).IsLattice F ∧ IsMaxEvenAt Q a p (evenAtSub Q p hLm.1) ∧
      ∀ q : Ideal R, q.IsMaximal → q ≠ p → AgreeAt q L (evenAtSub Q p hLm.1) := by
  set M := evenAtSub Q p hLm.1 with hMdef
  have h2 := two_mem_of_not_isAEvenAt Q hLm.1 hnot
  have hp0 : p ≠ ⊥ := fun h => two_ne_zero_R F (by rw [h] at h2; exact (Ideal.mem_bot).1 h2)
  have : Finite (R ⧸ p) := hR p hp0
  obtain ⟨-, hidx⟩ := lemma_4_5 Q ha ha0 hp h22 hLm.1 hnot
  have hML : M ≤ L := fun x hx => hx.1
  have hMl : M.IsLattice F := isLattice_evenAtSub Q h2 h22 hLm.1 hL
  have hpL : p • L ≤ M := smul_le_evenAtSub Q h2 h22 hLm.1
  refine ⟨hMl, ⟨hLm.1.mono Q hML, fun x hx => hx.2, fun N hMN hk hNv hNe => ?_⟩, fun q hq hqp => ?_⟩
  · obtain ⟨k, hk'⟩ := hk
    have hNl : N.IsLattice F := by
      refine isLattice_of_le_of_smul hMl hMN (pow_ne_zero k (two_ne_zero_R F)) fun x hx => ?_
      exact hk' (Submodule.smul_mem_smul (Ideal.pow_mem_pow h2 k) hx)
    rcases step_index Q hR hV ha ha0 h22 hL hLm hnot hNl hMN ⟨k, hk'⟩ hNv with h | ⟨hNidx, -⟩
    · exact h
    · exfalso
      have hpN : p • N ≤ M := by
        rcases latIndex_eq_one_or hp hMN ⟨k, hk'⟩ (hNidx ▸ dvd_rfl) with h | ⟨-, h⟩
        · rw [h, latIndex, AddSubgroup.relIndex_self] at hNidx
          exact absurd hNidx.symm (one_lt_card_quot (p := p)).ne'
        · exact h
      -- `L ⊓ N = M`
      have hNL : ¬ L ≤ N := by
        intro hLN
        have hkL : ∃ k : ℕ, p ^ k • N ≤ L := ⟨k, hk'.trans hML⟩
        have := hLm.2 N hLN hkL hNv
        exact hnot (this ▸ hNe)
      have hinf : L ⊓ N = M := by
        have hMinf : M ≤ L ⊓ N := le_inf hML hMN
        have hmul := AddSubgroup.relIndex_mul_relIndex M.toAddSubgroup (L ⊓ N).toAddSubgroup L.toAddSubgroup
          hMinf (show L ⊓ N ≤ L from inf_le_left)
        have hdvd : latIndex M (L ⊓ N) ∣ Nat.card (R ⧸ p) := by
          rw [← hidx]; exact ⟨_, hmul.symm⟩
        have hk1 : ∃ k : ℕ, p ^ k • (L ⊓ N) ≤ M := ⟨1, by rw [pow_one]; exact (Submodule.smul_mono le_rfl inf_le_left).trans hpL⟩
        rcases latIndex_eq_one_or hp hMinf hk1 hdvd with h | ⟨h, -⟩
        · exact h
        · exfalso
          have h1 : (L ⊓ N).toAddSubgroup.relIndex L.toAddSubgroup = 1 := by
            have hpos : 0 < Nat.card (R ⧸ p) := Nat.card_pos
            have : Nat.card (R ⧸ p) * (L ⊓ N).toAddSubgroup.relIndex L.toAddSubgroup = Nat.card (R ⧸ p) * 1 := by
              rw [mul_one]
              calc Nat.card (R ⧸ p) * (L ⊓ N).toAddSubgroup.relIndex L.toAddSubgroup
                  = latIndex M (L ⊓ N) * (L ⊓ N).toAddSubgroup.relIndex L.toAddSubgroup := by rw [h]
                _ = Nat.card (R ⧸ p) := hmul.trans hidx
            exact Nat.eq_of_mul_eq_mul_left hpos this
          have hLle : L ≤ L ⊓ N := AddSubgroup.relIndex_eq_one.1 h1
          exact hNL (hLle.trans inf_le_right)
      have hnb : IsHPNeighbor Q a p L N := by
        refine ⟨hLm.1, hNv, by rw [hinf]; exact hidx, by rw [hinf]; exact hNidx, hpL.trans hMN, hpN.trans hML, ?_⟩
        by_contra hcon
        push Not at hcon
        have hsup := isHValued_sup Q hLm.1 hNv hcon
        have hk2 : ∃ k : ℕ, p ^ k • (L ⊔ N) ≤ L := by
          refine ⟨k, ?_⟩
          rw [Submodule.smul_le]
          intro r hr x hx
          obtain ⟨l, hl, n, hn, rfl⟩ := Submodule.mem_sup.1 hx
          rw [smul_add]
          exact L.add_mem (L.smul_mem r hl) (hML (hk' (Submodule.smul_mem_smul hr hn)))
        have := hLm.2 (L ⊔ N) le_sup_left hk2 hsup
        have hNle : N ≤ L := by rw [← this]; exact le_sup_right
        have hNM : N = M := le_antisymm (by rw [← hinf]; exact le_inf hNle le_rfl) hMN
        rw [hNM, latIndex, AddSubgroup.relIndex_self] at hNidx
        exact (one_lt_card_quot (p := p)).ne hNidx
      exact hno N hNl hnb hNe
  · have : ¬ p ≤ q := fun h => hqp.symm (hp.eq_of_le hq.ne_top h)
    obtain ⟨s, hsp, hsq⟩ := Set.not_subset.1 this
    exact ⟨s, hsq, fun x hx => hpL (Submodule.smul_mem_smul hsp hx), fun y hy => L.smul_mem s (hML hy)⟩

/-! ### Step 3: maximal $\mathfrak a$-even at every prime gives a maximal quadratic lattice -/

/-- **Algorithm 4.6, step 3** (Hanke 2013, p. 16: "This remaining $L$ is a maximal $\mathfrak a$-even lattice in $(V, H)$, so
$L$ is also a maximal $\mathfrak a$-valued quadratic lattice on $(V, Q)$"): a lattice that is maximal $\mathfrak a$-even at every
maximal ideal is a maximal $\mathfrak a$-valued quadratic lattice (O'Meara's $\mathfrak a$-maximal lattice, `OMeara.IsMaximal`:
$\mathfrak nL\subseteq\mathfrak a$ and maximal with this property). *Proof*: it is $\mathfrak a$-even (Remark 4.3), hence $Q(L)\subseteq\mathfrak a$
(Lemma 4.4); a lattice $K\supsetneq L$ with $Q(K)\subseteq\mathfrak a$ contains $L + Rz$ with $\mathfrak qz\subseteq L$ for some maximal
$\mathfrak q$ (`exists_smul_le_or`), which is $\mathfrak a$-valued and $\mathfrak a$-even at $\mathfrak q$ (Remark 4.2, Lemma 4.4). -/
@[kb "hanke2013algorithms" "Algorithm 4.6, step 3, p. 16"]
theorem isMaximal_of_forall_isMaxEvenAt {a : Submodule R F} {L : Submodule R V} (hL : L.IsLattice F)
    (hLv : IsHValued Q a L) (h : ∀ (q : Ideal R) [q.IsMaximal], IsMaxEvenAt Q a q L) : IsMaximal Q a L := by
  have hQ : ∀ x ∈ L, Q x ∈ a := by
    have hE : IsAEven Q a L := fun x hx =>
      ((remark_4_3 Q hLv x).2 fun p hp => ⟨hx, (h p).2.1 x hx⟩).2
    exact (lemma_4_4 Q a L).1 hE
  refine ⟨hL, ?_, fun K hK hLK hKa => ?_⟩
  · rw [normIdeal, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hQ x hx
  · have hKQ : ∀ x ∈ K, Q x ∈ a := fun x hx => hKa (Q_mem_normIdeal Q hx)
    have hKE : IsAEven Q a K := (lemma_4_4 Q a K).2 hKQ
    have hKv : IsHValued Q a K := remark_4_2 Q hKE
    by_contra hne
    have hKL : ¬ K ≤ L := fun h' => hne (le_antisymm h' hLK)
    have hI : L.colon (K : Set V) ≠ ⊤ := fun hI => hKL fun x hx => by
      have : (1 : R) ∈ L.colon (K : Set V) := hI ▸ Submodule.mem_top
      simpa using Submodule.mem_colon.1 this x hx
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal _ hI
    rcases exists_smul_le_or hq hL hK hLK with ⟨s, hs, hsK⟩ | ⟨z, hzK, hzL, hqz⟩
    · exact hs (hIq (Submodule.mem_colon.2 hsK))
    · have hle : L ⊔ span R {z} ≤ K := sup_le hLK ((Submodule.span_singleton_le_iff_mem _ _).2 hzK)
      exact (h q).not_sup Q hzL hqz (hKv.mono Q hle) fun x hx => le_locAt q _ (hKE x (hle hx))

/-! ### The algorithm -/

open scoped Classical in
/-- **Algorithm 4.6, step 2, at one prime** $\mathfrak p$ (Hanke 2013, p. 16), as a Lean definition: if $L$ is $\mathfrak a$-valued for
$H$ and not $\mathfrak a$-even at $\mathfrak p$, replace $L$ by a $\mathfrak p$-neighbour (`IsHPNeighbor`) that is a lattice and is
$\mathfrak a$-even at $\mathfrak p$ if there is one (chosen), and otherwise by $L^{\mathfrak a\text{-even at }\mathfrak p}$; else leave $L$ unchanged.
(The paper finds the neighbours with Theorem 5.6; here the step is the choice it makes.) *Update:* here $L$ is
not an $\mathfrak a$-valued quadratic lattice, so the neighbours are those of Definition 5.1 (corrected) read for the Hessian
form (`IsHPNeighbor`). -/
@[kb "hanke2013algorithms" "Algorithm 4.6, step 2, p. 16"]
def alg46Step (a : Submodule R F) (p : Ideal R) [hp : p.IsPrime] (L : Submodule R V) : Submodule R V :=
  if hL : IsHValued Q a L then
    if IsAEvenAt Q a p L then L
    else if h : ∃ L' : Submodule R V, L'.IsLattice F ∧ IsHPNeighbor Q a p L L' ∧ IsAEvenAt Q a p L' then
      h.choose
    else evenAtSub Q p hL
  else L

/-- **Algorithm 4.6** (Hanke 2013, pp. 16–17), as a Lean definition: starting from a lattice $L$ (in step 1, an
$\mathfrak a$-maximal lattice of the Hessian space, Algorithm 3.16), apply step 2 (`alg46Step`) at the primes of the list $S$
in turn. -/
@[kb "hanke2013algorithms" "Algorithm 4.6, pp. 16–17"]
def algorithm46 (a : Submodule R F) (S : List {p : Ideal R // p.IsMaximal}) (L : Submodule R V) :
    Submodule R V :=
  S.foldl (fun L p => alg46Step Q a p.1 (hp := p.2.isPrime) L) L

/-- **Correctness of one round of step 2** (Hanke 2013, Algorithm 4.6, proof, pp. 16–17): for a lattice $L$ that is
$\mathfrak a$-maximal at $\mathfrak p$ ($2\notin\mathfrak p^2$), `alg46Step` returns a lattice that is $\mathfrak a$-valued for $H$, maximal
$\mathfrak a$-even at $\mathfrak p$, and agrees with $L$ at every other maximal ideal. -/
@[kb "hanke2013algorithms" "Algorithm 4.6, proof, pp. 16–17 (one round of step 2)"]
theorem alg46Step_spec (hR : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I))
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    {p : Ideal R} [hp : p.IsMaximal] (h22 : (2 : R) ∉ p ^ 2) {L : Submodule R V} (hL : L.IsLattice F)
    (hLm : IsHMaximalAt Q a p L) :
    (alg46Step Q a p L).IsLattice F ∧ IsHValued Q a (alg46Step Q a p L) ∧ IsMaxEvenAt Q a p (alg46Step Q a p L) ∧
      ∀ q : Ideal R, q.IsMaximal → q ≠ p → AgreeAt q L (alg46Step Q a p L) := by
  classical
  unfold alg46Step
  split_ifs with h0 he h
  · exact ⟨hL, hLm.1, hLm.isMaxEvenAt Q he, fun q hq _ => AgreeAt.refl hq.ne_top L⟩
  · obtain ⟨hl, hN, hE⟩ := h.choose_spec
    obtain ⟨-, hmax, hag⟩ := step_neighbor Q hR hV ha ha0 h22 hL hLm he hl hN hE
    exact ⟨hl, hN.valued', hmax, hag⟩
  · push Not at h
    obtain ⟨hl, hmax, hag⟩ := step_no_neighbor Q hR hV ha ha0 h22 hL hLm he fun L' h1 h2 => h L' h1 h2
    exact ⟨hl, hmax.1, hmax, hag⟩
  · exact absurd hLm.1 h0

/-- The invariant of the loop of Algorithm 4.6 after the primes `done`. -/
def Alg46Inv (a : Submodule R F) (L₀ : Submodule R V) (done : List {p : Ideal R // p.IsMaximal})
    (L : Submodule R V) : Prop :=
  L.IsLattice F ∧ IsHValued Q a L ∧
    ∀ q : {p : Ideal R // p.IsMaximal},
      (q ∈ done → haveI := q.2.isPrime; IsMaxEvenAt Q a q.1 L) ∧ (q ∉ done → AgreeAt q.1 L₀ L)

theorem alg46Inv_foldl (hR : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I))
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    (h22 : ∀ p : Ideal R, p.IsMaximal → (2 : R) ∉ p ^ 2) {L₀ : Submodule R V}
    (hL₀m : IsAMaximal ((2 : F) • Q) a L₀) :
    ∀ (S done : List {p : Ideal R // p.IsMaximal}) (L : Submodule R V), S.Nodup → (∀ p ∈ S, p ∉ done) →
      Alg46Inv Q a L₀ done L → Alg46Inv Q a L₀ (done ++ S) (algorithm46 Q a S L) := by
  intro S
  induction S with
  | nil => intro done L _ _ h; simpa [algorithm46] using h
  | cons p S ih =>
    intro done L hnd hdis hinv
    obtain ⟨hp, hpS⟩ := p
    have hpd : (⟨hp, hpS⟩ : {p : Ideal R // p.IsMaximal}) ∉ done := hdis _ List.mem_cons_self
    have := hpS
    obtain ⟨hLl, hLv, hq⟩ := hinv
    have hLm : IsHMaximalAt Q a hp L :=
      ((hq ⟨hp, hpS⟩).2 hpd).isHMaximalAt Q hpS hLv (isHMaximalAt_of_isAMaximal Q hp hL₀m)
    obtain ⟨h1l, h1v, h1m, h1a⟩ := alg46Step_spec Q hR hV ha ha0 (h22 hp hpS) hLl hLm
    have hinv' : Alg46Inv Q a L₀ (done ++ [⟨hp, hpS⟩]) (alg46Step Q a hp L) := by
      refine ⟨h1l, h1v, fun q => ⟨fun hqd => ?_, fun hqd => ?_⟩⟩
      · rcases List.mem_append.1 hqd with hqd | hqd
        · have hqp : q.1 ≠ hp := fun h => hpd (by
            have e : q = ⟨hp, hpS⟩ := Subtype.ext h
            exact e ▸ hqd)
          have := q.2.isPrime
          exact (h1a q.1 q.2 hqp).isMaxEvenAt Q q.2 h1v ((hq q).1 hqd)
        · rw [List.mem_singleton] at hqd
          subst hqd
          exact h1m
      · have hqp : q.1 ≠ hp := fun h => hqd (List.mem_append_right _ (by
          rw [List.mem_singleton]; exact Subtype.ext h))
        have hqd' : q ∉ done := fun h => hqd (List.mem_append_left _ h)
        have := q.2.isPrime
        exact ((hq q).2 hqd').trans (h1a q.1 q.2 hqp)
    have := ih (done ++ [⟨hp, hpS⟩]) (alg46Step Q a hp L) (List.nodup_cons.1 hnd).2
      (fun x hx hx' => by
        rcases List.mem_append.1 hx' with h | h
        · exact hdis x (List.mem_cons_of_mem _ hx) h
        · rw [List.mem_singleton] at h; subst h; exact (List.nodup_cons.1 hnd).1 hx) hinv'
    simpa [algorithm46, List.foldl_cons] using this

/-- **Algorithm 4.6 is correct** (Hanke 2013, pp. 16–17). Let $R$ be a Dedekind domain with fraction field $F$ and finite
quotients $R/I$ ($I\ne0$), in which $2$ is unramified ($2\notin\mathfrak p^2$ for all maximal $\mathfrak p$; for $R = \mathcal O_F$ of a number
field: "$p = 2$ is unramified in $F$"), $(V, Q)$ a non-degenerate quadratic space over $F$ and $\mathfrak a$ a non-zero fractional
ideal. Let $L_0$ be an $\mathfrak a$-maximal lattice of the Hessian bilinear space $(V, H)$ (step 1, Algorithm 3.16;
`exists_isAMaximal`), and $S$ a list without repetitions containing every maximal ideal at which $L_0$ is not $\mathfrak a$-even
(the paper's finite set $S$; all such primes divide $2$, `two_mem_of_not_isAEvenAt`). Then the output
`algorithm46 Q a S L₀` of step 2 is a maximal $\mathfrak a$-valued quadratic lattice on $(V, Q)$. -/
@[kb "hanke2013algorithms" "Algorithm 4.6, pp. 16–17 (correctness)"]
theorem algorithm_4_6 (hR : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I))
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    (h22 : ∀ p : Ideal R, p.IsMaximal → (2 : R) ∉ p ^ 2) {L₀ : Submodule R V} (hL₀ : L₀.IsLattice F)
    (hL₀m : IsAMaximal ((2 : F) • Q) a L₀) (S : List {p : Ideal R // p.IsMaximal}) (hS : S.Nodup)
    (hSc : ∀ (p : Ideal R) [hp : p.IsMaximal], ¬ IsAEvenAt Q a p L₀ → ⟨p, hp⟩ ∈ S) :
    IsMaximal Q a (algorithm46 Q a S L₀) := by
  have hL₀v := (isAValued_two_smul_iff Q).1 hL₀m.1
  have h0 : Alg46Inv Q a L₀ [] L₀ :=
    ⟨hL₀, hL₀v, fun q => ⟨fun h => absurd h List.not_mem_nil, fun _ => AgreeAt.refl q.2.ne_top L₀⟩⟩
  obtain ⟨hl, hv, hq⟩ := alg46Inv_foldl Q hR hV ha ha0 h22 hL₀m S [] L₀ hS (fun _ _ h => List.not_mem_nil h) h0
  refine isMaximal_of_forall_isMaxEvenAt Q hl hv fun q hqm => ?_
  by_cases hqS : (⟨q, hqm⟩ : {p : Ideal R // p.IsMaximal}) ∈ [] ++ S
  · exact (hq ⟨q, hqm⟩).1 hqS
  · have hag := (hq ⟨q, hqm⟩).2 hqS
    have he : IsAEvenAt Q a q L₀ := by
      by_contra he
      exact hqS (by simpa using hSc q he)
    exact hag.isMaxEvenAt Q hqm hv ((isHMaximalAt_of_isAMaximal Q q hL₀m).isMaxEvenAt Q he)

/-- **The set $S$ of Algorithm 4.6, step 1, is finite** (Hanke 2013, p. 16: "Let $S$ be the finite set of primes $\mathfrak p$
where $L$ is not $\mathfrak a$-even at $\mathfrak p$"): there is a list without repetitions containing every maximal ideal at which
an $\mathfrak a$-valued $L$ is not $\mathfrak a$-even (these divide $2$, and only finitely many primes divide $2\ne0$). -/
@[kb "hanke2013algorithms" "Algorithm 4.6, step 1, p. 16 (S is finite)"]
theorem exists_list_not_isAEvenAt {a : Submodule R F} {L : Submodule R V} (hL : IsHValued Q a L) :
    ∃ S : List {p : Ideal R // p.IsMaximal}, S.Nodup ∧
      ∀ (p : Ideal R) [hp : p.IsMaximal], ¬ IsAEvenAt Q a p L → ⟨p, hp⟩ ∈ S := by
  have h20 : Ideal.span {(2 : R)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact two_ne_zero_R F
  set X : Set (Ideal R) := IsDedekindDomain.HeightOneSpectrum.asIdeal ''
    {v : IsDedekindDomain.HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {(2 : R)}}
  have hX : X.Finite := (Ideal.finite_factors h20).image _
  set T : Set {p : Ideal R // p.IsMaximal} := {p | (2 : R) ∈ p.1}
  have hT : T.Finite := by
    refine (hX.preimage Subtype.val_injective.injOn).subset fun p hp => ?_
    have hp0 : p.1 ≠ ⊥ := fun h => two_ne_zero_R F (by
      have : (2 : R) ∈ p.1 := hp
      rwa [h, Ideal.mem_bot] at this)
    refine ⟨⟨p.1, p.2.isPrime, hp0⟩, ?_, rfl⟩
    show p.1 ∣ Ideal.span {(2 : R)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hp
  refine ⟨hT.toFinset.toList, Finset.nodup_toList _, fun p hp hnot => ?_⟩
  rw [Finset.mem_toList, Set.Finite.mem_toFinset]
  exact two_mem_of_not_isAEvenAt Q hL hnot

/-- **Algorithm 4.6, steps 1–3 together** (Hanke 2013, pp. 16–17): for an $\mathfrak a$-maximal lattice $L_0$ of the Hessian space
, the finite set $S$ exists (`exists_list_not_isAEvenAt`) and step 2 over $S$ outputs a maximal $\mathfrak a$-valued
quadratic lattice (`algorithm_4_6`). -/
@[kb "hanke2013algorithms" "Algorithm 4.6, pp. 16–17 (steps 1–3)"]
theorem algorithm_4_6_run (hR : ∀ I : Ideal R, I ≠ ⊥ → Finite (R ⧸ I))
    (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥)
    (h22 : ∀ p : Ideal R, p.IsMaximal → (2 : R) ∉ p ^ 2) {L₀ : Submodule R V} (hL₀ : L₀.IsLattice F)
    (hL₀m : IsAMaximal ((2 : F) • Q) a L₀) :
    ∃ S : List {p : Ideal R // p.IsMaximal}, S.Nodup ∧
      (∀ (p : Ideal R) [hp : p.IsMaximal], ¬ IsAEvenAt Q a p L₀ → ⟨p, hp⟩ ∈ S) ∧
      IsMaximal Q a (algorithm46 Q a S L₀) := by
  obtain ⟨S, hS, hSc⟩ := exists_list_not_isAEvenAt Q ((isAValued_two_smul_iff Q).1 hL₀m.1)
  exact ⟨S, hS, hSc, algorithm_4_6 Q hR hV ha ha0 h22 hL₀ hL₀m S hS hSc⟩

/-- **The neighbour search of step 2 is over the $\eta(P)$** (Hanke 2013, Algorithm 4.6, step 2, "we use Theorem 5.6"): every
$\mathfrak p$-neighbour $L'$ of $L$ in the Hessian space (`IsHPNeighbor`, $\mathfrak p\ne0$ with finite residue field) is
$\eta(P) = L'' + \mathfrak p^{-1}\vec v_P$ for some $\vec v_P\in L\setminus\mathfrak pL$ whose point is non-singular; if $L'$ is
$\mathfrak a$-even at $\mathfrak p$, then $Q(\vec v_P)\in(\mathfrak p^2\mathfrak a)_{\mathfrak p}$ (the local form of Theorem 5.6's condition
$Q(\vec v_P)\in\mathfrak p^2\mathfrak a$). Proof: `theorem_5_6_surjective_gen`, $\vec v_P = c\vec v'$, $Q(\vec v_P) = c^2Q(\vec v')$. -/
@[kb "hanke2013algorithms" "Algorithm 4.6, step 2, p. 16 (the p-neighbours are η(P), Theorem 5.6)"]
theorem isHPNeighbor_eq_nbLatP {a : Submodule R F} {p : Ideal R} [hp : p.IsMaximal] (hp0 : p ≠ ⊥)
    [Finite (R ⧸ p)] {L L' : Submodule R V} (hN : IsHPNeighbor Q a p L L') :
    ∃ v ∈ L, v ∉ p • L ∧ (IsAEvenAt Q a p L' → Q v ∈ locAt p (p • p • a)) ∧
      ¬ IsSingularPoint Q a p L v ∧ nbLatP Q a p L v = L' := by
  obtain ⟨c, hc, -, v', hv', hvL, hvp, hns, heq⟩ := theorem_5_6_surjective_gen Q hp hp0 hN.valued hN.valued'
    hN.index hN.index' hN.smul_le hN.smul_le' hN.not_valued
  refine ⟨c • v', hvL, hvp, fun he => ?_, hns, heq⟩
  obtain ⟨t, ht, htv⟩ := he v' hv'
  refine ⟨t, ht, ?_⟩
  have hQ : t • Q v' ∈ a := by
    have e : t • polar Q v' v' = 2 * (t • Q v') := by
      rw [polar_self, nsmul_eq_mul, Nat.cast_ofNat, Algebra.smul_def, Algebra.smul_def]; ring
    rw [e, mem_twoA, ← mul_assoc, invOf_mul_self, one_mul] at htv
    exact htv
  have e : t • Q (c • v') = c • c • (t • Q v') := by
    rw [Q_rsmul]; simp only [Algebra.smul_def]; ring
  rw [e]
  exact Submodule.smul_mem_smul hc (Submodule.smul_mem_smul hc hQ)

end Dedekind

end QuadFormsKB.Hanke2013Algorithms
