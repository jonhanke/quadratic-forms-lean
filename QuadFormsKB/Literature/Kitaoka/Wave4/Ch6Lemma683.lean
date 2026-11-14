/-
# Kitaoka 1993, Lemmas 6.8.3 and 6.8.4: glue maps and primitive representations

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §6.8, Lemma 6.8.3 (p. 176) and Lemma 6.8.4
(p. 177), printed pages, in the proof of the Minkowski–Siegel formula (Theorem 6.8.1).

**Book statements.** Keep condition (*) of §6.8. Let $\Phi$ be the set of linear maps $\varphi : K \to FM/M$ such that
there is an isometry $\sigma : N_\varphi \cong N$ (where $N_\varphi = M + R[x + \varphi(x) \mid x \in K]$, Lemma 6.8.1),
and $I$ the set of isometries $\eta : M \to N$ such that $\eta(M)$ is primitive in $N$ and
$\mathrm{proj}_{\eta(M)^\perp} N \cong K$. **Lemma 6.8.3.** The map $\xi : (\varphi, \sigma) \mapsto \sigma|_M$ from
$\bigsqcup_{\varphi \in \Phi}\{\sigma : N_\varphi \cong N\}$ to $I$ is surjective, and
$\xi(\varphi_1, \sigma_1) = \xi(\varphi_2, \sigma_2)$ if and only if $\varphi_1 = \varphi_2\alpha$ and
$\sigma_1 = \sigma_2(\mathrm{id}_M \perp \alpha)$ for some $\alpha \in O(K)$. **Lemma 6.8.4.** For $R = \mathbb Z$ and
$\mathbb QN$ positive definite,
$E(N)^{-1}\#\{\sigma : M \to N \mid \sigma(M) \text{ primitive in } N,\ \mathrm{proj}_{\sigma(M)^\perp} N \cong K\}
= E(K)^{-1}\#\{\varphi : K \to \mathbb QM/M \mid N_\varphi \cong N\}$, with $E(L) = \#O(L)$.

**Setting and encoding.** As in `Wave3/Ch6Lemma681.lean` and `Ch6Lemma682.lean`: $(V, Q)$ is a regular quadratic
space over $F$ (hypothesis `hreg`), $V = W \oplus W'$ with $W = FM$, $W' = FK$ orthogonal (`hperp`), $M \subseteq W$ and
$K \subseteq W'$ are $R$-submodules, $N$ is an $R$-submodule of $V$.
* An isometry of lattices is the restriction of an isometry of the spaces they span (O'Meara's definition, §82A, as
  in `OMeara.IsometricLat`). So an isometry $\sigma : N_\varphi \cong N$ is an element $\sigma$ of $O(V)$
  (`OMeara.orth Q`) with $\sigma(N_\varphi) = N$; $\Psi = \bigsqcup_{\varphi \in \Phi}\{\sigma : N_\varphi \cong N\}$ is
  `glueIsoSet` (pairs $(\varphi, \sigma)$) and $\Phi$ is `glueSet`.
* An element $\eta$ of $I$ is an $F$-linear isometric map $\tau : W \to V$ (`embSet`) with $\tau(M) \subseteq N$,
  $N \cap \tau(W) \subseteq \tau(M)$ ($\tau(M)$ primitive in $N$), together with an isometric $\alpha : W' \to V$ with
  $B(\tau W, \alpha W') = 0$ and $\tau(W) + \alpha(W') = V$ (so $\alpha(W') = \tau(W)^\perp$), such that
  $\mathrm{proj}_{\tau(W)^\perp} N = \alpha(K)$, i.e. for $x \in W'$: $x \in K$ iff $\tau(w) + \alpha(x) \in N$ for some
  $w \in W$. Then $\alpha|_K$ is the isometry $K \cong \mathrm{proj}_{\eta(M)^\perp} N$.
* $O(K)$ is realized as $\{g \in O(V) \mid g|_W = \mathrm{id},\ g(K) = K\}$ (`orthK`): these are exactly the maps
  $\mathrm{id}_M \perp \alpha$ with $\alpha \in O(K)$ (an isometry fixing $W$ preserves $W^\perp = W'$). The composite
  $\varphi\alpha$ is `φ.comp (restrK g)`.
* $\xi(\varphi, \sigma) = \sigma|_W$ (`xi`).

**Proves**
* `xi_mem_embSet`, `xi_surjective` and `xi_eq_iff` (Lemma 6.8.3, `lemma683`);
* `lemma684_card`: $\#I \cdot \#O(K) = \#\Phi \cdot \#O(N)$ as cardinals (`Nat.card`, so $0$ for infinite sets), with
  no definiteness assumption; and `lemma684` (Lemma 6.8.4): if $O(N)$ and $O(K)$ are finite (true for positive definite
  lattices over $\mathbb Z$, Kitaoka's hypothesis), then $\#O(N)^{-1}\#I = \#O(K)^{-1}\#\Phi$.

All results are unconditional (no named input hypotheses).
-/
import QuadFormsKB.Literature.Kitaoka.Wave4.Ch6Lemma682
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

noncomputable section

open QuadraticMap Submodule Module
open QuadFormsKB.OMeara (bil orth orthLat latMap bil_comm bil_add_left bil_add_right bil_sub_left bil_sub_right)

namespace QuadFormsKB.Kitaoka.Glue

variable {R F V : Type*} [CommRing R] [Field F] [Algebra R F] [Invertible (2 : F)] [AddCommGroup V] [Module F V]
  [Module R V] [IsScalarTower R F V]
variable {Q : QuadraticForm F V} {W W' : Submodule F V} {hc : IsCompl W W'} {M N K : Submodule R V}

/-! ### Preliminaries -/

/-- An element of $O(V)$ preserves $B$. -/
theorem bil_orth {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (x y : V) : bil Q (σ x) (σ y) = bil Q x y := by
  have h : ∀ v, Q (σ v) = Q v := hσ
  simp only [bil, QuadraticMap.associated_apply, ← map_add, h]

/-- An $F$-linear map with $Q(f x) = Q(x)$ preserves $B$. -/
theorem bil_isom {U : Type*} [AddCommGroup U] [Module F U] {QU : QuadraticForm F U} {f : U →ₗ[F] V}
    (hf : ∀ x, Q (f x) = QU x) (x y : U) : bil Q (f x) (f y) = bil QU x y := by
  simp only [bil, QuadraticMap.associated_apply, ← map_add, hf]

theorem projK_add (w x : V) (hw : w ∈ W) (hx : x ∈ W') : projK R W W' hc (w + x) = x := by
  rw [map_add, (projK_eq_zero_iff (R := R) W W' hc w).mpr hw, zero_add, projK_of_mem' hx]

theorem projM_add (w x : V) (hw : w ∈ W) (hx : x ∈ W') :
    ((projM R W W' hc (w + x) : W.restrictScalars R) : V) = w := by
  have h := projM_add_projK R W W' hc (w + x)
  rw [projK_add w x hw hx] at h
  exact add_right_cancel h

/-- Membership in $N_\varphi$ of $w + x$ with $w \in W$, $x \in W'$: $x \in K$ and $w \equiv \varphi(x)$ modulo $M$. -/
theorem add_mem_glueLat_iff (φ : K →ₗ[R] glueTarget W M) {w x : V} (hw : w ∈ W) (hx : x ∈ W') :
    w + x ∈ glueLat hc K φ ↔
      ∃ hxK : x ∈ K, (Submodule.Quotient.mk (⟨w, hw⟩ : W.restrictScalars R) : glueTarget W M) = φ ⟨x, hxK⟩ := by
  rw [mem_glueLat, GlueCond]
  have e1 := projK_add (hc := hc) (R := R) w x hw hx
  have e2 : projM R W W' hc (w + x) = ⟨w, hw⟩ := Subtype.ext (projM_add w x hw hx)
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨by rw [← e1]; exact h, ?_⟩
    rw [← e2, h']
    congr 1; exact Subtype.ext e1
  · rintro ⟨h, h'⟩
    refine ⟨by rw [e1]; exact h, ?_⟩
    rw [e2, h']
    congr 1; exact Subtype.ext e1.symm

theorem mem_glueLat_of_mem_W_iff (hMW : M ≤ W.restrictScalars R) (φ : K →ₗ[R] glueTarget W M) {w : V}
    (hw : w ∈ W) : w ∈ glueLat hc K φ ↔ w ∈ M := by
  have := add_mem_glueLat_iff (hc := hc) φ hw W'.zero_mem
  rw [add_zero] at this
  rw [this]
  constructor
  · rintro ⟨h0, h⟩
    have e : (⟨0, h0⟩ : K) = 0 := rfl
    rw [e, map_zero, Submodule.Quotient.mk_eq_zero] at h
    exact h
  · intro h
    refine ⟨K.zero_mem, ?_⟩
    have e : (⟨0, K.zero_mem⟩ : K) = 0 := rfl
    rw [e, map_zero, Submodule.Quotient.mk_eq_zero]
    exact h

theorem exists_add_mem_glueLat_iff (φ : K →ₗ[R] glueTarget W M) {x : V} (hx : x ∈ W') :
    (∃ w ∈ W, w + x ∈ glueLat hc K φ) ↔ x ∈ K := by
  constructor
  · rintro ⟨w, hw, h⟩
    exact ((add_mem_glueLat_iff φ hw hx).mp h).1
  · intro hxK
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (φ ⟨x, hxK⟩)
    exact ⟨w, w.2, (add_mem_glueLat_iff φ w.2 hx).mpr ⟨hxK, hw⟩⟩

theorem mem_latMap_iff {σ : V ≃ₗ[F] V} {L : Submodule R V} {y : V} : y ∈ latMap σ L ↔ σ.symm y ∈ L := by
  constructor
  · rintro ⟨v, hv, rfl⟩; simpa using hv
  · intro h; exact ⟨σ.symm y, h, by simp⟩

/-- Every $v \in V$ is $w + x$ with $w \in W$, $x \in W'$. -/
theorem exists_decomp (hc : IsCompl W W') (v : V) : ∃ w ∈ W, ∃ x ∈ W', v = w + x :=
  ⟨_, Submodule.projection_apply_mem hc v, _, Submodule.projection_apply_mem hc.symm v,
    (Submodule.projection_add_projection_eq_self hc v).symm⟩

/-- With $V$ regular and $V = W \oplus W'$, $W \perp W'$: a vector orthogonal to $W$ lies in $W'$. -/
theorem mem_W'_of_orth (hc : IsCompl W W') (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0) (hreg : ∀ v, (∀ u, bil Q v u = 0) → v = 0)
    {v : V} (hv : ∀ w ∈ W, bil Q v w = 0) : v ∈ W' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp hc v
  have : a = 0 := by
    apply hreg
    intro u
    obtain ⟨c, hc', d, hd, rfl⟩ := exists_decomp hc u
    rw [bil_add_right, hperp a ha d hd, add_zero]
    have h1 := hv c hc'
    rw [bil_add_left, bil_comm Q b c, hperp c hc' b hb, add_zero] at h1
    exact h1
  rw [this, zero_add]; exact hb

/-! ### $O(K)$, $\Phi$, $\Psi$ and $I$ -/

variable (Q W K) in
/-- **$O(K)$, realized inside $O(V)$** (Kitaoka 1993, Lemma 6.8.3, p. 176: the maps $\mathrm{id}_M \perp \alpha$,
$\alpha \in O(K)$): the isometries $g$ of $V$ which fix $W = FM$ pointwise and satisfy $g(K) = K$. -/
def orthK : Subgroup (V ≃ₗ[F] V) := orthLat Q K ⊓ fixingSubgroup (V ≃ₗ[F] V) (W : Set V)

theorem orthK_fix {g : V ≃ₗ[F] V} (hg : g ∈ orthK Q W K) {w : V} (hw : w ∈ W) : g w = w :=
  (mem_fixingSubgroup_iff _).mp hg.2 w hw

theorem orthK_orth {g : V ≃ₗ[F] V} (hg : g ∈ orthK Q W K) : g ∈ orth Q := hg.1.1

theorem orthK_mapsTo {g : V ≃ₗ[F] V} (hg : g ∈ orthK Q W K) {x : V} (hx : x ∈ K) : g x ∈ K := by
  have : g x ∈ latMap g K := ⟨x, hx, rfl⟩
  rwa [hg.1.2] at this

theorem orthK_mapsTo_W' (hc : IsCompl W W') (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0) (hreg : ∀ v, (∀ u, bil Q v u = 0) → v = 0)
    {g : V ≃ₗ[F] V} (hg : g ∈ orthK Q W K) {x : V} (hx : x ∈ W') : g x ∈ W' := by
  apply mem_W'_of_orth hc hperp hreg
  intro w hw
  rw [← orthK_fix hg hw, bil_orth (orthK_orth hg), bil_comm]
  exact hperp w hw x hx

/-- The restriction $\alpha = g|_K \in O(K)$ of $g \in$ `orthK`. -/
def restrK (g : orthK Q W K) : K →ₗ[R] K :=
  ((g.1 : V →ₗ[F] V).restrictScalars R).restrict fun _ hx => orthK_mapsTo g.2 hx

@[simp] theorem restrK_apply (g : orthK Q W K) (x : K) : (restrK g x : V) = g.1 x := rfl

variable (Q hc M N K) in
/-- **$\Psi = \bigsqcup_{\varphi \in \Phi} \{\sigma : N_\varphi \cong N\}$** (Kitaoka 1993, Lemma 6.8.3, p. 176): pairs
$(\varphi, \sigma)$ of a linear $\varphi : K \to FM/M$ and an isometry $\sigma \in O(V)$ with $\sigma(N_\varphi) = N$. -/
def glueIsoSet : Set ((K →ₗ[R] glueTarget W M) × (V ≃ₗ[F] V)) :=
  {p | p.2 ∈ orth Q ∧ latMap p.2 (glueLat hc K p.1) = N}

variable (Q hc M N K) in
/-- **$\Phi$** (Kitaoka 1993, Lemma 6.8.3, p. 176): the linear maps $\varphi : K \to FM/M$ with $N_\varphi \cong N$. -/
def glueSet : Set (K →ₗ[R] glueTarget W M) :=
  {φ | ∃ σ ∈ orth Q, latMap σ (glueLat hc K φ) = N}

variable (Q W W' M N K) in
/-- **$I$** (Kitaoka 1993, Lemma 6.8.3, p. 176): the isometries $\eta : M \to N$ with $\eta(M)$ primitive in $N$ and
$\mathrm{proj}_{\eta(M)^\perp} N \cong K$, encoded as $F$-linear isometric maps $\tau : W = FM \to V$ (see the module
docstring): $\tau(M) \subseteq N$, $N \cap \tau(W) \subseteq \tau(M)$, and there is an isometric
$\alpha : W' = FK \to V$ onto $\tau(W)^\perp$ ($B(\tau W, \alpha W') = 0$, $\tau(W) + \alpha(W') = V$) with
$\mathrm{proj}_{\tau(W)^\perp} N = \alpha(K)$. -/
def embSet : Set (W →ₗ[F] V) :=
  {τ | (∀ w, Q (τ w) = Q w) ∧ (∀ w : W, (w : V) ∈ M → τ w ∈ N) ∧ (∀ w : W, τ w ∈ N → (w : V) ∈ M) ∧
    ∃ α : W' →ₗ[F] V, (∀ x, Q (α x) = Q x) ∧ (∀ w x, bil Q (τ w) (α x) = 0) ∧
      (∀ v, ∃ w x, v = τ w + α x) ∧ ∀ x : W', (x : V) ∈ K ↔ ∃ w, τ w + α x ∈ N}

/-- **The map $\xi$** of Lemma 6.8.3: $(\varphi, \sigma) \mapsto \sigma|_M$ (here $\sigma|_{FM}$). -/
def xi (p : (K →ₗ[R] glueTarget W M) × (V ≃ₗ[F] V)) : W →ₗ[F] V := (p.2 : V →ₗ[F] V) ∘ₗ W.subtype

/-! ### Lemma 6.8.3 -/

variable (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0) (hreg : ∀ v, (∀ u, bil Q v u = 0) → v = 0)
  (hMW : M ≤ W.restrictScalars R) (hKW : K ≤ W'.restrictScalars R)

include hperp hMW hKW in
/-- $\xi$ maps $\Psi$ into $I$ (Kitaoka 1993, proof of Lemma 6.8.3, p. 176: $\xi$ is well defined). -/
theorem xi_mem_embSet {p : (K →ₗ[R] glueTarget W M) × (V ≃ₗ[F] V)} (hp : p ∈ glueIsoSet Q hc M N K) :
    xi p ∈ embSet Q W W' M N K := by
  obtain ⟨hσ, hN⟩ := hp
  set σ := p.2
  have hmem : ∀ v, σ v ∈ N ↔ v ∈ glueLat hc K p.1 := fun v => by
    rw [← hN, mem_latMap_iff]; simp
  refine ⟨fun w => hσ w, fun w hw => (hmem w).mpr ((mem_glueLat_of_mem_W_iff hMW p.1 w.2).mpr hw),
    fun w hw => (mem_glueLat_of_mem_W_iff hMW p.1 w.2).mp ((hmem w).mp hw), (σ : V →ₗ[F] V) ∘ₗ W'.subtype,
    fun x => hσ x, fun w x => show bil Q (σ w) (σ x) = 0 by rw [bil_orth hσ]; exact hperp w w.2 x x.2,
    fun v => ?_, fun x => ?_⟩
  · obtain ⟨w, hw, x, hx, h⟩ := exists_decomp hc (σ.symm v)
    refine ⟨⟨w, hw⟩, ⟨x, hx⟩, ?_⟩
    show v = σ w + σ x
    rw [← map_add, ← h]; simp
  · show (x : V) ∈ K ↔ ∃ w : W, σ w + σ x ∈ N
    simp only [← map_add, hmem]
    rw [← exists_add_mem_glueLat_iff (hc := hc) p.1 x.2]
    exact ⟨fun ⟨w, hw, h⟩ => ⟨⟨w, hw⟩, h⟩, fun ⟨w, h⟩ => ⟨w, w.2, h⟩⟩

include hperp hreg in
/-- An isometric $\tau : W \to V$ is injective ($V$ regular, $W \perp W'$). -/
theorem injective_of_isom (hc : IsCompl W W') {τ : W →ₗ[F] V} (hτ : ∀ w, Q (τ w) = Q w) : Function.Injective τ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  apply Subtype.ext
  apply hreg
  intro u
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp hc u
  rw [bil_add_right, hperp w w.2 b hb, add_zero]
  have := bil_isom (QU := Q.comp W.subtype) (f := τ) (fun x => hτ x) w ⟨a, ha⟩
  rw [hw] at this
  simp only [bil, QuadraticMap.associated_apply, map_zero, zero_add, sub_self, zero_sub] at this
  simp only [bil, QuadraticMap.associated_apply, QuadraticMap.comp_apply, Submodule.coe_subtype,
    Submodule.coe_add] at this ⊢
  rw [← this]; simp

include hperp hreg in
/-- From $\tau \in I$ with its $\alpha$, the isometry $\sigma = \tau \perp \alpha$ of $V$ (Kitaoka 1993, proof of
Lemma 6.8.3: $\sigma := \eta \perp \alpha$). -/
theorem exists_orth_of_embSet (hc : IsCompl W W') {τ : W →ₗ[F] V} (hτ : ∀ w, Q (τ w) = Q w) {α : W' →ₗ[F] V}
    (hα : ∀ x, Q (α x) = Q x) (horth : ∀ w x, bil Q (τ w) (α x) = 0) (hspan : ∀ v, ∃ w x, v = τ w + α x) :
    ∃ σ ∈ orth Q, (∀ w : W, σ w = τ w) ∧ ∀ x : W', σ x = α x := by
  set f : V →ₗ[F] V := τ ∘ₗ W.projectionOnto W' hc + α ∘ₗ W'.projectionOnto W hc.symm
  have hfW : ∀ w : W, f w = τ w := fun w => by
    simp [f, Submodule.projectionOnto_apply_left, Submodule.projectionOnto_apply_right]
  have hfW' : ∀ x : W', f x = α x := fun x => by
    simp [f, Submodule.projectionOnto_apply_left, Submodule.projectionOnto_apply_right]
  have hfdec : ∀ (w : W) (x : W'), f (w + x) = τ w + α x := fun w x => by rw [map_add, hfW, hfW']
  have hQ : ∀ v, Q (f v) = Q v := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp hc v
    rw [show a + b = ((⟨a, ha⟩ : W) : V) + ((⟨b, hb⟩ : W') : V) from rfl, hfdec]
    rw [← OMeara.bil_self Q, ← OMeara.bil_self Q (a + b), bil_add_left, bil_add_right, bil_add_right,
      bil_add_left, bil_add_right, bil_add_right, horth, bil_comm Q (α _), horth,
      hperp a ha b hb, bil_comm Q b a, hperp a ha b hb]
    have h1 := bil_isom (QU := Q.comp W.subtype) (f := τ) hτ ⟨a, ha⟩ ⟨a, ha⟩
    have h2 := bil_isom (QU := Q.comp W'.subtype) (f := α) hα ⟨b, hb⟩ ⟨b, hb⟩
    simp only [bil, QuadraticMap.associated_apply, QuadraticMap.comp_apply, Submodule.coe_subtype,
      Submodule.coe_add] at h1 h2 ⊢
    rw [h1, h2]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hreg
    intro u
    obtain ⟨w, x, rfl⟩ := hspan u
    have hb := bil_isom (QU := Q) (f := f) hQ v
    rw [← hb, hv]
    simp [bil]
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨w, x, rfl⟩ := hspan v
    exact ⟨w + x, hfdec w x⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun v => hQ v, fun w => hfW w, fun x => hfW' x⟩

include hperp hreg hMW hKW in
/-- **Kitaoka 1993, Lemma 6.8.3** (p. 176), surjectivity: every $\eta \in I$ is $\xi(\varphi, \sigma)$ for some
$(\varphi, \sigma) \in \Psi$. -/
theorem xi_surjective {τ : W →ₗ[F] V} (hτ : τ ∈ embSet Q W W' M N K) :
    ∃ p ∈ glueIsoSet Q hc M N K, xi p = τ := by
  obtain ⟨hτQ, hτM, hτprim, α, hαQ, horth, hspan, hαK⟩ := hτ
  obtain ⟨σ, hσ, hσW, hσW'⟩ := exists_orth_of_embSet hperp hreg hc hτQ hαQ horth hspan
  set N' := latMap σ.symm N
  have hmem : ∀ v, v ∈ N' ↔ σ v ∈ N := fun v => by rw [mem_latMap_iff]; simp
  have hM' : N' ⊓ W.restrictScalars R = M := by
    ext v
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, hmem]
    constructor
    · rintro ⟨h, hv⟩
      have := hτprim ⟨v, hv⟩ (by rw [← hσW ⟨v, hv⟩]; exact h)
      exact this
    · intro hv
      refine ⟨?_, hMW hv⟩
      rw [show v = ((⟨v, hMW hv⟩ : W) : V) from rfl, hσW]
      exact hτM ⟨v, hMW hv⟩ hv
  have hK' : N'.map (projK R W W' hc) = K := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp hc v
      rw [projK_add a b ha hb]
      rw [SetLike.mem_coe, hmem, map_add, show a = ((⟨a, ha⟩ : W) : V) from rfl, show b = ((⟨b, hb⟩ : W') : V) from rfl,
        hσW, hσW'] at hv
      exact (hαK ⟨b, hb⟩).mpr ⟨_, hv⟩
    · intro hx
      have hxW' := hKW hx
      obtain ⟨w, hw⟩ := (hαK ⟨x, hxW'⟩).mp hx
      refine ⟨(w : V) + x, ?_, projK_add _ _ w.2 hxW'⟩
      rw [SetLike.mem_coe, hmem, map_add, hσW, show x = ((⟨x, hxW'⟩ : W') : V) from rfl, hσW']
      exact hw
  have hglue : glueLat hc K (glueMap hc hM' hK') = N' := by
    ext v; exact (mem_iff_glueCond hc hM' hK' v).symm
  refine ⟨(glueMap hc hM' hK', σ), ⟨hσ, ?_⟩, ?_⟩
  · show latMap σ (glueLat hc K (glueMap hc hM' hK')) = N
    rw [hglue]
    ext y
    rw [mem_latMap_iff, hmem]; simp
  · ext w
    exact hσW w

include hperp hreg hKW in
/-- **Kitaoka 1993, Lemma 6.8.3** (p. 176), fibres of $\xi$: for $(\varphi_1, \sigma_1), (\varphi_2, \sigma_2) \in \Psi$,
$\xi(\varphi_1, \sigma_1) = \xi(\varphi_2, \sigma_2)$ if and only if $\varphi_1 = \varphi_2\alpha$ and
$\sigma_1 = \sigma_2(\mathrm{id}_M \perp \alpha)$ for some $\alpha \in O(K)$ (here $g = \mathrm{id}_M \perp \alpha$ in
`orthK`). -/
theorem xi_eq_iff {p₁ p₂ : (K →ₗ[R] glueTarget W M) × (V ≃ₗ[F] V)} (hp₁ : p₁ ∈ glueIsoSet Q hc M N K)
    (hp₂ : p₂ ∈ glueIsoSet Q hc M N K) :
    xi p₁ = xi p₂ ↔ ∃ g : orthK Q W K, p₁.1 = p₂.1.comp (restrK g) ∧ p₁.2 = p₂.2 * g.1 := by
  constructor
  · intro h
    have hW : ∀ w ∈ W, p₁.2 w = p₂.2 w := fun w hw => LinearMap.congr_fun h ⟨w, hw⟩
    set g : V ≃ₗ[F] V := p₂.2⁻¹ * p₁.2
    have hgorth : g ∈ orth Q := (orth Q).mul_mem ((orth Q).inv_mem hp₂.1) hp₁.1
    have hgW : ∀ w ∈ W, g w = w := fun w hw => by
      simp [g, LinearEquiv.coe_inv, hW w hw]
    -- `g` maps `N_{φ₁}` onto `N_{φ₂}`
    have hgN : ∀ v, v ∈ glueLat hc K p₁.1 ↔ g v ∈ glueLat hc K p₂.1 := fun v => by
      have e1 : v ∈ glueLat hc K p₁.1 ↔ p₁.2 v ∈ N := by rw [← hp₁.2, mem_latMap_iff]; simp
      have e2 : g v ∈ glueLat hc K p₂.1 ↔ p₂.2 (g v) ∈ N := by rw [← hp₂.2, mem_latMap_iff]; simp
      rw [e1, e2]; simp [g]
    have hgW' : ∀ x ∈ W', g x ∈ W' := fun x hx => by
      apply mem_W'_of_orth hc hperp hreg
      intro w hw
      rw [← hgW w hw, bil_orth hgorth, bil_comm]
      exact hperp w hw x hx
    have hgK : ∀ x ∈ K, g x ∈ K := fun x hx => by
      have hxW' := hKW hx
      obtain ⟨w, hw, h⟩ := (exists_add_mem_glueLat_iff (hc := hc) p₁.1 hxW').mpr hx
      rw [hgN, map_add, hgW w hw] at h
      exact (exists_add_mem_glueLat_iff (hc := hc) p₂.1 (hgW' x hxW')).mp ⟨w, hw, h⟩
    have hgK' : ∀ x ∈ K, g⁻¹ x ∈ K := fun x hx => by
      have hxW' := hKW hx
      have hW'inv : g⁻¹ x ∈ W' := by
        apply mem_W'_of_orth hc hperp hreg
        intro w hw
        have := bil_orth hgorth (g⁻¹ x) w
        rw [show g (g⁻¹ x) = x by simp [LinearEquiv.coe_inv], hgW w hw, bil_comm] at this
        rw [← this]; exact hperp w hw x hxW'
      obtain ⟨w, hw, h⟩ := (exists_add_mem_glueLat_iff (hc := hc) p₂.1 hxW').mpr hx
      have h' : g (w + g⁻¹ x) ∈ glueLat hc K p₂.1 := by
        rwa [map_add, hgW w hw, show g (g⁻¹ x) = x by simp [LinearEquiv.coe_inv]]
      rw [← hgN] at h'
      exact (exists_add_mem_glueLat_iff (hc := hc) p₁.1 hW'inv).mp ⟨w, hw, h'⟩
    have hgmem : g ∈ orthK Q W K := by
      refine ⟨⟨hgorth, ?_⟩, (mem_fixingSubgroup_iff _).mpr fun w hw => hgW w hw⟩
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩; exact hgK x hx
      · intro x hx; exact ⟨g⁻¹ x, hgK' x hx, by simp [LinearEquiv.coe_inv]⟩
    refine ⟨⟨g, hgmem⟩, ?_, ?_⟩
    · ext x
      obtain ⟨c, hc'⟩ := Submodule.Quotient.mk_surjective _ (p₁.1 x)
      have hx1 : (c : V) + x ∈ glueLat hc K p₁.1 :=
        (add_mem_glueLat_iff p₁.1 c.2 (hKW x.2)).mpr ⟨x.2, hc'⟩
      rw [hgN, map_add, hgW c c.2] at hx1
      obtain ⟨hgx, h2⟩ := (add_mem_glueLat_iff p₂.1 c.2 (hgW' x (hKW x.2))).mp hx1
      rw [← hc', LinearMap.comp_apply]
      convert h2 using 2
      exact Subtype.ext rfl
    · simp [g]
  · rintro ⟨g, -, h2⟩
    ext w
    simp [xi, h2, orthK_fix g.2 w.2]

include hperp hreg hMW hKW in
/-- **Kitaoka 1993, Lemma 6.8.3** (p. 176): $\xi : \Psi \to I$, $(\varphi, \sigma) \mapsto \sigma|_M$, is well defined
and surjective, and $\xi(\varphi_1, \sigma_1) = \xi(\varphi_2, \sigma_2)$ iff $\varphi_1 = \varphi_2\alpha$ and
$\sigma_1 = \sigma_2(\mathrm{id}_M \perp \alpha)$ for some $\alpha \in O(K)$. -/
@[kb "kitaoka1993" "§6.8, Lemma 6.8.3, p. 176"]
theorem lemma683 :
    Set.MapsTo xi (glueIsoSet Q hc M N K) (embSet Q W W' M N K) ∧
    Set.SurjOn xi (glueIsoSet Q hc M N K) (embSet Q W W' M N K) ∧
    ∀ p₁ ∈ glueIsoSet Q hc M N K, ∀ p₂ ∈ glueIsoSet Q hc M N K,
      (xi p₁ = xi p₂ ↔ ∃ g : orthK Q W K, p₁.1 = p₂.1.comp (restrK g) ∧ p₁.2 = p₂.2 * g.1) :=
  ⟨fun _ hp => xi_mem_embSet hperp hMW hKW hp, fun _ hτ => xi_surjective hperp hreg hMW hKW hτ,
    fun _ hp₁ _ hp₂ => xi_eq_iff hperp hreg hKW hp₁ hp₂⟩

/-! ### Lemma 6.8.4 -/

theorem latMap_mul (σ τ : V ≃ₗ[F] V) (L : Submodule R V) : latMap (σ * τ) L = latMap σ (latMap τ L) := by
  ext y; simp only [mem_latMap_iff]; rfl

theorem latMap_inv_eq {σ : V ≃ₗ[F] V} {L L' : Submodule R V} (h : latMap σ L = L') : latMap σ⁻¹ L' = L := by
  rw [← h, ← latMap_mul, inv_mul_cancel]; ext y; simp [mem_latMap_iff]

include hperp hreg in
/-- $g = \mathrm{id}_M \perp \alpha$ maps $N_{\varphi\alpha}$ onto $N_\varphi$. -/
theorem mem_glueLat_comp_iff (φ : K →ₗ[R] glueTarget W M) (g : orthK Q W K) (u : V) :
    u ∈ glueLat hc K (φ.comp (restrK g)) ↔ g.1 u ∈ glueLat hc K φ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp hc u
  have hgb : g.1 b ∈ W' := orthK_mapsTo_W' hc hperp hreg g.2 hb
  rw [map_add, orthK_fix g.2 ha, add_mem_glueLat_iff _ ha hb, add_mem_glueLat_iff _ ha hgb]
  constructor
  · rintro ⟨hbK, h⟩
    exact ⟨orthK_mapsTo g.2 hbK, h.trans rfl⟩
  · rintro ⟨hgbK, h⟩
    have hbK : b ∈ K := by
      have : g.1 b ∈ latMap g.1 K := by rw [g.2.1.2]; exact hgbK
      rw [mem_latMap_iff] at this
      simpa using this
    exact ⟨hbK, h.trans rfl⟩

include hperp hreg in
/-- The action of $O(K)$ on $\Psi$: $(\varphi, \sigma) \cdot g = (\varphi\alpha, \sigma g)$ stays in $\Psi$. -/
theorem smul_mem_glueIsoSet {p : (K →ₗ[R] glueTarget W M) × (V ≃ₗ[F] V)} (hp : p ∈ glueIsoSet Q hc M N K)
    (g : orthK Q W K) : (p.1.comp (restrK g), p.2 * g.1) ∈ glueIsoSet Q hc M N K := by
  refine ⟨(orth Q).mul_mem hp.1 (orthK_orth g.2), ?_⟩
  show latMap (p.2 * g.1) (glueLat hc K (p.1.comp (restrK g))) = N
  rw [latMap_mul, ← hp.2]
  congr 1
  ext y
  rw [mem_latMap_iff, mem_glueLat_comp_iff hperp hreg]
  simp

include hperp hreg hMW hKW in
/-- $\Psi \simeq I \times O(K)$ (Kitaoka 1993, proof of Lemma 6.8.4: $\#\Psi = \#I \cdot E(K)$). -/
theorem nonempty_equiv_embSet_prod :
    Nonempty (glueIsoSet Q hc M N K ≃ embSet Q W W' M N K × orthK Q W K) := by
  have hs : ∀ τ : embSet Q W W' M N K, ∃ p : glueIsoSet Q hc M N K, xi p.1 = τ.1 := fun τ => by
    obtain ⟨p, hp, h⟩ := xi_surjective hperp hreg hMW hKW τ.2
    exact ⟨⟨p, hp⟩, h⟩
  choose s hs using hs
  have hg : ∀ p : glueIsoSet Q hc M N K, ∃ g : orthK Q W K,
      p.1.1 = (s ⟨xi p.1, xi_mem_embSet hperp hMW hKW p.2⟩).1.1.comp (restrK g) ∧
        p.1.2 = (s ⟨xi p.1, xi_mem_embSet hperp hMW hKW p.2⟩).1.2 * g.1 := fun p =>
    (xi_eq_iff hperp hreg hKW p.2 (s _).2).mp (hs ⟨xi p.1, xi_mem_embSet hperp hMW hKW p.2⟩).symm
  choose g hg using hg
  refine ⟨{ toFun := fun p => (⟨xi p.1, xi_mem_embSet hperp hMW hKW p.2⟩, g p)
            invFun := fun q => ⟨_, smul_mem_glueIsoSet hperp hreg (s q.1).2 q.2⟩
            left_inv := fun p => ?_
            right_inv := fun q => ?_ }⟩
  · apply Subtype.ext
    exact Prod.ext (hg p).1.symm (hg p).2.symm
  · obtain ⟨τ, h⟩ := q
    have hxi : xi ((s τ).1.1.comp (restrK h), (s τ).1.2 * h.1) = τ.1 := by
      rw [← hs τ]; ext w; simp [xi, orthK_fix h.2 w.2]
    have hτ : (⟨xi ((s τ).1.1.comp (restrK h), (s τ).1.2 * h.1), xi_mem_embSet hperp hMW hKW
        (smul_mem_glueIsoSet hperp hreg (s τ).2 h)⟩ : embSet Q W W' M N K) = τ := Subtype.ext hxi
    refine Prod.ext hτ ?_
    set p : glueIsoSet Q hc M N K := ⟨_, smul_mem_glueIsoSet hperp hreg (s τ).2 h⟩
    have h2 := (hg p).2
    simp only [p] at h2
    rw [hτ] at h2
    exact Subtype.ext (mul_left_cancel h2).symm

/-- $\Psi \simeq \Phi \times O(N)$ (Kitaoka 1993, proof of Lemma 6.8.4: $\#\Psi = \#\Phi \cdot E(N)$). -/
theorem nonempty_equiv_glueSet_prod :
    Nonempty (glueIsoSet Q hc M N K ≃ glueSet Q hc M N K × orthLat Q N) := by
  have hs : ∀ φ : glueSet Q hc M N K, ∃ σ ∈ orth Q, latMap σ (glueLat hc K φ.1) = N := fun φ => φ.2
  choose σ hσ hσN using hs
  refine ⟨{ toFun := fun p => (⟨p.1.1, p.1.2, p.2.1, p.2.2⟩,
              ⟨p.1.2 * (σ ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩)⁻¹, (orth Q).mul_mem p.2.1 ((orth Q).inv_mem (hσ _)), ?_⟩)
            invFun := fun q => ⟨(q.1.1, q.2.1 * σ q.1), (orth Q).mul_mem q.2.2.1 (hσ q.1), ?_⟩
            left_inv := fun p => ?_
            right_inv := fun q => ?_ }⟩
  · show latMap _ N = N
    rw [latMap_mul, latMap_inv_eq (hσN _), p.2.2]
  · show latMap _ _ = N
    rw [latMap_mul, hσN, q.2.2.2]
  · apply Subtype.ext; simp
  · obtain ⟨φ, h⟩ := q
    simp

include hperp hreg hMW hKW in
/-- **Kitaoka 1993, Lemma 6.8.4** (p. 177), cardinality form: $\#I \cdot \#O(K) = \#\Phi \cdot \#O(N)$, where
$\#I$ is the number of isometries $\sigma : M \to N$ with $\sigma(M)$ primitive in $N$ and
$\mathrm{proj}_{\sigma(M)^\perp} N \cong K$, and $\Phi$ the set of $\varphi : K \to FM/M$ with $N_\varphi \cong N$
(cardinalities as `Nat.card`, $0$ for infinite sets; no definiteness is needed for this identity). -/
@[kb "kitaoka1993" "§6.8, Lemma 6.8.4, p. 177 (cardinality form)"]
theorem lemma684_card :
    Nat.card (embSet Q W W' M N K) * Nat.card (orthK Q W K) =
      Nat.card (glueSet Q hc M N K) * Nat.card (orthLat Q N) := by
  obtain ⟨e₁⟩ := nonempty_equiv_embSet_prod hperp hreg hMW hKW (hc := hc) (N := N)
  obtain ⟨e₂⟩ := nonempty_equiv_glueSet_prod (Q := Q) (hc := hc) (M := M) (N := N) (K := K)
  rw [← Nat.card_prod, ← Nat.card_prod, ← Nat.card_congr e₁, Nat.card_congr e₂]

include hperp hreg hMW hKW in
/-- **Kitaoka 1993, Lemma 6.8.4** (p. 177): if $O(N)$ and $O(K)$ are finite (as for lattices on positive definite
spaces over $\mathbb Q$, Kitaoka's hypothesis), then
$E(N)^{-1}\#\{\sigma : M \to N \mid \sigma(M)$ primitive in $N$, $\mathrm{proj}_{\sigma(M)^\perp} N \cong K\} =
E(K)^{-1}\#\{\varphi : K \to FM/M \mid N_\varphi \cong N\}$, $E(L) = \#O(L)$. -/
@[kb "kitaoka1993" "§6.8, Lemma 6.8.4, p. 177"]
theorem lemma684 [Finite (orthLat Q N)] [Finite (orthK Q W K)] :
    (Nat.card (embSet Q W W' M N K) : ℚ) / Nat.card (orthLat Q N) =
      (Nat.card (glueSet Q hc M N K) : ℚ) / Nat.card (orthK Q W K) := by
  have h := lemma684_card hperp hreg hMW hKW (Q := Q) (hc := hc) (M := M) (N := N) (K := K)
  have h1 : (Nat.card (orthLat Q N) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h2 : (Nat.card (orthK Q W K) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [div_eq_div_iff h1 h2]
  exact_mod_cast h

/-! ### Lemma 6.8.9, first part: $\Phi = \{0\}$ for unimodular $M$, $N$ -/

include hMW in
/-- $M$ is primitive in $N_\varphi$: $N_\varphi \cap FM = M$ (Lemma 6.8.1, converse part). -/
theorem glueLat_inf_W (φ : K →ₗ[R] glueTarget W M) : glueLat hc K φ ⊓ W.restrictScalars R = M := by
  ext v
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨h, hv⟩; exact (mem_glueLat_of_mem_W_iff hMW φ hv).mp h
  · intro hv; exact ⟨(mem_glueLat_of_mem_W_iff hMW φ (hMW hv)).mpr hv, hMW hv⟩

include hKW in
/-- $\mathrm{proj}(N_\varphi) = K$ (Lemma 6.8.1, converse part). -/
theorem map_projK_glueLat (φ : K →ₗ[R] glueTarget W M) : (glueLat hc K φ).map (projK R W W' hc) = K := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨h, -⟩ := hv
    exact h
  · intro hx
    obtain ⟨w, hw, h⟩ := (exists_add_mem_glueLat_iff (hc := hc) φ (hKW hx)).mpr hx
    exact ⟨w + x, h, projK_add w x hw (hKW hx)⟩

include hperp hMW hKW in
/-- **Kitaoka 1993, Lemma 6.8.9** (p. 182), first assertion $\#\Phi = 1$: under (*), if $M$ is unimodular
($M^\# = M$ on $FM$, Kitaoka's Proposition 5.2.1) and $N$ is integral ($B(N, N) \subseteq R$; in the book $N$ is
unimodular and $R = \mathbb Z_p$, $p \ne 2$), then the only linear map $\varphi : K \to FM/M$ with
$N_\varphi \cong N$ is $\varphi = 0$. *Update:* the hypothesis $p \ne 2$ is not needed for this assertion, and $N$
need only be integral. The second assertion of the lemma (the conditions on $\sigma$ in Lemma 6.8.7 can be dropped)
concerns Lemma 6.8.7, which is not formalized. -/
@[kb "kitaoka1993" "§6.8, Lemma 6.8.9, p. 182 (#Φ = 1)"]
theorem lemma689_glueSet (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    (hMdual : LinearMap.BilinForm.dualSubmodule (R := R) (associated Q) M ⊓ W.restrictScalars R = M)
    (hN : ∀ x ∈ N, ∀ y ∈ N, bil Q x y ∈ (1 : Submodule R F)) :
    glueSet Q hc M N K = {0} := by
  ext φ
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨σ, hσ, hσN⟩
    have hN' : ∀ x ∈ glueLat hc K φ, ∀ y ∈ glueLat hc K φ, bil Q x y ∈ (1 : Submodule R F) := by
      intro x hx y hy
      have hx' : σ x ∈ N := hσN ▸ ⟨x, hx, rfl⟩
      have hy' : σ y ∈ N := hσN ▸ ⟨y, hy, rfl⟩
      rw [← bil_orth hσ]
      exact hN _ hx' _ hy'
    have hM' := glueLat_inf_W (hc := hc) hMW φ
    have hK' := map_projK_glueLat (hc := hc) (M := M) hKW φ
    have h0 := glueMap_eq_zero hperp hM' hK' hMdual hN'
    have hglue : glueLat hc K (glueMap hc hM' hK') = glueLat hc K φ := by
      ext v; exact (mem_iff_glueCond hc hM' hK' v).symm
    have huniq := (lemma681 hc hM' hK').unique (rfl : glueLat hc K φ = glueLat hc K φ) hglue
    rw [huniq, h0]
  · rintro rfl
    refine ⟨1, (orth Q).one_mem, ?_⟩
    have h0 := glueMap_eq_zero hperp hM hK hMdual hN
    have hg : glueLat hc K (glueMap hc hM hK) = N := by
      ext v; exact (mem_iff_glueCond hc hM hK v).symm
    rw [h0] at hg
    rw [hg]
    ext y
    simp [mem_latMap_iff]

end QuadFormsKB.Kitaoka.Glue
