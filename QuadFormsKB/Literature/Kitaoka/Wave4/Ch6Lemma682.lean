/-
# Kitaoka 1993, Lemma 6.8.2: discriminant, scale and glue map of a lattice with a primitive sublattice

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §6.8, Lemma 6.8.2, p. 175 (printed page), in the
proof of the Minkowski–Siegel formula (Theorem 6.8.1).

**Book statement.** Under condition (*) of §6.8 ($R$, $F$ are $\mathbb Z$, $\mathbb Q$ or $\mathbb Z_p$, $\mathbb Q_p$;
$FN = FM \perp FK$ regular, $M$ primitive in $N$, $K = \mathrm{proj}(N)$ the projection of $N$ to $FK$):
$d N = d M\, d K$, $s(K) \subseteq s(N)^2 s(M^\#) + s(N)$, the index $[K^\# : K^\# \cap K]$ and the number
$\#\varphi(K)$ of values of the glue map $\varphi$ of Lemma 6.8.1 are bounded by constants depending only on $M$, $N$;
and if $M$ and $N$ are unimodular, then $N = M \perp K$.

**Setting.** As in `Wave3/Ch6Lemma681.lean`: $R$ a commutative ring, $F$ a field which is an $R$-algebra with $2$
invertible, $(V, Q)$ a quadratic space over $F$ with Kitaoka's bilinear form $B(x, y) = \tfrac12(Q(x+y)-Q(x)-Q(y))$
(`OMeara.bil Q`), $W = FM$ and $W' = FK$ complementary subspaces (`IsCompl W W'`) which are orthogonal (`hperp`),
$N$ an $R$-submodule of $V$, $M = N \cap W$ (hypothesis `hM`: $M$ is primitive in $N$) and $K = \pi(N)$ for the
projection $\pi$ onto $W'$ along $W$ (hypothesis `hK`). The dual $M^\#$ of $M$ on $FM = W$ (Kitaoka §5.1, p. 70)
is $\{y \in W : B(y, M) \subseteq R\}$, written with Mathlib's `LinearMap.BilinForm.dualSubmodule` as
`LinearMap.BilinForm.dualSubmodule (R := R) (associated Q) M ⊓ W.restrictScalars R`. Scales are O'Meara's `OMeara.scale`, discriminants
`OMeara.HasDisc`, and $N = M \perp K$ is `OMeara.IsOrthSum Q N M K`.

**Proves**
* `lemma682_disc` ($dN = dM\,dK$): if $M$ and $K$ have bases with discriminants $\alpha$ and $\beta$ and
  $FM = W$, then $N$ has a base with discriminant $\alpha\beta$ (so $dN = dM\,dK$ exactly, not only up to unit
  squares).
* `lemma682_scale` ($s(K) \subseteq s(N)^2 s(M^\#) + s(N)$), for $s(N) = aR$ principal (always the case for
  $R = \mathbb Z$ or $\mathbb Z_p$).
* `lemma682_glue` (the content of the bound on $\#\varphi(K)$, display (3) of the proof): every value of $\varphi$ is the
  class of $a\,y$ for some $y \in M^\#$, where $s(N) \subseteq aR$; so $\varphi(K)$ lies in the image of $aM^\#$ in
  $FM/M$, a finite group of order $[aM^\# + M : M]$ depending only on $M$ and $s(N)$.
* `lemma682_unimodular` ($N = M \perp K$ for $M$, $N$ unimodular), and then $\varphi = 0$ (`glueMap_eq_zero`). Unimodular
  is used in the form of Kitaoka's Proposition 5.2.1 ($M^\# = M$ on $FM$); for $N$ only $s(N) \subseteq R$ is used.

*Update:* the unimodular clause holds as soon as $M^\# = M$ and $B(N, N) \subseteq R$ (that is, $N$ integral rather
than unimodular). The boundedness of $[K^\# : K^\# \cap K]$ is not formalized (it follows from the scale bound and
needs indices of lattices); the bound on $\#\varphi(K)$ is formalized as the containment it rests on.

All results are unconditional (no named input hypotheses).
-/
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch6Lemma681
import QuadFormsKB.Literature.OMeara.Sec82
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

set_option linter.unusedSectionVars false

noncomputable section

open QuadraticMap Submodule Module
open scoped Matrix
open QuadFormsKB.OMeara (bil scale gram HasDisc IsOrthSum bil_comm bil_add_left bil_add_right bil_sub_left
  bil_sub_right bil_smul_left bil_smul_right bil_rsmul_left bil_rsmul_right bil_sum_left bil_sum_right)

namespace QuadFormsKB.Kitaoka.Glue

variable {R F V : Type*} [CommRing R] [Field F] [Algebra R F] [Invertible (2 : F)] [AddCommGroup V] [Module F V]
  [Module R V] [IsScalarTower R F V]
variable {Q : QuadraticForm F V} {W W' : Submodule F V} {hc : IsCompl W W'} {M N K : Submodule R V}

theorem projK_mem (v : V) : projK R W W' hc v ∈ W' := by
  rw [projK, LinearMap.restrictScalars_apply, Submodule.projection_apply]
  exact (W'.projectionOnto W hc.symm v).2

theorem projK_of_mem' {x : V} (hx : x ∈ W') : projK R W W' hc x = x := by
  rw [projK, LinearMap.restrictScalars_apply, Submodule.projection_apply,
    Submodule.projectionOnto_apply_of_mem_left hc.symm hx]

theorem K_le_W' (hK : N.map (projK R W W' hc) = K) : K ≤ W'.restrictScalars R := by
  rw [← hK]; rintro _ ⟨v, -, rfl⟩; exact projK_mem v

theorem M_le_W (hM : N ⊓ W.restrictScalars R = M) : M ≤ W.restrictScalars R := hM ▸ inf_le_right

theorem M_le_N (hM : N ⊓ W.restrictScalars R = M) : M ≤ N := hM ▸ inf_le_left

/-- $B(x, w) = B(\pi x, w) + B(\rho x, w)$ reduces to the $W$-part when $w \in W$: $B(x, w) = B(\rho x, w)$, where
$\rho x$ is the $W$-component of $x$. -/
theorem bil_projM (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0) (x : V) {w : V} (hw : w ∈ W) :
    bil Q ((projM R W W' hc x : W.restrictScalars R) : V) w = bil Q x w := by
  conv_rhs => rw [← projM_add_projK R W W' hc x]
  rw [bil_add_left, bil_comm Q (projK R W W' hc x), hperp w hw _ (projK_mem x), add_zero]

/-- **Kitaoka 1993, Lemma 6.8.2** (p. 175), last clause: under (*), if $M$ is unimodular ($M^\# = M$ on $FM$,
Kitaoka's Proposition 5.2.1) and $N$ is integral ($B(N, N) \subseteq R$; in the book $N$ is unimodular), then
$N = M \perp K$. -/
@[kb "kitaoka1993" "§6.8, Lemma 6.8.2, p. 175 (M, N unimodular ⇒ N = M ⊥ K)"]
theorem lemma682_unimodular (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0)
    (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    (hMdual : LinearMap.BilinForm.dualSubmodule (R := R) (associated Q) M ⊓ W.restrictScalars R = M)
    (hN : ∀ x ∈ N, ∀ y ∈ N, bil Q x y ∈ (1 : Submodule R F)) :
    IsOrthSum Q N M K := by
  have hMW := M_le_W hM
  have hMN := M_le_N hM
  have hKW := K_le_W' hK
  -- the `W`-component of every `x ∈ N` lies in `M`
  have hρ : ∀ x ∈ N, ((projM R W W' hc x : W.restrictScalars R) : V) ∈ M := by
    intro x hx
    rw [← hMdual]
    refine ⟨fun m hm => ?_, (projM R W W' hc x).2⟩
    change bil Q _ m ∈ _
    rw [bil_projM hperp x (hMW hm)]
    exact hN x hx m (hMN hm)
  have hKN : K ≤ N := by
    rw [← hK]
    rintro _ ⟨x, hx, rfl⟩
    have h := projM_add_projK R W W' hc x
    have : projK R W W' hc x = x - ((projM R W W' hc x : W.restrictScalars R) : V) := by
      exact eq_sub_of_add_eq' h
    rw [this]
    exact N.sub_mem hx (hMN (hρ x hx))
  refine ⟨fun x hx y hy => hperp x (hMW hx) y (hKW hy), ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxM hxK
    have h1 := projK_of_mem' (hc := hc) (R := R) (hKW hxK)
    rw [(projK_eq_zero_iff (R := R) W W' hc x).mpr (hMW hxM)] at h1
    exact h1.symm
  · apply le_antisymm (sup_le hMN hKN)
    intro x hx
    rw [← projM_add_projK R W W' hc x]
    exact Submodule.add_mem_sup (hρ x hx) (hK ▸ ⟨x, hx, rfl⟩)

/-- Under the hypotheses of `lemma682_unimodular` the glue map of Lemma 6.8.1 is zero (Kitaoka 1993, proof of
Lemma 6.8.2, p. 176: $q_i = 1$). -/
theorem glueMap_eq_zero (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0)
    (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    (hMdual : LinearMap.BilinForm.dualSubmodule (R := R) (associated Q) M ⊓ W.restrictScalars R = M)
    (hN : ∀ x ∈ N, ∀ y ∈ N, bil Q x y ∈ (1 : Submodule R F)) :
    glueMap hc hM hK = 0 := by
  have hs := lemma682_unimodular hperp hM hK hMdual hN
  have hKN : K ≤ N := hs.sup_eq ▸ le_sup_right
  ext k
  have hk : projK R W W' hc (k : V) ∈ K := by
    rw [projK_of_mem' (K_le_W' hK k.2)]; exact k.2
  have e : (⟨projK R W W' hc (k : V), hk⟩ : K) = k := Subtype.ext (projK_of_mem' (K_le_W' hK k.2))
  rw [LinearMap.zero_apply, ← e, glueMap_apply hc hM hK (hKN k.2) hk, Submodule.Quotient.mk_eq_zero]
  change ((projM R W W' hc (k : V) : W.restrictScalars R) : V) ∈ M
  have h := projM_add_projK R W W' hc (k : V)
  rw [projK_of_mem' (K_le_W' hK k.2), add_eq_right] at h
  rw [h]; exact M.zero_mem

/-- The $W$-component $\rho(n)$ of an element $n \in N$ pairs with $M$ into $s(N)$: $B(\rho n, m) = B(n, m)$. -/
theorem bil_projM_mem_scale (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0) (hM : N ⊓ W.restrictScalars R = M)
    {n : V} (hn : n ∈ N) {m : V} (hm : m ∈ M) :
    bil Q ((projM R W W' hc n : W.restrictScalars R) : V) m ∈ scale Q N := by
  rw [bil_projM hperp n (M_le_W hM hm)]
  exact OMeara.bil_mem_scale Q hn (M_le_N hM hm)

/-- If $s(N) \subseteq aR$ with $a \ne 0$, the $W$-component of every $n \in N$ is $a\,y$ with $y \in M^\#$ (the dual
of $M$ on $FM = W$). -/
theorem projM_mem_smul_dual (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0) (hM : N ⊓ W.restrictScalars R = M)
    {a : F} (ha : a ≠ 0) (hsN : scale Q N ≤ R ∙ a) {n : V} (hn : n ∈ N) :
    ∃ y ∈ LinearMap.BilinForm.dualSubmodule (R := R) (associated Q) M ⊓ W.restrictScalars R,
      ((projM R W W' hc n : W.restrictScalars R) : V) = a • y := by
  set c : V := ((projM R W W' hc n : W.restrictScalars R) : V)
  refine ⟨a⁻¹ • c, ⟨fun m hm => ?_, W.smul_mem _ (projM R W W' hc n).2⟩, by rw [smul_smul, mul_inv_cancel₀ ha,
    one_smul]⟩
  change bil Q (a⁻¹ • c) m ∈ _
  rw [bil_smul_left]
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hsN (bil_projM_mem_scale hperp hM hn hm))
  rw [← hr, Algebra.smul_def, mul_left_comm, inv_mul_cancel₀ ha, mul_one]
  exact Submodule.mem_one.mpr ⟨r, rfl⟩

/-- **Kitaoka 1993, Lemma 6.8.2** (p. 175), the glue map clause, in the form of display (3) of the proof: if
$s(N) \subseteq aR$ ($a \ne 0$), then every value $\varphi(x)$ ($x \in K$) of the glue map of Lemma 6.8.1 is the class
modulo $M$ of $a\,y$ for some $y$ in the dual $M^\#$ of $M$ on $FM$. Hence $\varphi(K)$ lies in the image of $aM^\#$
in $FM/M$, whose order $[aM^\# + M : M]$ depends only on $M$ and $s(N)$: this is Kitaoka's bound on
$\#\varphi(K)$. -/
@[kb "kitaoka1993" "§6.8, Lemma 6.8.2, p. 175 (#φ(K) bounded)"]
theorem lemma682_glue (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0)
    (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    {a : F} (ha : a ≠ 0) (hsN : scale Q N ≤ R ∙ a) (k : K) :
    ∃ y ∈ LinearMap.BilinForm.dualSubmodule (R := R) (associated Q) M ⊓ W.restrictScalars R, ∃ hy : a • y ∈ W,
      glueMap hc hM hK k = Submodule.Quotient.mk (⟨a • y, hy⟩ : W.restrictScalars R) := by
  obtain ⟨n, hn, hnk⟩ := exists_of_mem_K hc hK k
  have hk : projK R W W' hc n ∈ K := hK ▸ ⟨n, hn, rfl⟩
  obtain ⟨y, hy, hcy⟩ := projM_mem_smul_dual hperp hM ha hsN hn
  refine ⟨y, hy, hcy ▸ (projM R W W' hc n).2, ?_⟩
  have e : (⟨projK R W W' hc n, hk⟩ : K) = k := Subtype.ext hnk
  rw [← e, glueMap_apply hc hM hK hn hk]
  congr 1
  exact Subtype.ext hcy

/-- **Kitaoka 1993, Lemma 6.8.2** (p. 175), scale clause: under (*), if $s(N) = aR$ (a principal fractional ideal, as
always over $\mathbb Z$ and $\mathbb Z_p$; $a \ne 0$), then $s(K) \subseteq s(N)^2 s(M^\#) + s(N)$, where $M^\#$ is
the dual of $M$ on $FM = W$. -/
@[kb "kitaoka1993" "§6.8, Lemma 6.8.2, p. 175 (s(K) ⊆ s(N)² s(M#) + s(N))"]
theorem lemma682_scale (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0)
    (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    {a : F} (ha : a ≠ 0) (hsN : scale Q N = R ∙ a) :
    scale Q K ≤ scale Q N * scale Q N * scale Q (LinearMap.BilinForm.dualSubmodule (R := R) (associated Q) M ⊓ W.restrictScalars R) +
      scale Q N := by
  rw [scale, Submodule.span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  obtain ⟨nx, hnx, rfl⟩ := hK ▸ hx
  obtain ⟨ny, hny, rfl⟩ := hK ▸ hy
  obtain ⟨dx, hdx, hcx⟩ := projM_mem_smul_dual (hc := hc) hperp hM ha hsN.le hnx
  obtain ⟨dy, hdy, hcy⟩ := projM_mem_smul_dual (hc := hc) hperp hM ha hsN.le hny
  -- `B(πx, πy) = B(nx, ny) - B(ρ nx, ρ ny)`
  have hdec : ∀ v : V, projK R W W' hc v = v - ((projM R W W' hc v : W.restrictScalars R) : V) := fun v => by
    exact eq_sub_of_add_eq' (projM_add_projK R W W' hc v)
  have key : bil Q (projK R W W' hc nx) (projK R W W' hc ny) =
      bil Q nx ny - bil Q ((projM R W W' hc nx : W.restrictScalars R) : V)
        ((projM R W W' hc ny : W.restrictScalars R) : V) := by
    have h1 : bil Q ((projM R W W' hc nx : W.restrictScalars R) : V) (projK R W W' hc ny) = 0 :=
      hperp _ (projM R W W' hc nx).2 _ (projK_mem ny)
    have h2 : bil Q (projK R W W' hc nx) (projK R W W' hc ny) = bil Q nx (projK R W W' hc ny) := by
      conv_rhs => rw [← projM_add_projK R W W' hc nx]
      rw [bil_add_left, h1, zero_add]
    rw [h2, hdec ny, bil_sub_right, bil_comm Q nx ((projM R W W' hc ny : W.restrictScalars R) : V),
      bil_projM hperp nx (projM R W W' hc ny).2, bil_comm Q _ nx]
  change bil Q _ _ ∈ _
  rw [key, sub_eq_neg_add]
  refine Submodule.add_mem_sup ?_ (OMeara.bil_mem_scale Q hnx hny)
  rw [hcx, hcy, bil_smul_left, bil_smul_right, ← mul_assoc, ← neg_mul]
  have haN : a ∈ scale Q N := hsN ▸ Submodule.mem_span_singleton_self a
  have : -(a * a) * bil Q dx dy = (-a) * a * bil Q dx dy := by ring
  rw [this]
  exact Submodule.mul_mem_mul (Submodule.mul_mem_mul (Submodule.neg_mem _ haN) haN)
    (OMeara.bil_mem_scale Q hdx hdy)

/-! ### The discriminant: $dN = dM\,dK$ -/

/-- The matrix of a family $x_i = \sum_j T_{ij} b_j$ with coefficients $T_{ij} \in F$ is $T\,G\,T^{\mathsf T}$, $G$ the
matrix of $b$ (the field version of `OMeara.gram_comb`). -/
theorem gram_combF {ι κ : Type*} [Fintype κ] (b : κ → V) (T : Matrix ι κ F) :
    gram Q (fun i => ∑ j, T i j • b j) = T * gram Q b * Tᵀ := by
  ext i k
  simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, bil_sum_left, bil_sum_right,
    bil_smul_left, bil_smul_right, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable (hc) in
/-- The family of Kitaoka's proof: a base $u_0, \dots, u_{a-1}$ of $M$ followed by lifts $w_j \in N$ of a base
$v_0, \dots, v_{b-1}$ of $K$ ($\pi(w_j) = v_j$). -/
def glueFamily (hK : N.map (projK R W W' hc) = K) {a b : ℕ} (bM : Basis (Fin a) R M) (bK : Basis (Fin b) R K) :
    Fin a ⊕ Fin b → V :=
  Sum.elim (fun i => (bM i : V)) (fun j => Classical.choose (exists_of_mem_K hc hK (bK j)))

theorem glueFamily_inr_mem (hK : N.map (projK R W W' hc) = K) {a b : ℕ} (bM : Basis (Fin a) R M)
    (bK : Basis (Fin b) R K) (j : Fin b) :
    glueFamily hc hK bM bK (Sum.inr j) ∈ N ∧ projK R W W' hc (glueFamily hc hK bM bK (Sum.inr j)) = bK j :=
  Classical.choose_spec (exists_of_mem_K hc hK (bK j))

theorem glueFamily_linearIndependent (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    {a b : ℕ} (bM : Basis (Fin a) R M) (bK : Basis (Fin b) R K) :
    LinearIndependent R (glueFamily hc hK bM bK) := by
  have hliM : LinearIndependent R (fun i => (bM i : V)) :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hliK : LinearIndependent R (fun j => (bK j : V)) :=
    bK.linearIndependent.map' K.subtype (Submodule.ker_subtype K)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  have h0 : ∀ i, projK R W W' hc (glueFamily hc hK bM bK (Sum.inl i)) = 0 := fun i =>
    (projK_eq_zero_iff (R := R) W W' hc _).mpr (M_le_W hM (bM i).2)
  have hK0 : ∑ j, g (Sum.inr j) • (bK j : V) = 0 := by
    have := congrArg (projK R W W' hc) hg
    simpa [map_sum, map_smul, h0, (glueFamily_inr_mem hK bM bK _).2] using this
  have hgK := (Fintype.linearIndependent_iff.mp hliK) _ hK0
  have hM0 : ∑ i, g (Sum.inl i) • (bM i : V) = 0 := by
    simpa [hgK, glueFamily] using hg
  have hgM := (Fintype.linearIndependent_iff.mp hliM) _ hM0
  rintro (i | j)
  · exact hgM i
  · exact hgK j

theorem span_glueFamily (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    {a b : ℕ} (bM : Basis (Fin a) R M) (bK : Basis (Fin b) R K) :
    span R (Set.range (glueFamily hc hK bM bK)) = N := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨(i | j), rfl⟩
    · exact M_le_N hM (bM i).2
    · exact (glueFamily_inr_mem hK bM bK j).1
  · intro x hx
    have hxK : projK R W W' hc x ∈ K := hK ▸ ⟨x, hx, rfl⟩
    set c := bK.repr ⟨_, hxK⟩
    set y : V := x - ∑ j, c j • glueFamily hc hK bM bK (Sum.inr j)
    have hyN : y ∈ N := N.sub_mem hx (N.sum_mem fun j _ => N.smul_mem _ (glueFamily_inr_mem hK bM bK j).1)
    have hyW : y ∈ W := by
      rw [← projK_eq_zero_iff (R := R) W W' hc]
      have hs := congrArg Subtype.val (bK.sum_repr ⟨_, hxK⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hs
      simp only [y, map_sub, map_sum, map_smul, (glueFamily_inr_mem hK bM bK _).2]
      rw [hs, sub_self]
    have hyM : y ∈ M := hM ▸ ⟨hyN, hyW⟩
    have hsM := congrArg Subtype.val (bM.sum_repr ⟨y, hyM⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsM
    have : x = ∑ i, bM.repr ⟨y, hyM⟩ i • glueFamily hc hK bM bK (Sum.inl i) +
        ∑ j, c j • glueFamily hc hK bM bK (Sum.inr j) := by
      simp only [glueFamily, Sum.elim_inl]
      rw [hsM]; simp only [y, glueFamily, Sum.elim_inr]; abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span ⟨_, rfl⟩))
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨_, rfl⟩))

/-- The base of $N$ of Kitaoka's proof, indexed by $\{0,\dots,a-1\} \sqcup \{0, \dots, b-1\}$. -/
def glueBasis (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    {a b : ℕ} (bM : Basis (Fin a) R M) (bK : Basis (Fin b) R K) : Basis (Fin a ⊕ Fin b) R N :=
  (Basis.span (glueFamily_linearIndependent hM hK bM bK)).map
    (LinearEquiv.ofEq _ _ (span_glueFamily hM hK bM bK))

theorem glueBasis_apply (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    {a b : ℕ} (bM : Basis (Fin a) R M) (bK : Basis (Fin b) R K) (s : Fin a ⊕ Fin b) :
    (glueBasis hM hK bM bK s : V) = glueFamily hc hK bM bK s := by
  simp [glueBasis]

/-- The determinant of the matrix of the glued base is the product of the determinants for $M$ and $K$
(Kitaoka 1993, proof of Lemma 6.8.2: the lifts $w_j$ differ from $v_j$ by vectors of $FM$, a unipotent change of
base, and $FM \perp FK$). -/
theorem det_gram_glueFamily (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0)
    (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    (hMW : span F (M : Set V) ≤ W → W ≤ span F (M : Set V))
    {a b : ℕ} (bM : Basis (Fin a) R M) (bK : Basis (Fin b) R K) :
    (gram Q (glueFamily hc hK bM bK)).det =
      (gram Q fun i => (bM i : V)).det * (gram Q fun j => (bK j : V)).det := by
  have hWle : W ≤ span F (Set.range fun i => (bM i : V)) := by
    refine le_trans (hMW (span_le.mpr fun m hm => ?_)) (span_le.mpr fun m hm => ?_)
    · exact M_le_W hM hm
    · have hs := congrArg Subtype.val (bM.sum_repr ⟨m, hm⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hs
      rw [← hs]
      exact Submodule.sum_mem _ fun i _ => by
        rw [← algebraMap_smul F]
        exact Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)
  -- the `W`-components of the lifts, as combinations of the base of `M`
  have hc' : ∀ j, ∃ t : Fin a → F, ∑ i, t i • (bM i : V) =
      ((projM R W W' hc (glueFamily hc hK bM bK (Sum.inr j)) : W.restrictScalars R) : V) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun F).mp (hWle (projM R W W' hc _).2)
  choose t ht using hc'
  set u : Fin a ⊕ Fin b → V := Sum.elim (fun i => (bM i : V)) (fun j => (bK j : V))
  set P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F := Matrix.fromBlocks 1 0 (Matrix.of t) 1
  have hfam : glueFamily hc hK bM bK = fun s => ∑ s', P s s' • u s' := by
    funext s
    rcases s with i | j
    · simp [P, u, glueFamily, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
    · have h := projM_add_projK R W W' hc (glueFamily hc hK bM bK (Sum.inr j))
      rw [(glueFamily_inr_mem hK bM bK j).2, ← ht j] at h
      simp [P, u, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply, h]
  have hgu : gram Q u = Matrix.fromBlocks (gram Q fun i => (bM i : V)) 0 0 (gram Q fun j => (bK j : V)) := by
    ext (i | i) (j | j)
    · simp [gram, u]
    · simp only [gram, u, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply]
      exact hperp _ (M_le_W hM (bM i).2) _ (K_le_W' hK (bK j).2)
    · simp only [gram, u, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply]
      rw [bil_comm]
      exact hperp _ (M_le_W hM (bM j).2) _ (K_le_W' hK (bK i).2)
    · simp [gram, u]
  rw [hfam, gram_combF, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hgu, Matrix.det_fromBlocks_zero₂₁]
  simp [P]

/-- **Kitaoka 1993, Lemma 6.8.2** (p. 175), discriminant clause $dN = dM\,dK$: under (*) (with $FM = W$, hypothesis
`hMW`), if $M$ has a base with discriminant $\alpha$ and $K$ a base with discriminant $\beta$ (`OMeara.HasDisc`), then
$N$ has a base with discriminant $\alpha\beta$. -/
@[kb "kitaoka1993" "§6.8, Lemma 6.8.2, p. 175 (dN = dM dK)"]
theorem lemma682_disc (hperp : ∀ w ∈ W, ∀ x ∈ W', bil Q w x = 0)
    (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    (hMW : span F (M : Set V) = W) {α β : F} (hα : HasDisc Q M α) (hβ : HasDisc Q K β) :
    HasDisc Q N (α * β) := by
  have : Nontrivial R := (algebraMap R F).domain_nontrivial
  obtain ⟨bM, rfl⟩ := hα
  obtain ⟨bK, rfl⟩ := hβ
  set B := glueBasis hM hK bM bK
  have hr : finrank R N = finrank R M + finrank R K := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  let e : Fin (finrank R M) ⊕ Fin (finrank R K) ≃ Fin (finrank R N) := finSumFinEquiv.trans (finCongr hr.symm)
  refine ⟨B.reindex e, ?_⟩
  have : (gram Q fun i => ((B.reindex e) i : V)) = (gram Q (glueFamily hc hK bM bK)).submatrix e.symm e.symm := by
    ext i j
    simp [gram, Basis.reindex_apply, B, glueBasis_apply]
  rw [this, Matrix.det_submatrix_equiv_self,
    det_gram_glueFamily hperp hM hK (fun _ => hMW.ge) bM bK]

end QuadFormsKB.Kitaoka.Glue
