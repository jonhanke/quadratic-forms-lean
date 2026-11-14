/-
# Kitaoka 1993, Lemma 6.8.1: a lattice is determined by a primitive sublattice, the projection, and a glue map

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §6.8, condition (*) and Lemma 6.8.1, p. 174
(printed page), in the proof of the Minkowski–Siegel formula (Theorem 6.8.1).

**Book statement.** (*): $R$, $F$ are $\mathbb Z$, $\mathbb Q$ or $\mathbb Z_p$, $\mathbb Q_p$; $N, M, K$ are quadratic
lattices with $FN = FM \perp FK$ regular, $M$ a primitive submodule of $N$ ($M = N \cap FM$), and $K = \mathrm{proj}(N)$
the projection of $N$ to $FK$ along $FN = FM \oplus FK$. **Lemma 6.8.1.** Under (*) there is a unique linear map
$\varphi : K \to FM/M$ with $N = M + R[x + \varphi(x) \mid x \in K]$. Conversely, for any linear
$\psi : K \to FM/M$, $M$ is primitive in $N_\psi := M + R[x + \psi(x) \mid x \in K]$, $\mathrm{proj}(N_\psi) = K$,
and $N_\psi = N$ if and only if $\psi = \varphi$.

**Encoding.** The lemma is pure linear algebra; the quadratic form only provides the orthogonal splitting. Here $R$ is
any commutative ring, $F$ a field that is an $R$-algebra, $V$ an $F$-vector space (an $R$-module through $F$),
$W = FM$ and $W' = FK$ complementary subspaces (`IsCompl W W'`; in the book $W' = W^\perp$), $N$ an $R$-submodule
of $V$, $M = N \cap W$ (hypothesis `hM`: $M$ is primitive in $N$ with $FM = W$) and $K = \pi(N)$ for the projection
$\pi$ onto $W'$ along $W$ (hypothesis `hK`). The target $FM/M$ is the $R$-module `W.restrictScalars R ⧸ M`
(`glueTarget`). For $v = w + x$ ($w \in W$, $x \in W'$), "$v \in x + \varphi(x)$" means $x \in K$ and
$w \bmod M = \varphi(x)$ (`GlueCond`); so $M + R[x + \varphi(x) \mid x \in K]$ is the set `glueLat φ` of such $v$.

**Proves** `lemma681` (existence and uniqueness of $\varphi$) and `lemma681_converse` (the converse part).

The result is unconditional (no named input hypotheses).
-/
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.Quotient.Basic
import QuadFormsKB.Citation

noncomputable section

namespace QuadFormsKB.Kitaoka.Glue

variable {R F V : Type*} [CommRing R] [Field F] [Algebra R F] [AddCommGroup V] [Module F V] [Module R V]
  [IsScalarTower R F V]
variable (W W' : Submodule F V) (hc : IsCompl W W')

variable (R) in
/-- The projection $\pi$ of $V = W \oplus W'$ onto $W'$ along $W$, as an $R$-linear map $V \to V$. -/
def projK : V →ₗ[R] V := (W'.projection W hc.symm).restrictScalars R

variable (R) in
/-- The component in $W$ of $v = w + x$ ($w \in W$, $x \in W'$), as an element of $W$ viewed as an $R$-module. -/
def projM : V →ₗ[R] W.restrictScalars R :=
  LinearMap.codRestrict (W.restrictScalars R) ((W.projection W' hc).restrictScalars R) fun v => by
    rw [LinearMap.restrictScalars_apply, Submodule.projection_apply]
    exact (W.projectionOnto W' hc v).2

variable (R) in
theorem projM_add_projK (v : V) : ((projM R W W' hc v : W.restrictScalars R) : V) + projK R W W' hc v = v := by
  show W.projection W' hc v + W'.projection W hc.symm v = v
  exact Submodule.projection_add_projection_eq_self hc v

variable (R) in
theorem projK_eq_zero_iff (v : V) : projK R W W' hc v = 0 ↔ v ∈ W := by
  rw [projK, LinearMap.restrictScalars_apply, Submodule.projection_apply, ZeroMemClass.coe_eq_zero,
    Submodule.projectionOnto_apply_eq_zero_iff]

variable (R) in
theorem projM_of_mem {v : V} (hv : v ∈ W) : ((projM R W W' hc v : W.restrictScalars R) : V) = v := by
  have h := projM_add_projK R W W' hc v
  rwa [(projK_eq_zero_iff (R := R) W W' hc v).mpr hv, add_zero] at h

variable (M : Submodule R V)

/-- The submodule $M$ of $W$ (as an $R$-module), for the quotient $FM/M$. -/
def mIn : Submodule R (W.restrictScalars R) := M.comap (W.restrictScalars R).subtype

/-- **The target $FM/M$** of the glue map (Kitaoka 1993, Lemma 6.8.1, p. 174). -/
abbrev glueTarget := (W.restrictScalars R) ⧸ mIn W M

variable {W W' M}

/-- **$v \in x + \varphi(x)$ for $x = \pi(v)$**: the projection $x = \pi(v)$ lies in $K$ and the $W$-component of $v$
is $\varphi(x)$ modulo $M$. -/
def GlueCond (K : Submodule R V) (φ : K →ₗ[R] glueTarget W M) (v : V) : Prop :=
  ∃ h : projK R W W' hc v ∈ K, Submodule.Quotient.mk (projM R W W' hc v) = φ ⟨_, h⟩

/-- **The lattice $N_\varphi = M + R[x + \varphi(x) \mid x \in K]$** (Kitaoka 1993, Lemma 6.8.1, p. 174). -/
def glueLat (K : Submodule R V) (φ : K →ₗ[R] glueTarget W M) : Submodule R V where
  carrier := {v | GlueCond hc K φ v}
  zero_mem' := ⟨by simp, by
    have e : ∀ h, (⟨projK R W W' hc 0, h⟩ : K) = 0 := fun h => Subtype.ext (by simp)
    rw [e, map_zero, map_zero, Submodule.Quotient.mk_zero]⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_add]; exact K.add_mem ha hb, ?_⟩
    have : (⟨projK R W W' hc (a + b), by rw [map_add]; exact K.add_mem ha hb⟩ : K) = ⟨_, ha⟩ + ⟨_, hb⟩ :=
      Subtype.ext (by simp)
    rw [this, map_add, map_add, Submodule.Quotient.mk_add, ha', hb']
  smul_mem' := by
    rintro r a ⟨ha, ha'⟩
    refine ⟨by rw [map_smul]; exact K.smul_mem r ha, ?_⟩
    have : (⟨projK R W W' hc (r • a), by rw [map_smul]; exact K.smul_mem r ha⟩ : K) = r • ⟨_, ha⟩ :=
      Subtype.ext (by simp)
    rw [this, map_smul, map_smul, Submodule.Quotient.mk_smul, ha']

theorem mem_glueLat {K : Submodule R V} {φ : K →ₗ[R] glueTarget W M} {v : V} :
    v ∈ glueLat hc K φ ↔ GlueCond hc K φ v := Iff.rfl

variable {N K : Submodule R V}

/-- Two elements of $N$ with the same projection have the same $W$-component modulo $M = N \cap W$. -/
theorem mk_projM_eq (hM : N ⊓ W.restrictScalars R = M) {a b : V} (ha : a ∈ N) (hb : b ∈ N)
    (hab : projK R W W' hc a = projK R W W' hc b) :
    (Submodule.Quotient.mk (projM R W W' hc a) : glueTarget W M) = Submodule.Quotient.mk (projM R W W' hc b) := by
  rw [Submodule.Quotient.eq, ← map_sub]
  have hW : a - b ∈ W := by rw [← projK_eq_zero_iff (R := R) W W' hc, map_sub, hab, sub_self]
  change ((projM R W W' hc (a - b) : W.restrictScalars R) : V) ∈ M
  rw [projM_of_mem R W W' hc hW, ← hM]
  exact ⟨N.sub_mem ha hb, hW⟩

theorem exists_of_mem_K (hK : N.map (projK R W W' hc) = K) (k : K) : ∃ n ∈ N, projK R W W' hc n = k := by
  have : (k : V) ∈ N.map (projK R W W' hc) := hK ▸ k.2
  obtain ⟨n, hn, e⟩ := this
  exact ⟨n, hn, e⟩

/-- The glue map $\varphi$ of $N$: $\varphi(x)$ is the $W$-component, modulo $M$, of any $n \in N$ with $\pi(n) = x$. -/
def glueMap (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K) : K →ₗ[R] glueTarget W M where
  toFun k := Submodule.Quotient.mk (projM R W W' hc (Classical.choose (exists_of_mem_K hc hK k)))
  map_add' k₁ k₂ := by
    have h₁ := Classical.choose_spec (exists_of_mem_K hc hK k₁)
    have h₂ := Classical.choose_spec (exists_of_mem_K hc hK k₂)
    have h₁₂ := Classical.choose_spec (exists_of_mem_K hc hK (k₁ + k₂))
    rw [← Submodule.Quotient.mk_add, ← map_add]
    refine mk_projM_eq hc hM h₁₂.1 (N.add_mem h₁.1 h₂.1) ?_
    rw [h₁₂.2, map_add, h₁.2, h₂.2]; rfl
  map_smul' r k := by
    have h₁ := Classical.choose_spec (exists_of_mem_K hc hK k)
    have h₂ := Classical.choose_spec (exists_of_mem_K hc hK (r • k))
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul, ← map_smul]
    refine mk_projM_eq hc hM h₂.1 (N.smul_mem r h₁.1) ?_
    rw [h₂.2, map_smul, h₁.2]; rfl

theorem glueMap_apply (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K) {n : V} (hn : n ∈ N)
    (hk : projK R W W' hc n ∈ K) :
    glueMap hc hM hK ⟨_, hk⟩ = Submodule.Quotient.mk (projM R W W' hc n) := by
  have h := Classical.choose_spec (exists_of_mem_K hc hK ⟨_, hk⟩)
  exact mk_projM_eq hc hM h.1 hn h.2

/-- $N$ is described by its glue map: $v \in N$ iff $\pi(v) \in K$ and the $W$-component of $v$ is $\varphi(\pi v)$
modulo $M$. -/
theorem mem_iff_glueCond (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K) (v : V) :
    v ∈ N ↔ GlueCond hc K (glueMap hc hM hK) v := by
  constructor
  · intro hv
    have hk : projK R W W' hc v ∈ K := hK ▸ ⟨v, hv, rfl⟩
    exact ⟨hk, (glueMap_apply hc hM hK hv hk).symm⟩
  · rintro ⟨hk, hφ⟩
    obtain ⟨n, hn, hnv⟩ := exists_of_mem_K hc hK ⟨_, hk⟩
    have hnk : projK R W W' hc n ∈ K := hK ▸ ⟨n, hn, rfl⟩
    have e : (⟨projK R W W' hc v, hk⟩ : K) = ⟨projK R W W' hc n, hnk⟩ := Subtype.ext hnv.symm
    rw [e, glueMap_apply hc hM hK hn hnk, Submodule.Quotient.eq, ← map_sub] at hφ
    have hW : v - n ∈ W := by rw [← projK_eq_zero_iff (R := R) W W' hc, map_sub, hnv, sub_self]
    change ((projM R W W' hc (v - n) : W.restrictScalars R) : V) ∈ M at hφ
    rw [projM_of_mem R W W' hc hW, ← hM] at hφ
    have := N.add_mem hn hφ.1
    rwa [add_sub_cancel] at this

/-- **Kitaoka 1993, Lemma 6.8.1** (p. 174), first part: under (*) ($M = N \cap FM$ primitive, $K = \mathrm{proj}(N)$)
there is a unique linear map $\varphi : K \to FM/M$ with $N = M + R[x + \varphi(x) \mid x \in K]$. -/
@[kb "kitaoka1993" "§6.8, Lemma 6.8.1, p. 174"]
theorem lemma681 (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K) :
    ∃! φ : K →ₗ[R] glueTarget W M, glueLat hc K φ = N := by
  refine ⟨glueMap hc hM hK, ?_, ?_⟩
  · ext v; exact (mem_iff_glueCond hc hM hK v).symm
  · intro φ hφ
    ext k
    obtain ⟨n, hn, hnk⟩ := exists_of_mem_K hc hK k
    have hn' : n ∈ glueLat hc K φ := hφ ▸ hn
    obtain ⟨hk, h⟩ := hn'
    have e : (⟨projK R W W' hc n, hk⟩ : K) = k := Subtype.ext hnk
    rw [← e, ← h, glueMap_apply hc hM hK hn hk]

/-- **Kitaoka 1993, Lemma 6.8.1** (p. 174), converse part: for every linear $\psi : K \to FM/M$, $M$ is primitive in
$N_\psi = M + R[x + \psi(x) \mid x \in K]$ (i.e. $N_\psi \cap FM = M$), $\mathrm{proj}(N_\psi) = K$, and $N_\psi = N$
if and only if $\psi$ is the glue map $\varphi$ of $N$. -/
@[kb "kitaoka1993" "§6.8, Lemma 6.8.1, p. 174 (converse)"]
theorem lemma681_converse (hM : N ⊓ W.restrictScalars R = M) (hK : N.map (projK R W W' hc) = K)
    (ψ : K →ₗ[R] glueTarget W M) :
    glueLat hc K ψ ⊓ W.restrictScalars R = M ∧ (glueLat hc K ψ).map (projK R W W' hc) = K ∧
      (glueLat hc K ψ = N ↔ ψ = glueMap hc hM hK) := by
  have hMW : M ≤ W.restrictScalars R := hM ▸ inf_le_right
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_glueLat]
    constructor
    · rintro ⟨⟨hk, h⟩, hv⟩
      have h0 : (⟨projK R W W' hc v, hk⟩ : K) = 0 := Subtype.ext ((projK_eq_zero_iff (R := R) W W' hc v).mpr hv)
      rw [h0, map_zero, Submodule.Quotient.mk_eq_zero] at h
      change ((projM R W W' hc v : W.restrictScalars R) : V) ∈ M at h
      rwa [projM_of_mem R W W' hc hv] at h
    · intro hv
      have hvW : v ∈ W := hMW hv
      have hk0 : projK R W W' hc v = 0 := (projK_eq_zero_iff (R := R) W W' hc v).mpr hvW
      refine ⟨⟨by rw [hk0]; exact K.zero_mem, ?_⟩, hvW⟩
      have h0 : (⟨projK R W W' hc v, by rw [hk0]; exact K.zero_mem⟩ : K) = 0 := Subtype.ext hk0
      rw [h0, map_zero, Submodule.Quotient.mk_eq_zero]
      change ((projM R W W' hc v : W.restrictScalars R) : V) ∈ M
      rwa [projM_of_mem R W W' hc hvW]
  · ext x
    constructor
    · rintro ⟨v, ⟨hk, -⟩, rfl⟩; exact hk
    · intro hx
      obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (ψ ⟨x, hx⟩)
      have hxW' : x ∈ W' := by
        rw [← hK] at hx
        obtain ⟨n, -, rfl⟩ := hx
        rw [projK, LinearMap.restrictScalars_apply, Submodule.projection_apply]
        exact (W'.projectionOnto W hc.symm n).2
      have hπw : projK R W W' hc (w : V) = 0 := (projK_eq_zero_iff (R := R) W W' hc _).mpr w.2
      have hπx : projK R W W' hc x = x := by
        rw [projK, LinearMap.restrictScalars_apply, Submodule.projection_apply,
          Submodule.projectionOnto_apply_of_mem_left hc.symm hxW']
      have hρx : ((projM R W W' hc x : W.restrictScalars R) : V) = 0 := by
        have h := projM_add_projK R W W' hc x
        rw [hπx] at h
        simpa using h
      refine ⟨(w : V) + x, ⟨?_, ?_⟩, ?_⟩
      · rw [map_add, hπw, zero_add, hπx]; exact hx
      · have hρ : projM R W W' hc ((w : V) + x) = w := by
          apply Subtype.ext
          rw [map_add, Submodule.coe_add, projM_of_mem R W W' hc w.2, hρx, add_zero]
        have e : (⟨projK R W W' hc ((w : V) + x), by rw [map_add, hπw, zero_add, hπx]; exact hx⟩ : K) =
            ⟨x, hx⟩ := Subtype.ext (show projK R W W' hc ((w : V) + x) = x by rw [map_add, hπw, zero_add, hπx])
        rw [e, hρ, hw]
      · rw [map_add, hπw, zero_add, hπx]
  · have hglue : glueLat hc K (glueMap hc hM hK) = N := by
      ext v; exact (mem_iff_glueCond hc hM hK v).symm
    constructor
    · intro h
      exact (lemma681 hc hM hK).unique h hglue
    · rintro rfl
      exact hglue

end QuadFormsKB.Kitaoka.Glue
