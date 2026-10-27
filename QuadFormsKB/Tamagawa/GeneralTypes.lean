/-
# Local types for a general base lattice and an imprimitive base vector

**Layer:** the completion $F_\mathfrak p$ of a number field at a finite prime, the split space
$V_\mathfrak p = F_\mathfrak p e_0 \perp (F_\mathfrak p^n, Q')$ with $Q = \langle m\rangle\perp Q'$ (`splitForm m Q'`), and the group
$H = O(Q')(F_\mathfrak p)$ acting through $\mathrm{diag}(1,\cdot)$ (`orthEmb`).

The local type set (`LocCompSet`) is $Y_\mathfrak p = \{M \in O(V_\mathfrak p)\,\mathfrak o_\mathfrak p^{n+1} : e_0 \in M\}$: the base lattice is the
standard split lattice and the base vector $e_0$ is primitive. For Weil's orbital Euler product (`OrbitalEulerProduct`)
the lattice is $\mathfrak b^{-1}L$ in coordinates adapted to a vector $\xi_\rho$ of norm $\rho$, so both must be general. This file
introduces, for an $\mathfrak o_\mathfrak p$-lattice $\Lambda \subset F_\mathfrak p^{n+1}$ and a scalar $c \in F_\mathfrak p$,
$$Y_\mathfrak p(\Lambda, c) = \{M \in O(V_\mathfrak p)\,\Lambda : c\,e_0 \in M\}\qquad(\texttt{LocCompSetG}),$$
its local weights $w(M) = [K_0' : K_M\cap K_0']/[K_M : K_M\cap K_0']$ (`locWeightG`, the same index ratio as `locWeight`) and
the local type sum $W_\mathfrak p(\Lambda, c) = \sum_t w(M_t)$ (`locTypeSumG`).

**Proves**
* `locWeightG_smul`: the weights do not depend on the representative of a type (the unimodularity, `modRatio_eq_one`).
* `finsum_orbit_congr`, `locTypeSumG_congr`: type sums are invariant under equivariant bijections (a general lemma).
* `locTypeSumG_unit`: $W_\mathfrak p(\Lambda, uc) = W_\mathfrak p(\Lambda, c)$ for a unit $u$ (the type set only sees $\mathrm{ord}\,c$).
* `locTypeSumG_transport`: transport along $D = \mathrm{diag}(d, 1, \dots, 1)$, an isometry from $\langle d^2m\rangle\perp Q'$ to
  $\langle m\rangle\perp Q'$: $W_\mathfrak p^{d^2m}(\Lambda, c) = W_\mathfrak p^{m}(D\Lambda, dc)$.
* `locTypeSumG_eq_one_of_transitive`, `exists_smul_stdPtG`: one type of weight $1$ at the standard lattice when
  $2m$ is a unit (`exists_smul_locStdPt`, for $m \in F_\mathfrak p$ with an integral model).

Sources: Weil 1982, §3.4–3.5 [unverified locator]; Kitaoka 1993, §5.6 [unverified]; O'Meara 1963, §92 [unverified]. Indices are
0-based ($e_0$ is the first basis vector).
-/
import QuadFormsKB.Tamagawa.LocalUnimodular

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices LocalDensity QuadForm

/-! ### Type sums are invariant under equivariant bijections -/

section Congr

variable {H X Y : Type*} [Group H] [MulAction H X] [MulAction H Y]

/-- **Sums over orbit representatives are invariant under equivariant bijections**: if $e : X \to Y$ is an $H$-equivariant
bijection, $w_X$ is $H$-invariant and $w_Y(e\,x) = w_X(x)$, then $\sum_{t\in H\backslash X}w_X(x_t) = \sum_{s\in H\backslash Y}w_Y(y_s)$
for any choice of representatives (`Quotient.out`). -/
theorem finsum_orbit_congr (e : X ≃ Y) (he : ∀ (h : H) (x : X), e (h • x) = h • e x) (wX : X → ℝ) (wY : Y → ℝ)
    (hw : ∀ x, wY (e x) = wX x) (hinv : ∀ (h : H) (x : X), wX (h • x) = wX x) :
    ∑ᶠ t : orbitRel.Quotient H X, wX t.out = ∑ᶠ s : orbitRel.Quotient H Y, wY s.out := by
  have hinvY : ∀ (h : H) (y : Y), wY (h • y) = wY y := by
    intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← he, hw, hw, hinv]
  have hrel : ∀ a b : X, a ∈ orbit H b ↔ e a ∈ orbit H (e b) := by
    intro a b
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨h, (he h b).symm⟩
    · rintro ⟨h, hh⟩
      refine ⟨h, e.injective ?_⟩
      rw [he]; exact hh
  let E : orbitRel.Quotient H X ≃ orbitRel.Quotient H Y :=
    { toFun := Quotient.map' e fun a b hab => (hrel a b).mp hab
      invFun := Quotient.map' e.symm fun a b hab => by
        have := (hrel (e.symm a) (e.symm b)).mpr
        simp only [Equiv.apply_symm_apply] at this
        exact this hab
      left_inv := fun t => by
        induction t using Quotient.inductionOn' with | h x => ?_
        exact congrArg (Quotient.mk'' (s₁ := orbitRel H X)) (e.symm_apply_apply x)
      right_inv := fun s => by
        induction s using Quotient.inductionOn' with | h y => ?_
        exact congrArg (Quotient.mk'' (s₁ := orbitRel H Y)) (e.apply_symm_apply y) }
  rw [← finsum_comp_equiv E]
  refine finsum_congr fun t => ?_
  -- `(E t).out` and `e t.out` lie in one orbit
  have h1 : (Quotient.mk'' (e t.out) : orbitRel.Quotient H Y) = E t := by
    conv_rhs => rw [← Quotient.out_eq' t]
    rfl
  have h2 : (E t).out ∈ orbit H (e t.out) := by
    rw [← h1]
    exact orbitRel_apply.mp (Quotient.exact' (Quotient.out_eq' _))
  obtain ⟨h, hh⟩ := h2
  rw [← hh, hinvY, hw]

end Congr

/-! ### The general local type set -/

section GenTypes

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)

local notation "QS" => splitForm m Q'
local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The general local type set** $Y_\mathfrak p(\Lambda, c) = \{M \in O(V_\mathfrak p)\,\Lambda : c\,e_0 \in M\}$ for an $\mathfrak o_\mathfrak p$-lattice
$\Lambda \subset F_\mathfrak p^{n+1}$ and $c \in F_\mathfrak p$, $V = (F^{n+1}, \langle m\rangle\perp Q')$. `LocCompSet` is $\Lambda = \mathfrak o_\mathfrak p^{n+1}$,
$c = 1$. The group $O(Q')(F_\mathfrak p)$ acts through $\mathrm{diag}(1,\cdot)$, which fixes $c\,e_0$; its orbits are the **local types**
of the pairs (lattice of the local genus of $\Lambda$, vector $c\,e_0$) (Weil 1982, §3.4 [unverified]). -/
@[kb "weil1982" "§3.4 (local types, general lattice) [unverified]"]
def LocCompSetG (Λ : Submodule 𝔬 (Fin (n + 1) → Fv)) (c : Fv) : Type _ :=
  {M : Submodule 𝔬 (Fin (n + 1) → Fv) //
    (∃ g : orthGroup QS Fv, locAct v (g : GL (Fin (n + 1)) Fv) Λ = M) ∧ c • (e₀ : Fin (n + 1) → Fv) ∈ M}

theorem orthEmb_mulVec_smul_e₀ (h : orthGroup Q' Fv) (c : Fv) :
    (orthEmb m Q' Fv h : GL (Fin (n + 1)) Fv).val *ᵥ (c • (e₀ : Fin (n + 1) → Fv)) = c • e₀ := by
  rw [mulVec_smul, orthEmb_mulVec_e₀]

instance LocCompSetG.instMulAction (Λ : Submodule 𝔬 (Fin (n + 1) → Fv)) (c : Fv) :
    MulAction (orthGroup Q' Fv) (LocCompSetG v m Q' Λ c) where
  smul h M := ⟨locAct v (orthEmb m Q' Fv h : GL (Fin (n + 1)) Fv) M.1, by
      obtain ⟨g, hg⟩ := M.2.1
      exact ⟨orthEmb m Q' Fv h * g, by rw [Subgroup.coe_mul, locAct_mul, hg]⟩,
    ⟨c • e₀, M.2.2, orthEmb_mulVec_smul_e₀ v m Q' h c⟩⟩
  one_smul M := Subtype.ext (by
    show locAct v (orthEmb m Q' Fv 1 : GL (Fin (n + 1)) Fv) M.1 = M.1
    rw [map_one, OneMemClass.coe_one, locAct_one])
  mul_smul a b M := Subtype.ext (by
    show locAct v (orthEmb m Q' Fv (a * b) : GL (Fin (n + 1)) Fv) M.1 =
      locAct v (orthEmb m Q' Fv a : GL (Fin (n + 1)) Fv) (locAct v (orthEmb m Q' Fv b : GL (Fin (n + 1)) Fv) M.1)
    rw [map_mul, Subgroup.coe_mul, locAct_mul])

theorem LocCompSetG.smul_val {Λ : Submodule 𝔬 (Fin (n + 1) → Fv)} {c : Fv} (h : orthGroup Q' Fv)
    (M : LocCompSetG v m Q' Λ c) : (h • M).1 = locAct v (orthEmb m Q' Fv h : GL (Fin (n + 1)) Fv) M.1 := rfl

/-- **The local weight** of $M \in Y_\mathfrak p(\Lambda, c)$: $w(M) = [K_0' : K_M\cap K_0']/[K_M : K_M\cap K_0']$,
$K_M = \mathrm{Stab}_{O(Q')(F_\mathfrak p)}(M)$, $K_0' = O(\mathfrak o_\mathfrak p^n)$ (as `locWeight`). -/
@[kb "weil1982" "§3.5 (local weights) [unverified locator]"]
def locWeightG {Λ : Submodule 𝔬 (Fin (n + 1) → Fv)} {c : Fv} (M : LocCompSetG v m Q' Λ c) : ℝ :=
  ((stabilizer (orthGroup Q' Fv) M).relIndex (stdStab Q' v) : ℝ) /
    ((stdStab Q' v).relIndex (stabilizer (orthGroup Q' Fv) M) : ℝ)

/-- **The general local types**: the $O(Q')(F_\mathfrak p)$-orbits on $Y_\mathfrak p(\Lambda, c)$. -/
abbrev LocTypesG (Λ : Submodule 𝔬 (Fin (n + 1) → Fv)) (c : Fv) : Type _ :=
  orbitRel.Quotient (orthGroup Q' Fv) (LocCompSetG v m Q' Λ c)

/-- **The general local type sum** $W_\mathfrak p(\Lambda, c) = \sum_t w(M_t)$ over the local types, $M_t$ = `t.out`
(independent of the representatives, `locWeightG_smul`). A `finsum`: $0$ if there are infinitely many types. -/
@[kb "weil1982" "§3.5 (local type sum) [unverified locator]"]
def locTypeSumG (Λ : Submodule 𝔬 (Fin (n + 1) → Fv)) (c : Fv) : ℝ :=
  ∑ᶠ t : LocTypesG v m Q' Λ c, locWeightG v m Q' t.out

/-- The stabilizer of $M$ in $O(Q')(F_\mathfrak p)$ is the stabilizer of the lattice $M$ under $\mathrm{diag}(1,\cdot)$. -/
theorem stabilizer_locCompSetG {Λ : Submodule 𝔬 (Fin (n + 1) → Fv)} {c : Fv} (M : LocCompSetG v m Q' Λ c) :
    stabilizer (orthGroup Q' Fv) M =
      stabLat v ((orthGroup QS Fv).subtype.comp (orthEmb m Q' Fv)) M.1 := by
  ext g
  rw [mem_stabilizer_iff]
  constructor
  · intro hg; exact congrArg Subtype.val hg
  · intro hg; exact Subtype.ext hg

theorem stdStab_eq_stabLat_split :
    stdStab Q' v = stabLat v ((orthGroup QS Fv).subtype.comp (orthEmb m Q' Fv)) (std v) := by
  ext g
  exact (mem_stdStab_orthEmb_iff m Q' v g).symm

/-- **The weights do not depend on the representative of a type**: $w(hM) = \Delta(h)\,w(M) = w(M)$ for $h \in O(Q')(F_\mathfrak p)$
(`modRatio_eq_one`; the stabilizers are stabilizers of lattices, hence commensurable). -/
@[kb "weil1982" "§3.5 (independence of the representative) [unverified locator]"]
theorem locWeightG_smul (hQ' : Q'.Nondegenerate) {Λ : Submodule 𝔬 (Fin (n + 1) → Fv)}
    (hΛ : Λ.IsLattice Fv) {c : Fv} (h : orthGroup Q' Fv) (M : LocCompSetG v m Q' Λ c) :
    locWeightG v m Q' (h • M) = locWeightG v m Q' M := by
  set ψ : orthGroup Q' Fv →* GL (Fin (n + 1)) Fv := (orthGroup QS Fv).subtype.comp (orthEmb m Q' Fv)
  have hlat : ∀ N : LocCompSetG v m Q' Λ c, N.1.IsLattice Fv := by
    intro N
    obtain ⟨g, hg⟩ := N.2.1
    rw [← hg]; exact locAct_isLattice _ hΛ
  have hK₀ : stdStab Q' v = stabLat v ψ (std v) := stdStab_eq_stabLat_split v m Q'
  have hmod := modRatio_eq_one v Q' hQ' h
  unfold modRatio at hmod
  show relRatio (stdStab Q' v) (stabilizer _ (h • M)) = relRatio (stdStab Q' v) (stabilizer _ M)
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  have hstd : (std v : Submodule 𝔬 (Fin (n + 1) → Fv)).IsLattice Fv := std_isLattice v
  have hc1 : Commens (stdStab Q' v) ((stdStab Q' v).map (MulAut.conj h).toMonoidHom) := by
    rw [hK₀, stabLat_map_conj]; exact commens_stabLat v ψ hstd (locAct_isLattice _ hstd)
  have hc2 : Commens ((stdStab Q' v).map (MulAut.conj h).toMonoidHom)
      ((stabilizer (orthGroup Q' Fv) M).map (MulAut.conj h).toMonoidHom) := by
    rw [hK₀, stabilizer_locCompSetG, stabLat_map_conj, stabLat_map_conj]
    exact commens_stabLat v ψ (locAct_isLattice _ hstd) (locAct_isLattice _ (hlat _))
  have hc3 : Commens (stdStab Q' v)
      ((stabilizer (orthGroup Q' Fv) M).map (MulAut.conj h).toMonoidHom) := by
    rw [hK₀, stabilizer_locCompSetG, stabLat_map_conj]; exact commens_stabLat v ψ hstd (locAct_isLattice _ (hlat _))
  rw [← relRatio_mul hc1 hc2 hc3, hmod, one_mul, relRatio_map (MulAut.conj h).injective]

/-- **Type sums are invariant under equivariant bijections** of general type sets (possibly for different $m$, $\Lambda$, $c$, with
the same $Q'$): the weights only see the stabilizers, which an equivariant bijection preserves. -/
theorem locTypeSumG_congr (hQ' : Q'.Nondegenerate) {m₂ : F} {Λ Λ₂ : Submodule 𝔬 (Fin (n + 1) → Fv)}
    (hΛ : Λ.IsLattice Fv) {c c₂ : Fv} (e : LocCompSetG v m Q' Λ c ≃ LocCompSetG v m₂ Q' Λ₂ c₂)
    (he : ∀ (h : orthGroup Q' Fv) M, e (h • M) = h • e M) :
    locTypeSumG v m Q' Λ c = locTypeSumG v m₂ Q' Λ₂ c₂ := by
  refine finsum_orbit_congr e he _ _ (fun M => ?_) (fun h M => locWeightG_smul v m Q' hQ' hΛ h M)
  have hs : stabilizer (orthGroup Q' Fv) (e M) = stabilizer (orthGroup Q' Fv) M := by
    ext g
    rw [mem_stabilizer_iff, mem_stabilizer_iff, ← he]
    exact e.injective.eq_iff
  unfold locWeightG
  rw [hs]

/-- **Only $\mathrm{ord}\,c$ matters**: for a unit $u$ of $\mathfrak o_\mathfrak p$, $Y_\mathfrak p(\Lambda, uc) = Y_\mathfrak p(\Lambda, c)$, so the type sums agree. -/
theorem locTypeSumG_unit (hQ' : Q'.Nondegenerate) {Λ : Submodule 𝔬 (Fin (n + 1) → Fv)} (hΛ : Λ.IsLattice Fv)
    (c : Fv) (u : 𝔬ˣ) : locTypeSumG v m Q' Λ ((u : 𝔬) * c) = locTypeSumG v m Q' Λ c := by
  have hiff : ∀ M : Submodule 𝔬 (Fin (n + 1) → Fv),
      ((u : 𝔬) * c) • (e₀ : Fin (n + 1) → Fv) ∈ M ↔ c • (e₀ : Fin (n + 1) → Fv) ∈ M := by
    intro M
    have e1 : ((u : 𝔬) * c) • (e₀ : Fin (n + 1) → Fv) = (u : 𝔬) • (c • (e₀ : Fin (n + 1) → Fv)) := by
      rw [mul_smul]; rfl
    rw [e1]
    constructor
    · intro hM
      have := M.smul_mem ((u⁻¹ : 𝔬ˣ) : 𝔬) hM
      rwa [smul_smul, Units.inv_mul, one_smul] at this
    · intro hM; exact M.smul_mem _ hM
  refine (locTypeSumG_congr v m Q' hQ' hΛ
    { toFun := fun M => ⟨M.1, M.2.1, (hiff M.1).mp M.2.2⟩
      invFun := fun M => ⟨M.1, M.2.1, (hiff M.1).mpr M.2.2⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl } fun h M => rfl)

end GenTypes

/-! ### Transport along $D = \mathrm{diag}(d, 1, \dots, 1)$ -/

section Transport

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Q' : QuadForm F n)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $D = \mathrm{diag}(d, 1, \dots, 1)$ as an element of $\mathrm{GL}_{n+1}(F_\mathfrak p)$, $d \ne 0$. -/
def diagD {d : Fv} (hd : d ≠ 0) : GL (Fin (n + 1)) Fv :=
  ⟨cornerMat d 1, cornerMat d⁻¹ 1, by rw [cornerMat_mul, mul_inv_cancel₀ hd, Matrix.one_mul, cornerMat_one],
    by rw [cornerMat_mul, inv_mul_cancel₀ hd, Matrix.one_mul, cornerMat_one]⟩

theorem diagD_val {d : Fv} (hd : d ≠ 0) : (diagD v (n := n) hd).val = cornerMat d 1 := rfl

theorem diagD_inv_val {d : Fv} (hd : d ≠ 0) : ((diagD v (n := n) hd)⁻¹).val = cornerMat d⁻¹ 1 := rfl

theorem diagD_mulVec_e₀ {d : Fv} (hd : d ≠ 0) (c : Fv) :
    (diagD v (n := n) hd).val *ᵥ (c • (e₀ : Fin (n + 1) → Fv)) = (d * c) • e₀ := by
  rw [diagD_val, mulVec_smul, e₀, cornerMat_mulVec, Matrix.one_mulVec, mul_one]
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [mul_comm]

/-- **$D$ is an isometry** $\langle d^2m\rangle\perp Q' \to \langle m\rangle\perp Q'$: $Q_m(Dx) = Q_{d^2m}(x)$. -/
theorem evalIn_diagD (m : F) {m₂ : F} {d : Fv} (hd : d ≠ 0) (hdm : algebraMap F Fv m * d ^ 2 = algebraMap F Fv m₂)
    (x : Fin (n + 1) → Fv) :
    (splitForm m Q').evalIn Fv ((diagD v (n := n) hd).val *ᵥ x) = (splitForm m₂ Q').evalIn Fv x := by
  rw [← Fin.cons_self_tail x, diagD_val, cornerMat_mulVec, Matrix.one_mulVec, evalIn_splitForm, evalIn_splitForm,
    ← hdm]
  ring

/-- Conjugation by $D$ maps $O(\langle d^2m\rangle\perp Q')$ to $O(\langle m\rangle\perp Q')$. -/
theorem conj_diagD_mem (m : F) {m₂ : F} {d : Fv} (hd : d ≠ 0)
    (hdm : algebraMap F Fv m * d ^ 2 = algebraMap F Fv m₂) (g : orthGroup (splitForm m₂ Q') Fv) :
    diagD v (n := n) hd * (g : GL (Fin (n + 1)) Fv) * (diagD v hd)⁻¹ ∈ orthGroup (splitForm m Q') Fv := by
  refine mem_orthGroup_of_evalIn _ fun z => ?_
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, evalIn_diagD v Q' m hd hdm,
    evalIn_mulVec_of_mem _ g.2]
  conv_rhs => rw [← mulVec_inv_mulVec (diagD v (n := n) hd) z]
  rw [evalIn_diagD v Q' m hd hdm]

theorem diagD_mul_orthEmb (m m₂ : F) {d : Fv} (hd : d ≠ 0) (h : orthGroup Q' Fv) :
    diagD v (n := n) hd * (orthEmb m₂ Q' Fv h : GL (Fin (n + 1)) Fv) =
      (orthEmb m Q' Fv h : GL (Fin (n + 1)) Fv) * diagD v hd := by
  ext1
  rw [Units.val_mul, Units.val_mul, orthEmb_val, orthEmb_val, diagD_val, cornerMat_mul, cornerMat_mul,
    Matrix.one_mul, Matrix.mul_one, mul_one, one_mul]

/-- **Transport of local types along $D$**: $Y^{d^2m}_\mathfrak p(\Lambda, c) \simeq Y^m_\mathfrak p(D\Lambda, dc)$, $M \mapsto DM$, equivariantly
for $O(Q')(F_\mathfrak p)$ ($D$ commutes with $\mathrm{diag}(1, h)$). -/
def transportEquiv (m : F) {m₂ : F} {d : Fv} (hd : d ≠ 0) (hdm : algebraMap F Fv m * d ^ 2 = algebraMap F Fv m₂)
    (Λ : Submodule 𝔬 (Fin (n + 1) → Fv)) (c : Fv) :
    LocCompSetG v m₂ Q' Λ c ≃ LocCompSetG v m Q' (locAct v (diagD v hd) Λ) (d * c) where
  toFun M := ⟨locAct v (diagD v hd) M.1, by
      obtain ⟨g, hg⟩ := M.2.1
      refine ⟨⟨_, conj_diagD_mem v Q' m hd hdm g⟩, ?_⟩
      show locAct v (diagD v hd * (g : GL (Fin (n + 1)) Fv) * (diagD v hd)⁻¹) (locAct v (diagD v hd) Λ) = _
      rw [← locAct_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, locAct_mul, hg],
    ⟨c • e₀, M.2.2, diagD_mulVec_e₀ v hd c⟩⟩
  invFun M := ⟨locAct v (diagD v hd)⁻¹ M.1, by
      obtain ⟨g, hg⟩ := M.2.1
      have hmem : (diagD v hd)⁻¹ * (g : GL (Fin (n + 1)) Fv) * (diagD v hd) ∈ orthGroup (splitForm m₂ Q') Fv := by
        refine mem_orthGroup_of_evalIn _ fun z => ?_
        rw [← evalIn_diagD v Q' m hd hdm, ← evalIn_diagD v Q' m hd hdm, Units.val_mul, Units.val_mul,
          ← mulVec_mulVec, ← mulVec_mulVec]
        rw [show (diagD v (n := n) hd).val *ᵥ ((diagD v hd)⁻¹.val *ᵥ ((g : GL (Fin (n + 1)) Fv).val *ᵥ
          ((diagD v hd).val *ᵥ z))) = (g : GL (Fin (n + 1)) Fv).val *ᵥ ((diagD v hd).val *ᵥ z) by
            rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec],
          evalIn_mulVec_of_mem _ g.2]
      refine ⟨⟨_, hmem⟩, ?_⟩
      show locAct v ((diagD v hd)⁻¹ * (g : GL (Fin (n + 1)) Fv) * (diagD v hd)) Λ = _
      rw [locAct_mul, locAct_mul, hg],
    ⟨(d * c) • e₀, M.2.2, by
      show (diagD v hd)⁻¹.val *ᵥ ((d * c) • (e₀ : Fin (n + 1) → Fv)) = c • e₀
      rw [← diagD_mulVec_e₀ v hd c, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]⟩⟩
  left_inv M := Subtype.ext (locAct_inv_locAct _ _)
  right_inv M := Subtype.ext (by
    show locAct v (diagD v hd) (locAct v (diagD v hd)⁻¹ M.1) = M.1
    rw [← locAct_mul, mul_inv_cancel, locAct_one])

/-- **Transport of type sums along $D = \mathrm{diag}(d, 1, \dots, 1)$**: $W^{d^2m}_\mathfrak p(\Lambda, c) = W^m_\mathfrak p(D\Lambda, dc)$. -/
theorem locTypeSumG_transport (hQ' : Q'.Nondegenerate) (m : F) {m₂ : F} {d : Fv} (hd : d ≠ 0)
    (hdm : algebraMap F Fv m * d ^ 2 = algebraMap F Fv m₂) {Λ : Submodule 𝔬 (Fin (n + 1) → Fv)}
    (hΛ : Λ.IsLattice Fv) (c : Fv) :
    locTypeSumG v m₂ Q' Λ c = locTypeSumG v m Q' (locAct v (diagD v hd) Λ) (d * c) := by
  refine locTypeSumG_congr v m₂ Q' hQ' hΛ (transportEquiv v Q' m hd hdm Λ c) fun h M => Subtype.ext ?_
  show locAct v (diagD v hd) (locAct v _ M.1) = locAct v _ (locAct v (diagD v hd) M.1)
  rw [← locAct_mul, ← locAct_mul, diagD_mul_orthEmb]

end Transport

end QuadFormsKB.Tamagawa
