/-
# Representations of quadratic lattices by quadratic lattices: definitions

**Layer:** a number field $F$; the quadratic space $V = (F^N, Q)$ with a lattice $L$ (`Lat F N`, any Steinitz class), and a second
quadratic space $(F^r, T)$ with a lattice $T_\ell$ (`Lat F r`, any Steinitz class): the **quadratic lattice** $T = (T_\ell, T)$ of rank $r$.
Every projective $\mathcal O_F$-module $\mathfrak a_0x_0\oplus\dots\oplus\mathfrak a_{r-1}x_{r-1}$ with a quadratic form is isometric to such a
pair (take an $F$-basis of $F\otimes T$; the coefficient ideals become the lattice $T_\ell$). For $T_\ell = \mathcal O_F^r$ everything
below is the notion for the form $T$; for $T = \mathfrak a\langle m\rangle$ ($r = 1$),
$T_\ell = \mathfrak a \subseteq F$.

**Defines**
* `repCountLat Q M Tl T` $= r(M, T) = \#\{X \in F^{N\times r} : Q\circ X = T,\ X\,T_\ell \subseteq M\}$, the number of **isometric
  embeddings** $T \to M$ (a linear map $F^r \to F^N$ is its matrix $X$; $X$ is injective when $T$ is nondegenerate); `repMassLat Q L Tl T`
  $= \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)} r(M, T)/|O(M)|$;
* `latBetaT v Q₀ L T₀ Tl` $= \beta_\mathfrak p(L, T)$, **the local density of $T_\mathfrak p$ in $L_\mathfrak p$**: for local free models
  $L_\mathfrak p = A\mathfrak o_\mathfrak p^N$, $T_{\ell,\mathfrak p} = B\mathfrak o_\mathfrak p^r$ (`SiegelLat.IsLocModel`; $A$, $B$ global matrices with integral Gram forms),
  $$\beta_\mathfrak p(L, T) = \|\det A\|_\mathfrak p^{\,r}\,\|\det B\|_\mathfrak p^{\,r+1-N}\,\beta_\mathfrak p(Q_0\circ A,\ T_0\circ B),$$
  i.e. $\lim_U \mathrm{vol}\{X \in \mathrm{Hom}(T_\mathfrak p, L_\mathfrak p) : Q\circ X \in U\}/\mathrm{vol}(U)$ for the Haar measures of $F_\mathfrak p^{N\times r}$ and of
  $\mathrm{Sym}_r(F_\mathfrak p)$ giving the integral matrices volume $1$ **in the ambient coordinates** (those in which the archimedean density
  of `siegelProductAll` is computed): $X = AYB^{-1}$ scales the volume by $\|\det A\|^r\|\det B\|^{-N}$, and $S \mapsto B^{\mathsf T}SB$ by
  $\|\det B\|^{r+1}$. Independent of the models (`latBetaT_eq_of_loc`, `FrameLatLocal.lean`). $0$ if there is no integral model.
* `siegelDensityLat` $= \varepsilon_{N,r}\,\beta_\mathfrak p(L, T)$ (Siegel's $\varepsilon = \tfrac12$ for $r = N$);
* `LocFrameSetL v T Q' Λ Θ` $= \{M \in O(T\perp Q')(F_\mathfrak p)\,\Lambda : E\,\Theta \subseteq M\}$, the local type set of a lattice $T$
  ($\Theta = T_{\ell,\mathfrak p}$, $E$ the standard frame), with the action of $O(Q')(F_\mathfrak p)$ through $\mathrm{diag}(1_r, \cdot)$;
  `locFrameWeightL`, `locFrameTypeSumL` $W_\mathfrak p(\Lambda, \Theta)$ (as the `locFrameTypeSumG`, which is the case
  $\Theta = \mathfrak o_\mathfrak p^r$).

Sources: Siegel 1935, §1; Kitaoka 1993, §5.6 (local densities of lattices) and §6.8 [unverified]; O'Meara 1963, 81:5, p. 212
(Steinitz). Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameSiegelAll
import QuadFormsKB.Tamagawa.SiegelLat

open NumberField IsDedekindDomain Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.FramesLat

open QuadFormsKB.Tamagawa Lattices LocalDensity Frames SiegelLat QuadFormsKB.HilbertModular

/-! ### Representation numbers of lattices -/

section RepCount

variable {F : Type*} [Field F] [NumberField F] {N r : ℕ} (Q : QuadForm F N)

/-- **The number of isometric embeddings** $r(M, T)$ of the quadratic lattice $T = (T_\ell, T)$ into $M$:
$\#\{X \in F^{N\times r} : X\,T_\ell \subseteq M,\ Q\circ X = T\}$ (Siegel 1935, §1 [unverified]; O'Meara 1963, §82A, p. 220, for $r = 1$).
For $T_\ell = \mathcal O_F^r$ it is `repCountT` (`repCountLat_stdLat`). -/
@[kb "siegel1935" "§1 (representation numbers of lattices) [unverified]"]
def repCountLat (M : Lat F N) (Tl : Lat F r) (T : QuadForm F r) : ℕ :=
  Nat.card {X : Matrix (Fin N) (Fin r) F // (∀ t ∈ Tl.1, X *ᵥ t ∈ M.1) ∧ Q.compMat X = T}

/-- **Isometric lattices have the same number of embeddings:** $r(\gamma M, T) = r(M, T)$ for $\gamma \in O(V)(F)$. -/
theorem repCountLat_glImage {γ : GL (Fin N) F} (hγ : γ ∈ orthGroup Q F) (M : Lat F N) (Tl : Lat F r)
    (T : QuadForm F r) : repCountLat Q (Lat.image γ M) Tl T = repCountLat Q M Tl T := by
  refine Nat.card_congr
    { toFun := fun X => ⟨γ⁻¹.val * X.1, ?_, ?_⟩
      invFun := fun X => ⟨γ.val * X.1, ?_, ?_⟩
      left_inv := fun X => Subtype.ext (by
        show γ.val * (γ⁻¹.val * X.1) = X.1
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
      right_inv := fun X => Subtype.ext (by
        show γ⁻¹.val * (γ.val * X.1) = X.1
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]) }
  · intro t ht
    obtain ⟨y, hy, hyv⟩ := (mem_glImage).mp (X.2.1 t ht)
    rw [← Matrix.mulVec_mulVec, ← hyv, mulVec_mulVec, Units.inv_mul, one_mulVec]; exact hy
  · rw [compMat_orth Q ((orthGroup Q F).inv_mem hγ)]; exact X.2.2
  · intro t ht
    rw [← Matrix.mulVec_mulVec]; exact mulVec_mem_glImage (X.2.1 t ht)
  · rw [compMat_orth Q hγ]; exact X.2.2

theorem repCountLat_of_isIsometric {M M' : Lat F N} (h : IsIsometric Q M.1 M'.1) (Tl : Lat F r) (T : QuadForm F r) :
    repCountLat Q M Tl T = repCountLat Q M' Tl T := by
  obtain ⟨γ, hγ, he⟩ := h
  rw [← repCountLat_glImage Q hγ M Tl T]
  congr 1
  exact Lattices.Lat.ext he

/-- $r(M, T)$ of a class. -/
def LatClass.repCountLat (c : LatClass Q) (Tl : Lat F r) (T : QuadForm F r) : ℕ :=
  Quotient.lift (fun M : Lat F N => FramesLat.repCountLat Q M Tl T)
    (fun _ _ h => repCountLat_of_isIsometric Q h Tl T) c

/-- **The weighted number of embeddings of $T$ into the genus of $L$:**
$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)} r(M, T)/|O(M)|$ ($O(M)$ including improper automorphisms). -/
@[kb "siegel1935" "§1 (genus average, lattices) [unverified]"]
def repMassLat (L : Lat F N) (Tl : Lat F r) (T : QuadForm F r) : ℝ :=
  ∑ᶠ c ∈ genusClasses Q L, (LatClass.repCountLat Q c Tl T : ℝ) / LatClass.autCard Q c

end RepCount

/-! ### The local density of a lattice in a lattice -/

section Beta

variable {F : Type} [Field F] [NumberField F] {N r : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

open Classical in
/-- **$\beta_\mathfrak p(L, T)$, the local density of the quadratic lattice $T = (T_\ell, T_0)$ in $L$** (Kitaoka 1993, §5.6 [unverified]),
for the Haar measures normalized in the ambient coordinates (module docstring):
$\|\det A\|^r\|\det B\|^{r+1}\|\det B\|^{-N}\beta_\mathfrak p(Q_0\circ A, T_0\circ B)$ for local free models $A$ of $L$ and $B$ of $T_\ell$
at $\mathfrak p$ with integral Gram forms; $0$ if there are none. Independent of the models (`latBetaT_eq_of_loc`). -/
@[kb "kitaoka1993" "§5.6 (local densities of lattices) [unverified]"]
def latBetaT (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (T₀ : QuadForm (𝓞 F) r) (Tl : Lat F r) : ℝ :=
  if h : (∃ A, IsLocModel v L A ∧ Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) ∧
      (∃ B, IsLocModel v Tl B ∧ Lattices.IsIntegral (formF T₀) (Lattices.latOf B)) then
    ‖algebraMap F Fv h.1.choose.val.det‖ ^ r *
      (‖algebraMap F Fv h.2.choose.val.det‖ ^ (r + 1) / ‖algebraMap F Fv h.2.choose.val.det‖ ^ N) *
      NF.localDensityForm v (gramZ (formF Q₀) h.1.choose h.1.choose_spec.2)
        (gramZ (formF T₀) h.2.choose h.2.choose_spec.2)
  else 0

/-- **Siegel's normalization of $\beta_\mathfrak p(L, T)$:** $\varepsilon_{N,r}\,\beta_\mathfrak p(L, T)$, $\varepsilon = \tfrac12$ for $r = N$ (`epsNR`). -/
def siegelDensityLat (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (T₀ : QuadForm (𝓞 F) r) (Tl : Lat F r) : ℝ :=
  epsNR N r * latBetaT v Q₀ L T₀ Tl

end Beta

/-! ### Local types of frames of a lattice -/

section LocalTypesL

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T : QuadForm F r)
  (Q' : QuadForm F n') (Λ : Submodule (v.adicCompletionIntegers F) (Fin (r + n') → v.adicCompletion F))
  (Θ : Submodule (v.adicCompletionIntegers F) (Fin r → v.adicCompletion F))

local notation "QB" => blockForm T Q'
local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $\mathrm{diag}(1_r, h)$ fixes $E\,t$. -/
theorem orthEmbB_mulVec_stdFrameMat (h : orthGroup Q' Fv) (t : Fin r → Fv) :
    (orthEmbB T Q' Fv h : GL (Fin (r + n')) Fv).val *ᵥ ((stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t) =
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t := by
  rw [mulVec_mulVec]; exact congrArg (fun M => M *ᵥ t) (orthEmbB_mul_stdFrameMat T Q' Fv h)

/-- **The local type set of a lattice $T$ based at $\Lambda$:** $Y_\mathfrak p(\Lambda, \Theta) = \{M \in O(V)(F_\mathfrak p)\cdot\Lambda : E\,\Theta \subseteq M\}$
for $V = (F^{r+n'}, T\perp Q')$, $\Theta = T_{\ell,\mathfrak p}$ (Weil 1982, §3.4 [unverified]). For $\Theta = \mathfrak o_\mathfrak p^r$ it is `LocFrameSetG`. -/
@[kb "weil1982" "§3.4 (local types, lattices) [unverified]"]
def LocFrameSetL : Type _ :=
  {M : Submodule 𝔬 (Fin (r + n') → Fv) //
    (∃ g : orthGroup QB Fv, locAct v (g : GL (Fin (r + n')) Fv) Λ = M) ∧
      ∀ t ∈ Θ, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈ M}

theorem stdFrame_mem_locAct_orthEmbB (h : orthGroup Q' Fv) {M : Submodule 𝔬 (Fin (r + n') → Fv)}
    (hM : ∀ t ∈ Θ, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈ M) :
    ∀ t ∈ Θ, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈
      locAct v (orthEmbB T Q' Fv h : GL (Fin (r + n')) Fv) M :=
  fun t ht => ⟨_, hM t ht, orthEmbB_mulVec_stdFrameMat v T Q' h t⟩

instance LocFrameSetL.instMulAction : MulAction (orthGroup Q' Fv) (LocFrameSetL v T Q' Λ Θ) where
  smul h M := ⟨locAct v (orthEmbB T Q' Fv h : GL (Fin (r + n')) Fv) M.1, by
      obtain ⟨g, hg⟩ := M.2.1
      exact ⟨orthEmbB T Q' Fv h * g, by rw [Subgroup.coe_mul, locAct_mul, hg]⟩,
    stdFrame_mem_locAct_orthEmbB v T Q' Θ h M.2.2⟩
  one_smul M := Subtype.ext (by
    show locAct v (orthEmbB T Q' Fv 1 : GL (Fin (r + n')) Fv) M.1 = M.1
    rw [map_one, OneMemClass.coe_one, locAct_one])
  mul_smul a b M := Subtype.ext (by
    show locAct v (orthEmbB T Q' Fv (a * b) : GL (Fin (r + n')) Fv) M.1 =
      locAct v (orthEmbB T Q' Fv a : GL (Fin (r + n')) Fv) (locAct v (orthEmbB T Q' Fv b : GL (Fin (r + n')) Fv) M.1)
    rw [map_mul, Subgroup.coe_mul, locAct_mul])

theorem LocFrameSetL.smul_val (h : orthGroup Q' Fv) (M : LocFrameSetL v T Q' Λ Θ) :
    (h • M).1 = locAct v (orthEmbB T Q' Fv h : GL (Fin (r + n')) Fv) M.1 := rfl

/-- **The local types** of a lattice $T$ at $\mathfrak p$: the $O(Q')(F_\mathfrak p)$-orbits on $Y_\mathfrak p(\Lambda, \Theta)$. -/
abbrev LocFrameTypesL : Type _ := orbitRel.Quotient (orthGroup Q' Fv) (LocFrameSetL v T Q' Λ Θ)

/-- **The local weight** of $M \in Y_\mathfrak p(\Lambda, \Theta)$: $w_\mathfrak p(M) = [K_0' : K_M\cap K_0']/[K_M : K_M \cap K_0']$ with
$K_M = \mathrm{Stab}_{O(Q')(F_\mathfrak p)}(M)$, $K_0' = O(\mathfrak o_\mathfrak p^{n'})$ (the formula of `locFrameWeightG`). -/
def locFrameWeightL (M : LocFrameSetL v T Q' Λ Θ) : ℝ :=
  ((stabilizer (orthGroup Q' Fv) M).relIndex (stdStab Q' v) : ℝ) /
    ((stdStab Q' v).relIndex (stabilizer (orthGroup Q' Fv) M) : ℝ)

/-- **The local type sum** $W_\mathfrak p(\Lambda, \Theta) = \sum_t w_\mathfrak p(M_t)$ of a lattice $T$ ($M_t$ any representative of the type
$t$; the weights do not depend on it, `locFrameWeightL_smul`). -/
@[kb "weil1982" "§3.5 (local type sums, lattices) [unverified locator]"]
def locFrameTypeSumL : ℝ := ∑ᶠ t : LocFrameTypesL v T Q' Λ Θ, locFrameWeightL v T Q' Λ Θ t.out

end LocalTypesL

end QuadFormsKB.Tamagawa.FramesLat
