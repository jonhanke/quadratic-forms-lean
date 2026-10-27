/-
# O'Meara §64: global notation for idèles

**Setting.** $F$ is a number field (O'Meara's global field; function fields are outside the library). The idèle group
$J_F$ is Mathlib's `NumberField.IdeleGroup (𝓞 F) F`, the units of the adèle ring
$\mathbb A_F = \mathbb A_{F,\infty} \times \mathbb A_F^{\mathrm{fin}}$; the component of an idèle $i$ at a finite spot
$\mathfrak p$ is `ideleAt i 𝔭` $\in F_\mathfrak p$ and at an infinite spot $w$ it is `ideleAtInf i w` $\in F_w$. The
normalized valuation $\lvert\cdot\rvert_\mathfrak p$ is replaced by Mathlib's `Valued.v` (values $0$ and
$\exp(k)$, $k \in \mathbb Z$, an order-preserving reparametrization), so $\lvert x\rvert_\mathfrak p = 1$ is
`Valued.v x = 1`.

O'Meara's sets of spots $S$ (§33I, §64) are in practice Dedekind sets of discrete spots, and in §65 they consist of
non-dyadic discrete spots; here $S$ is a set of finite spots (`Set (HeightOneSpectrum (𝓞 F))`), so the infinite
spots always lie in $\Omega - S$.

**Defines**
* `sIdeles S` $= J_F^S$, the $S$-idèles: $\lvert i_\mathfrak p\rvert_\mathfrak p = 1$ for all $\mathfrak p \in S$
  (O'Meara §33I, p. 80), and `principalSIdeles S` $= P_F^S = J_F^S \cap P_F$ (p. 80);
* `kIdeles S` $= K_F^S$ (§64, p. 172): $\lvert i_\mathfrak p\rvert_\mathfrak p = 1$ for $\mathfrak p \in S$ and
  $i_\mathfrak p = 1$ for $\mathfrak p \in \Omega - S$;
* `ideleSupportedAt 𝔭` $= I_\mathfrak p$ (§64, p. 172): the idèles with $i_\mathfrak q = 1$ for all
  $\mathfrak q \ne \mathfrak p$ (the image of Mathlib's `IdeleGroup.ofAdicCompletion`).

**Proves** (§64, p. 172): $K^S$ is a subgroup of $J^S$ (`kIdeles_le_sIdeles`); $I_\mathfrak p$ is characterized by its
components (`mem_ideleSupportedAt_iff`); $\dot F_\mathfrak p \to I_\mathfrak p$ is an isomorphism
(`ideleSupportedAtEquiv`); $I_\mathfrak p \subseteq J^S$ if and only if $\mathfrak p \notin S$
(`ideleSupportedAt_le_sIdeles_iff`).
-/
import Mathlib
import QuadFormsKB.Citation

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F]

local notation "J" => IdeleGroup (𝓞 F) F

/-- The component $i_\mathfrak p \in F_\mathfrak p$ of an idèle $i$ at a finite spot $\mathfrak p$. -/
def ideleAt (i : J) (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F :=
  (i : AdeleRing (𝓞 F) F).2 v

/-- The component $i_w \in F_w$ of an idèle $i$ at an infinite spot $w$. -/
def ideleAtInf (i : J) (w : InfinitePlace F) : w.Completion :=
  (i : AdeleRing (𝓞 F) F).1 w

@[simp] theorem ideleAt_mul (i j : J) (v : HeightOneSpectrum (𝓞 F)) :
    ideleAt (i * j) v = ideleAt i v * ideleAt j v := rfl

@[simp] theorem ideleAt_one (v : HeightOneSpectrum (𝓞 F)) : ideleAt (1 : J) v = 1 := rfl

theorem ideleAt_inv (i : J) (v : HeightOneSpectrum (𝓞 F)) : ideleAt i⁻¹ v = (ideleAt i v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← ideleAt_mul]; simp

@[simp] theorem ideleAtInf_mul (i j : J) (w : InfinitePlace F) :
    ideleAtInf (i * j) w = ideleAtInf i w * ideleAtInf j w := rfl

@[simp] theorem ideleAtInf_one (w : InfinitePlace F) : ideleAtInf (1 : J) w = 1 := rfl

theorem ideleAtInf_inv (i : J) (w : InfinitePlace F) : ideleAtInf i⁻¹ w = (ideleAtInf i w)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← ideleAtInf_mul]; simp

theorem ideleAt_ofAdic_self (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    ideleAt (IdeleGroup.ofAdicCompletion (𝓞 F) F v x) v = x := by
  classical
  show (RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v
    (x : v.adicCompletion F) : Π v', v'.adicCompletion F) v = x
  exact Pi.mulSingle_eq_same v _

theorem ideleAt_ofAdic_ne (v v' : HeightOneSpectrum (𝓞 F)) (h : v' ≠ v) (x : (v.adicCompletion F)ˣ) :
    ideleAt (IdeleGroup.ofAdicCompletion (𝓞 F) F v x) v' = 1 := by
  classical
  show (RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v
    (x : v.adicCompletion F) : Π v', v'.adicCompletion F) v' = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem ideleAtInf_ofAdic (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) (x : (v.adicCompletion F)ˣ) :
    ideleAtInf (IdeleGroup.ofAdicCompletion (𝓞 F) F v x) w = 1 := rfl

/-- **The $S$-idèles** $J_F^S$ (O'Meara 1963, §33I, p. 80): the idèles $i$ with $\lvert i_\mathfrak p\rvert_\mathfrak p
= 1$ for every $\mathfrak p \in S$ (a subgroup of $J_F$). -/
@[kb "omeara1963" "§33I, p. 80 (the S-idèles J_F^S)"]
def sIdeles (S : Set (HeightOneSpectrum (𝓞 F))) : Subgroup J where
  carrier := {i | ∀ v ∈ S, Valued.v (ideleAt i v) = 1}
  mul_mem' := by
    intro a b ha hb v hv
    simp [ha v hv, hb v hv]
  one_mem' := by
    intro v hv
    simp
  inv_mem' := by
    intro a ha v hv
    simp [ideleAt_inv, ha v hv]

/-- **The principal $S$-idèles** $P_F^S = J_F^S \cap P_F$ (O'Meara 1963, §33I, p. 80), with $P_F$ the principal idèles
(Mathlib's `IdeleGroup.principalSubgroup`). -/
@[kb "omeara1963" "§33I, p. 80 (P_F^S = J_F^S ∩ P_F)"]
def principalSIdeles (S : Set (HeightOneSpectrum (𝓞 F))) : Subgroup J :=
  sIdeles S ⊓ IdeleGroup.principalSubgroup (𝓞 F) F

/-- **The group $K_F^S$** (O'Meara 1963, §64, p. 172): the idèles $i$ with $\lvert i_\mathfrak p\rvert_\mathfrak p = 1$
for $\mathfrak p \in S$ and $i_\mathfrak p = 1$ for $\mathfrak p \in \Omega - S$ (finite spots outside $S$ and all
infinite spots). -/
@[kb "omeara1963" "§64, p. 172 (the group K_F^S)"]
def kIdeles (S : Set (HeightOneSpectrum (𝓞 F))) : Subgroup J where
  carrier := {i | (∀ v ∈ S, Valued.v (ideleAt i v) = 1) ∧ (∀ v ∉ S, ideleAt i v = 1) ∧
    ∀ w : InfinitePlace F, ideleAtInf i w = 1}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · simp [ha1 v hv, hb1 v hv]
    · simp [ha2 v hv, hb2 v hv]
    · simp [ha3 w, hb3 w]
  one_mem' := by
    exact ⟨fun v hv => by simp, fun v hv => by simp, fun w => by simp⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · simp [ideleAt_inv, ha1 v hv]
    · simp [ideleAt_inv, ha2 v hv]
    · simp [ideleAtInf_inv, ha3 w]

/-- **$K^S$ is a subgroup of $J^S$** (O'Meara 1963, §64, p. 172). -/
@[kb "omeara1963" "§64, p. 172 (K_F^S is a subgroup of J_F^S)"]
theorem kIdeles_le_sIdeles (S : Set (HeightOneSpectrum (𝓞 F))) : kIdeles S ≤ sIdeles S :=
  fun _ h => h.1

/-- **The group $I_\mathfrak p$** (O'Meara 1963, §64, p. 172) of idèles supported at the finite spot $\mathfrak p$:
the image of $\dot F_\mathfrak p$ under $\alpha \mapsto$ the idèle with $\mathfrak p$-coordinate $\alpha$ and all other
coordinates $1$ (Mathlib's `IdeleGroup.ofAdicCompletion`). -/
@[kb "omeara1963" "§64, p. 172 (the group I_𝔭 of idèles supported at 𝔭)"]
def ideleSupportedAt (v : HeightOneSpectrum (𝓞 F)) : Subgroup J :=
  (IdeleGroup.ofAdicCompletion (𝓞 F) F v).range

/-- **O'Meara's definition of $I_\mathfrak p$** (O'Meara 1963, §64, p. 172): an idèle lies in $I_\mathfrak p$ if and
only if $i_\mathfrak q = 1$ for every spot $\mathfrak q \ne \mathfrak p$. -/
@[kb "omeara1963" "§64, p. 172 (I_𝔭 = {i : i_𝔮 = 1 for all 𝔮 ≠ 𝔭})"]
theorem mem_ideleSupportedAt_iff (v : HeightOneSpectrum (𝓞 F)) (i : J) :
    i ∈ ideleSupportedAt v ↔ (∀ v' ≠ v, ideleAt i v' = 1) ∧ ∀ w : InfinitePlace F, ideleAtInf i w = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun v' h => ideleAt_ofAdic_ne v v' h x, fun w => ideleAtInf_ofAdic v w x⟩
  · rintro ⟨h1, h2⟩
    let u : (v.adicCompletion F)ˣ :=
      ⟨ideleAt i v, ideleAt i⁻¹ v, by rw [← ideleAt_mul]; simp, by rw [← ideleAt_mul]; simp⟩
    refine ⟨u, ?_⟩
    apply Units.ext
    apply Prod.ext
    · funext w
      exact (ideleAtInf_ofAdic v w u).trans (h2 w).symm
    · apply RestrictedProduct.ext
      intro v'
      by_cases h : v' = v
      · subst h
        exact ideleAt_ofAdic_self v' u
      · exact (ideleAt_ofAdic_ne v v' h u).trans (h1 v' h).symm

theorem ideleAt_ofAdic_injective (v : HeightOneSpectrum (𝓞 F)) :
    Function.Injective (IdeleGroup.ofAdicCompletion (𝓞 F) F v) := by
  intro x y h
  apply Units.ext
  have := congrArg (fun i => ideleAt i v) h
  simpa [ideleAt_ofAdic_self] using this

/-- **The natural isomorphism $\dot F_\mathfrak p \to I_\mathfrak p$** (O'Meara 1963, §64, p. 172). -/
@[kb "omeara1963" "§64, p. 172 (the natural isomorphism F_𝔭 → I_𝔭)"]
def ideleSupportedAtEquiv (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ ≃* ideleSupportedAt v :=
  MonoidHom.ofInjective (ideleAt_ofAdic_injective v)

theorem ideleAt_ideleSupportedAtEquiv (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    ideleAt (ideleSupportedAtEquiv v x : J) v = x :=
  ideleAt_ofAdic_self v x

/-- **$I_\mathfrak p$ is a subgroup of $J^S$ if and only if $\mathfrak p \notin S$** (O'Meara 1963, §64, p. 172). -/
@[kb "omeara1963" "§64, p. 172 (I_𝔭 ⊆ J_F^S if and only if 𝔭 ∉ S)"]
theorem ideleSupportedAt_le_sIdeles_iff (S : Set (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    ideleSupportedAt v ≤ sIdeles S ↔ v ∉ S := by
  constructor
  · intro h hv
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have hπ0 : (π : v.adicCompletion F) ≠ 0 := by
      intro h0
      have : Valued.v (π : v.adicCompletion F) = 0 := by rw [h0]; exact map_zero _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ] at this
      exact WithZero.exp_ne_zero this
    have hmem : IdeleGroup.ofAdicCompletion (𝓞 F) F v (Units.mk0 _ hπ0) ∈ ideleSupportedAt v := ⟨_, rfl⟩
    have := h hmem v hv
    rw [ideleAt_ofAdic_self] at this
    simp only [Units.val_mk0] at this
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ] at this
    have h1 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp 0 := by
      rw [this]; simp
    have := WithZero.exp_injective h1
    omega
  · intro hv
    rintro _ ⟨x, rfl⟩ v' hv'
    have : v' ≠ v := fun h => hv (h ▸ hv')
    rw [ideleAt_ofAdic_ne v v' this]
    simp

end QuadFormsKB.OMeara
