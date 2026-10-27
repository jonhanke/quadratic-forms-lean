/-
# The local orbital identity for an imprimitive base vector

**Layer:** the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ at a finite prime (every residue characteristic, dyadic included), the
split space $V = F_\mathfrak p e_0\perp(F_\mathfrak p^n, Q')$ with $Q = \langle m\rangle\perp Q'$, the standard lattice $L = \mathfrak o_\mathfrak p^{n+1}$ and
$K = O(L)$ (`stdStab`), with the near counts and orbit machinery of `OrbitCount.lean` and `LocalOrbitalBad.lean`.

The primitive case proves Weil's local orbital identity for the lattice
$L = \mathfrak o_\mathfrak p e_0\perp\mathfrak o_\mathfrak p^n$ and the **primitive** split vector $e_0$.
In the orbital Euler product the vector is $\xi = \varpi^je_0$ ($j = \mathrm{ord}_\mathfrak p\mathfrak b$), and the local types are the $K$-orbits on
$\{x \in L : Q(x) = \varpi^{2j}m\}$: vectors $\varpi^iy$ with $y$ primitive of norm $\varpi^{2(j-i)}m$ for every $0 \le i \le j$ (Hanke's
*Zero* type $\varpi\mid x$, and the *Good*/*Bad* types of the primitive part; Hanke 2004, Def. 3.1, §3). We do not classify them:
Weil's argument only needs that **orbit volume times stabilizer volume is constant** on the level set.

**Proves**
* `nearCount_mul_relIndex_eq_gen` (**the within-lattice transfer, any base vector**): for two solutions $y_0$, $x$ of $Q = t$ in
  $L$ and an involution $\sigma$ of $V$ with $\sigma y_0 = x$,
  $N_{k,r}(Kx)\,[J : J \cap \mathrm{Stab}_K(x)] = N_{k,r}(Ky_0)\,[J : J\cap\mathrm{Stab}_K(y_0)]$, $J = K\cap\sigma K\sigma$.
* `sigmaPtG`, `relIndex_stabOf_smul_e₀`, `relIndex_stabOf_xG`: for $y_0 = c\,e_0$ the two indices are $[K_0' : K_0'\cap K_{\sigma L}]$ and
  $[K_{\sigma L} : K_0'\cap K_{\sigma L}]$, so $N(Kx) = w(\sigma L)\,N(Kc\,e_0)$.
* `localTypeOrbitCountG`: $W_\mathfrak p(L, c)\cdot N_{k,r}(K\,c\,e_0) = \#\{x \bmod \varpi^k : Q(x) \equiv c^2m\}$ for $k \gg 0$.
* `nearCount_smul`: $N_{k,r}(\varpi^jA, \varpi^{2j}t) = q^{j(n+1)}N_{k-2j,r-j}(A, t)$ (the Zero-type scaling).
* **`localIdentity_imprimitive`**: $W_\mathfrak p(L, \varpi^j)\,\alpha_\mathfrak p(L)\,|2m|^n = \alpha_\mathfrak p(L')\,q^{j(n-1)}\,\beta_\mathfrak p(L, \varpi^{2j}m)$.

Sources: Weil 1982, §3.4 [unverified]; Kitaoka 1993, §5.6 [unverified]; Hanke 2004, Def. 3.1 and §3 [unverified].
Indices are 0-based ($e_0$ is the first basis vector).
-/
import QuadFormsKB.Tamagawa.GeneralFactor

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices LocalDensity QuadForm

/-! ### The within-lattice transfer, for any base vector -/

section Transfer

variable {F : Type*} [Field F] [NumberField F] {N : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F N)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The within-lattice transfer** (Weil 1982, §3.4 [unverified]: orbit measure times stabilizer measure is constant on the
level set). For an integral model $Q_o$ of $Q$ (nondegenerate), two solutions $y_0, x \in \mathfrak o_\mathfrak p^N$ of $Q_o = t \ne 0$, and an
involution $\sigma$ of $V$ with $\sigma y_0 = x$ and $\varpi^c\sigma$ integral, with $J = K\cap\sigma K\sigma$ (`Jsub`), for
$r \ge f + 1 + 2c$ ($\pi^f\,\Vert\,4t$), $k \ge r + c + e$, $k \ge 2e+1$ ($\pi^e\,\Vert\,2t$):
$$N_{k,r}(Kx)\cdot[J : J\cap\mathrm{Stab}_K(x)] = N_{k,r}(Ky_0)\cdot[J : J\cap\mathrm{Stab}_K(y_0)].$$
*Proof:* `nearCount_mul_relIndex` at $y_0$ and at $x$, and `nearCount_eq_of_involution` for $Jy_0$ and
$Jx = \sigma Jy_0\sigma$. -/
@[kb "weil1982" "§3.4 (orbit measures, any base vector) [unverified]"]
theorem nearCount_mul_relIndex_eq_gen {Qo : QuadForm 𝔬 N} (hQo : IsIntModel v Q Qo) (hQnd : Qo.Nondegenerate)
    {t : 𝔬} (ht : t ≠ 0) (y₀ x : Fin N → 𝔬) (hy₀ : Qo.eval y₀ = t) (hx : Qo.eval x = t)
    (σ : orthGroup Q Fv) (hσ : σ * σ = 1)
    (hσx : (σ : GL (Fin N) Fv).val *ᵥ (fun i => (y₀ i : Fv)) = fun i => (x i : Fv))
    {c : ℕ} {σ' : Matrix (Fin N) (Fin N) 𝔬}
    (hσ' : σ'.map (algebraMap 𝔬 Fv) = ((NF.π v : 𝔬) : Fv) ^ c • (σ : GL (Fin N) Fv).val)
    {e f r k : ℕ} (he : NF.π v ^ e ∣ 2 * t) (he' : ¬ NF.π v ^ (e + 1) ∣ 2 * t)
    (hf : NF.π v ^ f ∣ 4 * t) (hf' : ¬ NF.π v ^ (f + 1) ∣ 4 * t)
    (hr : f + 1 + 2 * c ≤ r) (hk : r + c + e ≤ k) (hk2 : 2 * e + 1 ≤ k) :
    nearCount Qo (NF.π v) t k r (orbitOf (intRep v Q) ⊤ x) * (Jsub v Q σ).relIndex (stabOf (intRep v Q) x) =
      nearCount Qo (NF.π v) t k r (orbitOf (intRep v Q) ⊤ y₀) *
        (Jsub v Q σ).relIndex (stabOf (intRep v Q) y₀) := by
  set ρ := intRep v Q
  set J := Jsub v Q σ
  set ϖ : Fv := ((NF.π v : 𝔬) : Fv)
  have hπ := NF.irreducible_π v
  have hρQ : ∀ κ, Qo.compMat (ρ κ) = Qo := compMat_intRep v hQo
  have hQρ : ∀ κ y, Qo.eval (ρ κ *ᵥ y) = Qo.eval y := fun κ y => by rw [← eval_compMat, hρQ]
  set Sv := (σ : GL (Fin N) Fv).val
  have hSS : Sv * Sv = 1 := by
    have := congrArg (fun g : orthGroup Q Fv => (g : GL (Fin N) Fv).val) hσ
    simpa [Sv] using this
  have hσxe : Sv *ᵥ (fun i => (x i : Fv)) = fun i => (y₀ i : Fv) := by
    rw [← hσx, mulVec_mulVec, hSS, one_mulVec]
  have hopen : ∀ y : Fin N → 𝔬, Qo.eval y = t → ∀ κ ∈ congrSub ρ (NF.π v) r y,
      ∃ γ ∈ J, ρ γ *ᵥ y = ρ κ *ᵥ y := by
    intro y hy κ hκ
    exact exists_Jsub_of_near v Q σ hσ hσ' hQo hQnd ht hf hf' hr hy (by rw [hQρ, hy]) hκ
  have hJe := nearCount_mul_relIndex ρ Qo hρQ (NF.π v) t (k := k) (r := r) (by omega) hπ J y₀ (hopen y₀ hy₀)
  have hJx := nearCount_mul_relIndex ρ Qo hρQ (NF.π v) t (k := k) (r := r) (by omega) hπ J x (hopen x hx)
  have hcoe : ∀ z : Fin N → 𝔬, (fun i => ((σ' *ᵥ z) i : Fv)) = ϖ ^ c • (Sv *ᵥ fun i => (z i : Fv)) := by
    intro z; rw [coe_mulVec_o, hσ', smul_mulVec]
  have hσσ : ∀ z, σ' *ᵥ (σ' *ᵥ z) = (NF.π v ^ c) ^ 2 • z := by
    intro z
    apply coe_o_injective v
    show (fun i => ((σ' *ᵥ (σ' *ᵥ z)) i : Fv)) = fun i => ((((NF.π v ^ c) ^ 2 • z) i : 𝔬) : Fv)
    rw [hcoe, hcoe, mulVec_smul, mulVec_mulVec, hSS, one_mulVec, smul_smul]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, ϖ]
    push_cast
    ring
  have hσQ : ∀ z, Qo.eval (σ' *ᵥ z) = (NF.π v ^ c) ^ 2 * Qo.eval z := by
    intro z
    apply SetLike.coe_eq_coe.mp
    rw [← hQo, hcoe, evalIn_smul', evalIn_mulVec_of_mem Q σ.2, hQo]
    simp [ϖ]
  have hconjJ : ∀ γ ∈ J, ∃ γ' ∈ J, (γ' : orthGroup Q Fv) = σ * (γ : orthGroup Q Fv) * σ := by
    intro γ hγ
    refine ⟨⟨σ * γ * σ, (mem_Jsub_iff v Q σ hσ γ).mp hγ⟩, (mem_Jsub_iff v Q σ hσ _).mpr ?_, rfl⟩
    show σ * (σ * (γ : orthGroup Q Fv) * σ) * σ ∈ stdStab Q v
    have : σ * (σ * (γ : orthGroup Q Fv) * σ) * σ = γ := by
      calc σ * (σ * (γ : orthGroup Q Fv) * σ) * σ = (σ * σ) * γ * (σ * σ) := by group
        _ = γ := by rw [hσ]; group
    rw [this]; exact γ.2
  have hval : ∀ γ' γ : stdStab Q v, (γ' : orthGroup Q Fv) = σ * (γ : orthGroup Q Fv) * σ →
      ((γ' : orthGroup Q Fv) : GL (Fin N) Fv).val = Sv * ((γ : orthGroup Q Fv) : GL (Fin N) Fv).val * Sv := by
    intro γ' γ h; rw [h]; simp [Sv]
  have hAA' : ∀ (y y' : Fin N → 𝔬), Sv *ᵥ (fun i => (y i : Fv)) = (fun i => (y' i : Fv)) →
      ∀ a ∈ orbitOf ρ J y, ∃ a' ∈ orbitOf ρ J y', σ' *ᵥ a = NF.π v ^ c • a' := by
    intro y y' hyy' a ⟨γ, hγ, ha⟩
    obtain ⟨γ', hγ', hγ'v⟩ := hconjJ γ hγ
    refine ⟨ρ γ' *ᵥ y', ⟨γ', hγ', rfl⟩, ?_⟩
    apply coe_o_injective v
    show (fun i => ((σ' *ᵥ a) i : Fv)) = fun i => (((NF.π v ^ c • (ρ γ' *ᵥ y')) i : 𝔬) : Fv)
    rw [hcoe, ← ha, coe_intRep_mulVec]
    have h1 : (fun i => (((NF.π v ^ c • (ρ γ' *ᵥ y')) i : 𝔬) : Fv)) =
        ϖ ^ c • (fun i => ((ρ γ' *ᵥ y') i : Fv)) := by funext i; simp [ϖ]
    rw [h1, coe_intRep_mulVec, hval γ' γ hγ'v, ← hyy', mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
      hSS, Matrix.mul_one]
  have hsat : ∀ y : Fin N → 𝔬, Qo.eval y = t → ∀ a ∈ orbitOf ρ J y, ∀ z, Qo.eval z = t →
      (∀ i, NF.π v ^ (f + 1 + 2 * c) ∣ z i - a i) → z ∈ orbitOf ρ J y := by
    intro y hy a ⟨γ, hγ, ha⟩ z hz hza
    obtain ⟨γ₁, hγ₁, h1⟩ := exists_Jsub_of_near v Q σ hσ hσ' hQo hQnd ht hf hf' le_rfl
      (by rw [← ha, hQρ, hy]) hz hza
    refine ⟨γ₁ * γ, J.mul_mem hγ₁ hγ, ?_⟩
    rw [map_mul, ← mulVec_mulVec, ha, h1]
  have hσl := nearCount_eq_of_involution hπ Qo he he' σ' c hσσ hσQ (hAA' _ _ hσx) (hAA' _ _ hσxe)
    (hsat _ hy₀) (hsat _ hx) hr hk hk2
  have e1 : (nearCount Qo (NF.π v) t k r (orbitOf ρ ⊤ x) * J.relIndex (stabOf ρ x) : ℕ) =
      J.index * nearCount Qo (NF.π v) t k r (orbitOf ρ J x) := hJx
  rw [e1, ← hσl, ← hJe]

end Transfer

/-! ### Identifying the indices for the base vector $c\,e_0$ -/

section StabG

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)
  (σ : orthGroup (splitForm m Q') (v.adicCompletion F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QS" => splitForm m Q'

/-- **The lattice $\sigma L$** as an element of $Y_\mathfrak p(L, c)$, when $\sigma(c\,e_0) \in L$ and $\sigma^2 = 1$. -/
def sigmaPtG (c : Fv) (hσ : σ * σ = 1)
    (hx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ (c • (e₀ : Fin (n + 1) → Fv)) ∈ std v) :
    LocCompSetG v m Q' (std v) c :=
  ⟨locAct v (σ : GL (Fin (n + 1)) Fv) (std v), ⟨σ, rfl⟩, by
    refine ⟨_, hx, ?_⟩
    show (σ : GL (Fin (n + 1)) Fv).val *ᵥ ((σ : GL (Fin (n + 1)) Fv).val *ᵥ (c • e₀)) = c • e₀
    rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, hσ]
    simp⟩

theorem mem_stabilizer_sigmaPtG {c : Fv} (hσ : σ * σ = 1)
    (hx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ (c • (e₀ : Fin (n + 1) → Fv)) ∈ std v) (h : orthGroup Q' Fv) :
    σ * orthEmb m Q' Fv h * σ ∈ stdStab QS v ↔ h ∈ stabilizer (orthGroup Q' Fv) (sigmaPtG v m Q' σ c hσ hx) := by
  rw [conj_mem_stdStab_iff v m Q' σ hσ, mem_stabilizer_iff]
  constructor
  · intro h1; exact Subtype.ext h1
  · intro h1; exact congrArg Subtype.val h1

/-- $\mathrm{Stab}_K(c\,e_0) = \mathrm{Stab}_K(e_0)$ for $c \ne 0$. -/
theorem stabOf_smul_e₀ {N : ℕ} {c : 𝔬} (hc : c ≠ 0) (ρ : stdStab QS v →* Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬) :
    stabOf ρ (c • (e₀ : Fin (n + 1) → 𝔬)) = stabOf ρ e₀ := by
  ext κ
  show ρ κ *ᵥ (c • e₀) = c • e₀ ↔ ρ κ *ᵥ e₀ = e₀
  rw [mulVec_smul]
  exact smul_right_injective _ hc |>.eq_iff

theorem coe_smul_o (c : 𝔬) (y : Fin (n + 1) → 𝔬) :
    (fun i => (((c • y) i : 𝔬) : Fv)) = (c : Fv) • fun i => (y i : Fv) := by
  funext i; simp

/-- **The stabilizer of $c\,e_0$ against $J$**: $[J : J\cap\mathrm{Stab}_K(c\,e_0)] = [K_0' : K_0'\cap K_{\sigma L}]$ ($c \ne 0$). -/
theorem relIndex_stabOf_smul_e₀ (hm : m ≠ 0) (hσ : σ * σ = 1) {c : 𝔬} (hc : c ≠ 0)
    (hx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) ∈ std v) :
    (Jsub v QS σ).relIndex (stabOf (intRep v QS) (c • (e₀ : Fin (n + 1) → 𝔬))) =
      (stabilizer (orthGroup Q' Fv) (sigmaPtG v m Q' σ (c : Fv) hσ hx)).relIndex (stdStab Q' v) := by
  rw [stabOf_smul_e₀ v m Q' (N := n + 1) hc]
  have hm2 : algebraMap F Fv (2 * m) ≠ 0 := by
    rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm
  set S₀ := stabOf (intRep v QS) (e₀ : Fin (n + 1) → 𝔬)
  set sub := (stdStab QS v).subtype
  set φ := orthEmb m Q' Fv
  have hsub : Function.Injective sub := Subtype.val_injective
  have hφ : Function.Injective φ := orthEmb_injective m Q' Fv
  have hS₀ : ∀ κ : stdStab QS v, κ ∈ S₀ ↔
      ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
    intro κ
    show intRep v QS κ *ᵥ e₀ = e₀ ↔ _
    rw [← coe_intRep_e₀]
    constructor
    · intro h; rw [h, coe_e₀_o]
    · intro h
      apply coe_o_injective v
      show (fun i => ((intRep v QS κ *ᵥ (e₀ : Fin (n + 1) → 𝔬)) i : Fv)) =
        fun i => (((e₀ : Fin (n + 1) → 𝔬) i : 𝔬) : Fv)
      rw [h, coe_e₀_o]
  have hA : S₀.map sub = (stdStab Q' v).map φ := by
    ext g
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨κ, hκ, rfl⟩
      obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 κ ((hS₀ κ).mp hκ)
      refine ⟨h, (mem_stdStab_orthEmb_iff m Q' v h).mp (by rw [hh]; exact κ.2), hh⟩
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨φ h, (mem_stdStab_orthEmb_iff m Q' v h).mpr hh⟩, (hS₀ _).mpr (orthEmb_mulVec_e₀ m Q' Fv h), rfl⟩
  have hB : (Jsub v QS σ ⊓ S₀).map sub =
      (stabilizer (orthGroup Q' Fv) (sigmaPtG v m Q' σ (c : Fv) hσ hx) ⊓ stdStab Q' v).map φ := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨κ, ⟨hJ, hκ⟩, rfl⟩
      obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 κ ((hS₀ κ).mp hκ)
      refine ⟨h, ⟨(mem_stabilizer_sigmaPtG v m Q' σ hσ hx h).mp ?_,
        (mem_stdStab_orthEmb_iff m Q' v h).mp (by rw [hh]; exact κ.2)⟩, hh⟩
      rw [mem_Jsub_iff v QS σ hσ] at hJ
      rwa [show φ h = (κ : orthGroup QS Fv) from hh]
    · rintro ⟨h, ⟨hst, hh⟩, rfl⟩
      refine ⟨⟨φ h, (mem_stdStab_orthEmb_iff m Q' v h).mpr hh⟩,
        ⟨(mem_Jsub_iff v QS σ hσ _).mpr ((mem_stabilizer_sigmaPtG v m Q' σ hσ hx h).mpr hst),
          (hS₀ _).mpr (orthEmb_mulVec_e₀ m Q' Fv h)⟩, rfl⟩
  rw [← Subgroup.inf_relIndex_right, ← Subgroup.relIndex_map_map_of_injective _ _ hsub, hA, hB,
    Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.inf_relIndex_right]

/-- **The stabilizer of $x = \sigma(c\,e_0)$ against $J$**: $[J : J\cap\mathrm{Stab}_K(x)] = [K_{\sigma L} : K_0'\cap K_{\sigma L}]$. -/
theorem relIndex_stabOf_xG (hm : m ≠ 0) (hσ : σ * σ = 1) {c : 𝔬} (hc : c ≠ 0) (x : Fin (n + 1) → 𝔬)
    (hσx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) = fun i => (x i : Fv))
    (hx : (σ : GL (Fin (n + 1)) Fv).val *ᵥ ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) ∈ std v) :
    (Jsub v QS σ).relIndex (stabOf (intRep v QS) x) =
      (stdStab Q' v).relIndex (stabilizer (orthGroup Q' Fv) (sigmaPtG v m Q' σ (c : Fv) hσ hx)) := by
  have hm2 : algebraMap F Fv (2 * m) ≠ 0 := by
    rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm
  have hc' : (c : Fv) ≠ 0 := by
    intro h0; exact hc (Subtype.ext h0)
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  set Sx := stabOf (intRep v QS) x
  set sub := (stdStab QS v).subtype
  set φ := orthEmb m Q' Fv
  set cσ := (MulAut.conj σ).toMonoidHom
  have hsub : Function.Injective sub := Subtype.val_injective
  have hφ : Function.Injective φ := orthEmb_injective m Q' Fv
  have hcinj : Function.Injective cσ := (MulAut.conj σ).injective
  have hcv : ∀ g, cσ g = σ * g * σ := fun g => by
    show σ * g * σ⁻¹ = _; rw [hσi]
  set Sv := (σ : GL (Fin (n + 1)) Fv).val
  have hSS : Sv * Sv = 1 := by
    have := congrArg (fun g : orthGroup QS Fv => (g : GL (Fin (n + 1)) Fv).val) hσ
    simpa [Sv] using this
  have hσxe : Sv *ᵥ (fun i => (x i : Fv)) = (c : Fv) • e₀ := by rw [← hσx, mulVec_mulVec, hSS, one_mulVec]
  have hSx : ∀ κ : stdStab QS v, κ ∈ Sx ↔
      ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (fun i => (x i : Fv)) = fun i => (x i : Fv) := by
    intro κ
    show intRep v QS κ *ᵥ x = x ↔ _
    rw [← coe_intRep_mulVec]
    constructor
    · intro h; rw [h]
    · intro h; exact coe_o_injective v h
  have key2 : ∀ h : orthGroup Q' Fv, σ * φ h * σ ∈ stdStab QS v ↔
      h ∈ stabilizer (orthGroup Q' Fv) (sigmaPtG v m Q' σ (c : Fv) hσ hx) :=
    mem_stabilizer_sigmaPtG v m Q' σ hσ hx
  have hfix : ∀ κ : stdStab QS v, κ ∈ Sx →
      ((σ * (κ : orthGroup QS Fv) * σ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ
        (e₀ : Fin (n + 1) → Fv) = e₀ := by
    intro κ hκ
    apply smul_right_injective _ hc'
    show (c : Fv) • (_ *ᵥ e₀) = (c : Fv) • e₀
    rw [← mulVec_smul]
    simp only [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    rw [show (σ : GL (Fin (n + 1)) Fv).val *ᵥ ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) = fun i => (x i : Fv) from hσx,
      (hSx κ).mp hκ]
    exact hσxe
  have hback : ∀ h : orthGroup Q' Fv, ((σ * φ h * σ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ
      (fun i => (x i : Fv)) = fun i => (x i : Fv) := by
    intro h
    simp only [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    rw [show (σ : GL (Fin (n + 1)) Fv).val *ᵥ (fun i => (x i : Fv)) = (c : Fv) • e₀ from hσxe,
      orthEmb_mulVec_smul_e₀, hσx]
  have hcc : ∀ h : orthGroup Q' Fv, σ * (σ * φ h * σ) * σ = φ h := by
    intro h
    calc σ * (σ * φ h * σ) * σ = (σ * σ) * φ h * (σ * σ) := by group
      _ = φ h := by rw [hσ]; group
  have hC : (Sx.map sub).map cσ = (stabilizer (orthGroup Q' Fv) (sigmaPtG v m Q' σ (c : Fv) hσ hx)).map φ := by
    ext g
    simp only [Subgroup.map_map, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨κ, hκ, rfl⟩
      obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 _ (hfix κ hκ)
      refine ⟨h, (key2 h).mp ?_, by rw [hh, hcv]; rfl⟩
      rw [hh]
      have : σ * (σ * (κ : orthGroup QS Fv) * σ) * σ = κ := by
        calc σ * (σ * (κ : orthGroup QS Fv) * σ) * σ = (σ * σ) * κ * (σ * σ) := by group
          _ = κ := by rw [hσ]; group
      rw [this]; exact κ.2
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨σ * φ h * σ, (key2 h).mpr hh⟩, (hSx _).mpr (hback h), ?_⟩
      show cσ (σ * φ h * σ) = φ h
      rw [hcv, hcc]
  have hD : ((Jsub v QS σ ⊓ Sx).map sub).map cσ =
      (stdStab Q' v ⊓ stabilizer (orthGroup Q' Fv) (sigmaPtG v m Q' σ (c : Fv) hσ hx)).map φ := by
    ext g
    simp only [Subgroup.map_map, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply, Subgroup.mem_inf]
    constructor
    · rintro ⟨κ, ⟨hJ, hκ⟩, rfl⟩
      obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 _ (hfix κ hκ)
      have hκ' : σ * (σ * (κ : orthGroup QS Fv) * σ) * σ = κ := by
        calc σ * (σ * (κ : orthGroup QS Fv) * σ) * σ = (σ * σ) * κ * (σ * σ) := by group
          _ = κ := by rw [hσ]; group
      refine ⟨h, ⟨?_, (key2 h).mp ?_⟩, by rw [hh, hcv]; rfl⟩
      · rw [mem_Jsub_iff v QS σ hσ] at hJ
        rw [← mem_stdStab_orthEmb_iff m Q' v h, hh]; exact hJ
      · rw [hh, hκ']; exact κ.2
    · rintro ⟨h, ⟨hK, hh⟩, rfl⟩
      refine ⟨⟨σ * φ h * σ, (key2 h).mpr hh⟩, ⟨?_, (hSx _).mpr (hback h)⟩, ?_⟩
      · rw [mem_Jsub_iff v QS σ hσ]
        show σ * (σ * φ h * σ) * σ ∈ stdStab QS v
        rw [hcc]; exact (mem_stdStab_orthEmb_iff m Q' v h).mpr hK
      · show cσ (σ * φ h * σ) = φ h
        rw [hcv, hcc]
  rw [← Subgroup.inf_relIndex_right, ← Subgroup.relIndex_map_map_of_injective _ _ hsub,
    ← Subgroup.relIndex_map_map_of_injective _ _ hcinj, hC, hD, Subgroup.relIndex_map_map_of_injective _ _ hφ,
    Subgroup.inf_relIndex_right]

end StabG

/-! ### Local types for the base vector $c\,e_0$ and the $K$-orbits on $\{Q = c^2m\}$ -/

section TypesG

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QS" => splitForm m Q'

theorem evalIn_smul_inv {c : Fv} (hc : c ≠ 0) (z : Fin (n + 1) → Fv) {t : Fv} (hz : (QS).evalIn Fv z = c ^ 2 * t) :
    (QS).evalIn Fv (c⁻¹ • z) = t := by
  rw [evalIn_smul', hz]; field_simp

/-- **Data for a lattice of $Y_\mathfrak p(L, c)$**: for $M \in Y_\mathfrak p(L, c)$ there are $x \in \mathfrak o_\mathfrak p^{n+1}$ with $Q(x) = c^2m$, an
involution $\sigma$ with $\sigma(c\,e_0) = x$, and $h$ with $M = \mathrm{diag}(1,h)\,\sigma L$. -/
theorem exists_type_dataG (hm : m ≠ 0) {Qo : QuadForm 𝔬 (n + 1)} (hQo : IsIntModel v QS Qo) {mo : 𝔬}
    (hmoF : ((mo : 𝔬) : Fv) = algebraMap F Fv m) {c : 𝔬} (hc : c ≠ 0) (M : LocCompSetG v m Q' (std v) (c : Fv)) :
    ∃ (x : Fin (n + 1) → 𝔬) (σ : orthGroup QS Fv) (h : orthGroup Q' Fv), Qo.eval x = c ^ 2 * mo ∧ σ * σ = 1 ∧
      (σ : GL (Fin (n + 1)) Fv).val *ᵥ ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) = (fun i => (x i : Fv)) ∧
      locAct v ((orthEmb m Q' Fv h * σ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv) (std v) = M.1 := by
  have hm2 : algebraMap F Fv (2 * m) ≠ 0 := by
    rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm
  have hc' : (c : Fv) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  obtain ⟨g, hg⟩ := M.2.1
  have he := M.2.2
  rw [← hg] at he
  obtain ⟨y, hy, hgy⟩ := he
  replace hgy : (g : GL (Fin (n + 1)) Fv).val *ᵥ y = (c : Fv) • e₀ := hgy
  obtain ⟨x, rfl⟩ := integral_of_mem_std v hy
  have hQx : (QS).evalIn Fv (fun i => (x i : Fv)) = (c : Fv) ^ 2 * algebraMap F Fv m := by
    rw [← evalIn_mulVec_of_mem QS g.2, hgy, evalIn_smul', evalIn_splitForm_e₀]
  have hxmo : Qo.eval x = c ^ 2 * mo := by
    apply SetLike.coe_eq_coe.mp
    rw [← hQo, hQx, ← hmoF]; push_cast; ring
  obtain ⟨σ, hσ, hσx⟩ := exists_inv_e₀ v m Q' hm _ (evalIn_smul_inv v m Q' hc' _ hQx)
  have hσc : (σ : GL (Fin (n + 1)) Fv).val *ᵥ ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) = fun i => (x i : Fv) := by
    rw [mulVec_smul, hσx, smul_smul, mul_inv_cancel₀ hc', one_smul]
  have hgσ : ((g * σ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
    apply smul_right_injective _ hc'
    show (c : Fv) • (_ *ᵥ e₀) = (c : Fv) • e₀
    rw [← mulVec_smul]
    simp only [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hσc, hgy]
  obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 _ hgσ
  refine ⟨x, σ, h, hxmo, hσ, hσc, ?_⟩
  rw [hh, mul_assoc, hσ, mul_one, ← hg]

/-- **Points of one $K$-orbit give the same local type** (base vector $c\,e_0$). -/
theorem mem_orbit_of_stdStabG (hm : m ≠ 0) {c : Fv} (hc : c ≠ 0) (M M' : LocCompSetG v m Q' (std v) c)
    (g g' : orthGroup QS Fv)
    (hg : locAct v (g : GL (Fin (n + 1)) Fv) (std v) = M.1)
    (hg' : locAct v (g' : GL (Fin (n + 1)) Fv) (std v) = M'.1) (κ : stdStab QS v)
    (hκ : ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ ((g⁻¹ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ
      (c • (e₀ : Fin (n + 1) → Fv)) = ((g'⁻¹ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv).val *ᵥ (c • e₀)) :
    M' ∈ orbit (orthGroup Q' Fv) M := by
  have hm2 : algebraMap F Fv (2 * m) ≠ 0 := by
    rw [map_ne_zero]; exact mul_ne_zero two_ne_zero hm
  set γ : orthGroup QS Fv := g' * (κ : orthGroup QS Fv) * g⁻¹
  have hγc : (γ : GL (Fin (n + 1)) Fv).val *ᵥ (c • (e₀ : Fin (n + 1) → Fv)) = c • e₀ := by
    simp only [γ, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    rw [hκ, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    simp
  have hγ : (γ : GL (Fin (n + 1)) Fv).val *ᵥ (e₀ : Fin (n + 1) → Fv) = e₀ := by
    apply smul_right_injective _ hc
    show c • (_ *ᵥ e₀) = c • e₀
    rw [← mulVec_smul, hγc]
  obtain ⟨h, hh⟩ := exists_orthEmb_eq m Q' Fv hm2 γ hγ
  refine ⟨h, Subtype.ext ?_⟩
  rw [LocCompSetG.smul_val, hh, ← hg, ← hg', ← locAct_mul]
  have : ((γ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv) * (g : GL (Fin (n + 1)) Fv) =
      (g' : GL (Fin (n + 1)) Fv) * ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv) := by
    simp only [γ, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [this, locAct_mul, show locAct v ((κ : orthGroup QS Fv) : GL (Fin (n + 1)) Fv) (std v) = std v from κ.2]

theorem eval_splitForm_smul_e₀ {A : Type*} [CommRing A] (a : A) (Q₁ : QuadForm A n) (c : A) :
    (splitForm a Q₁).eval (c • (e₀ : Fin (n + 1) → A)) = c ^ 2 * a := by
  rw [eval_smul_gen, eval_splitForm_e₀']

end TypesG

/-! ### The orbit-count identity for the base vector $c\,e_0$ -/

section MainG

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QS" => splitForm m Q'

/-- **Weil's orbit-count identity for an imprimitive base vector** (Weil 1982, §3.4 [unverified]; every prime, dyadic included).
For $Q = \langle m\rangle\perp Q'$ with integral models $Q_o = \langle m_o\rangle\perp Q_o'$ (nondegenerate, $m_o \ne 0$), and $c \in \mathfrak o_\mathfrak p$, $c \ne 0$:
there is $r_0$ such that for every $r \ge r_0$ and all large $k$
$$W_\mathfrak p(L, c)\cdot N_{k,r}(K\,c\,e_0) = \#\{x \bmod \varpi^k : Q(x) \equiv c^2m\},\qquad L = \mathfrak o_\mathfrak p^{n+1}.$$
*Proof:* as for `localTypeOrbitCount_of_invariant`, with $c\,e_0$ for $e_0$: the $K$-orbits on $\{Q = c^2m\}$ are the
local types
(`exists_type_dataG`, `mem_orbit_of_stdStabG`), and the orbit of $x = \sigma(c\,e_0)$ has $w(\sigma L)$ times as many points as the
orbit of $c\,e_0$ (`nearCount_mul_relIndex_eq_gen`, `relIndex_stabOf_smul_e₀`, `relIndex_stabOf_xG`). -/
@[kb "weil1982" "§3.4 (orbits of the local fibration, imprimitive base vector) [unverified]"]
theorem localTypeOrbitCountG (hQ' : Q'.Nondegenerate) (hm : m ≠ 0) {Qo' : QuadForm 𝔬 n}
    (hQo' : IsIntModel v Q' Qo') {mo : 𝔬} (hmoF : ((mo : 𝔬) : Fv) = algebraMap F Fv m)
    (hQnd : (splitForm mo Qo').Nondegenerate) {c : 𝔬} (hc : c ≠ 0) :
    ∃ r₀ : ℕ, ∀ r, r₀ ≤ r → ∀ᶠ k in Filter.atTop,
      locTypeSumG v m Q' (std v) (c : Fv) *
          (nearCount (splitForm mo Qo') (NF.π v) (c ^ 2 * mo) k r
            (orbitOf (intRep v QS) ⊤ (c • (e₀ : Fin (n + 1) → 𝔬))) : ℝ) =
        (DVR.repCount (splitForm mo Qo') (NF.π v) k (c ^ 2 * mo) : ℝ) := by
  classical
  set Qo := splitForm mo Qo'
  have hQo : IsIntModel v QS Qo := isIntModel_splitForm v m Q' hQo' hmoF
  have hmo : mo ≠ 0 := by
    intro h0; apply hm
    have : algebraMap F Fv m = 0 := by rw [← hmoF, h0]; rfl
    exact (map_eq_zero_iff _ (algebraMap F Fv).injective).mp this
  have hc' : (c : Fv) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  set tv := c ^ 2 * mo with htv
  have ht : tv ≠ 0 := mul_ne_zero (pow_ne_zero _ hc) hmo
  have hy₀ : Qo.eval (c • (e₀ : Fin (n + 1) → 𝔬)) = tv := eval_splitForm_smul_e₀ mo Qo' c
  have hπ := NF.irreducible_π v
  have h2 : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  have h4 : (4 : 𝔬) ≠ 0 := by
    rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  obtain ⟨e, he, he'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h2 ht)
  obtain ⟨f, hf, hf'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h4 ht)
  set ρ := intRep v QS
  have hwinv : ∀ (h : orthGroup Q' Fv) (M : LocCompSetG v m Q' (std v) (c : Fv)),
      locWeightG v m Q' (h • M) = locWeightG v m Q' M :=
    fun h M => locWeightG_smul v m Q' hQ' (std_isLattice v) h M
  -- the data of the local types
  choose x σ h hx hσ hσx hloc using fun t : LocTypesG v m Q' (std v) (c : Fv) =>
    exists_type_dataG v m Q' hm hQo hmoF hc t.out
  set g : LocTypesG v m Q' (std v) (c : Fv) → orthGroup QS Fv := fun t => orthEmb m Q' Fv (h t) * σ t
  have hginv : ∀ t, ((g t)⁻¹ : orthGroup QS Fv).val.val *ᵥ ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) =
      fun i => (x t i : Fv) := by
    intro t
    have hσi : (σ t)⁻¹ = σ t := inv_eq_of_mul_eq_one_right (hσ t)
    simp only [g, _root_.mul_inv_rev, hσi, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, ← map_inv,
      orthEmb_mulVec_smul_e₀, hσx]
  have hce : (fun i => (((c • (e₀ : Fin (n + 1) → 𝔬)) i : 𝔬) : Fv)) = (c : Fv) • (e₀ : Fin (n + 1) → Fv) := by
    rw [coe_smul_o, coe_e₀_o]
  -- disjointness of the orbits
  have hdisj : ∀ (r : ℕ), f + 1 ≤ r → ∀ t t', ∀ a ∈ orbitOf ρ ⊤ (x t), ∀ a' ∈ orbitOf ρ ⊤ (x t'),
      (∀ i, NF.π v ^ r ∣ a i - a' i) → t = t' := by
    rintro r hr t t' a ⟨κ, -, ha⟩ a' ⟨κ', -, ha'⟩ haa'
    have hQa : Qo.eval a = tv := by rw [← ha, ← eval_compMat, compMat_intRep v hQo, hx t]
    have hQa' : Qo.eval a' = tv := by rw [← ha', ← eval_compMat, compMat_intRep v hQo, hx t']
    obtain ⟨T, hT, hTa, -⟩ := exists_openMat hπ Qo ht hf hf' (s := r) (by omega) hQa hQa'
      (fun i => by rw [← dvd_neg, neg_sub]; exact haa' i)
    obtain ⟨τ, hτ⟩ := exists_intRep_eq v hQo hQnd T hT
    have hκ₂ : ρ (κ'⁻¹ * τ * κ) *ᵥ x t = x t' := by
      rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, ha, hτ, hTa, ← ha', mulVec_inv_mulVec' ρ κ']
    have hmem := mem_orbit_of_stdStabG v m Q' hm hc' t.out t'.out (g t) (g t') (hloc t) (hloc t')
      (κ'⁻¹ * τ * κ) (by rw [hginv, hginv, ← coe_intRep_mulVec, hκ₂])
    have : (Quotient.mk'' t'.out : LocTypesG v m Q' (std v) (c : Fv)) = Quotient.mk'' t.out :=
      Quotient.sound' hmem
    rw [Quotient.out_eq', Quotient.out_eq'] at this
    exact this.symm
  -- finitely many types
  have hfinT : Finite (LocTypesG v m Q' (std v) (c : Fv)) := by
    have := DVR.finite_vec (ι := Fin (n + 1)) (NF.π v) hπ (f + 1)
    refine Finite.of_injective (fun t => DVR.redI (NF.π v) (f + 1) (x t)) fun t t' htt => ?_
    refine hdisj (f + 1) le_rfl t t' (x t) ⟨1, Subgroup.mem_top 1, by simp⟩ (x t') ⟨1, Subgroup.mem_top 1, by simp⟩
      ((DVR.redI_eq_iff _ _ _ _).mp htt)
  let _ : Fintype (LocTypesG v m Q' (std v) (c : Fv)) := Fintype.ofFinite _
  -- every solution lies in the orbit of some `x t`
  have hcover : ∀ y, Qo.eval y = tv → ∃ s, y ∈ orbitOf ρ ⊤ (x s) := by
    intro y hy
    have hQy : (QS).evalIn Fv (fun i => (y i : Fv)) = (c : Fv) ^ 2 * algebraMap F Fv m := by
      rw [hQo, hy, htv]; push_cast; rw [hmoF]
    obtain ⟨σy, hσy, hσye⟩ := exists_inv_e₀ v m Q' hm _ (evalIn_smul_inv v m Q' hc' _ hQy)
    have hσyc : (σy : GL (Fin (n + 1)) Fv).val *ᵥ ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) = fun i => (y i : Fv) := by
      rw [mulVec_smul, hσye, smul_smul, mul_inv_cancel₀ hc', one_smul]
    have hystd : (σy : GL (Fin (n + 1)) Fv).val *ᵥ ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) ∈ std v := by
      rw [hσyc]; exact coe_mem_std v y
    set M := sigmaPtG v m Q' σy (c : Fv) hσy hystd
    set s : LocTypesG v m Q' (std v) (c : Fv) := Quotient.mk'' M
    obtain ⟨h', hh'⟩ : s.out ∈ orbit (orthGroup Q' Fv) M := Quotient.exact' (Quotient.out_eq' s)
    set φ := orthEmb m Q' Fv
    set κo : orthGroup QS Fv := σy * (φ h')⁻¹ * g s
    have hσyσy : locAct v (σy : GL (Fin (n + 1)) Fv) (locAct v (σy : GL (Fin (n + 1)) Fv) (std v)) = std v :=
      locAct_sigma_sigma v m Q' σy hσy _
    have hκK : κo ∈ stdStab QS v := by
      show locAct v (κo : GL (Fin (n + 1)) Fv) (std v) = std v
      have h1 : locAct v ((g s : orthGroup _ _) : GL (Fin (n + 1)) Fv) (std v) =
          locAct v ((φ h' : orthGroup _ _) : GL (Fin (n + 1)) Fv)
            (locAct v (σy : GL (Fin (n + 1)) Fv) (std v)) := by
        rw [hloc s, ← hh']; rfl
      simp only [κo, Subgroup.coe_mul, Subgroup.coe_inv, locAct_mul]
      rw [h1, locAct_inv_locAct, hσyσy]
    refine ⟨s, ⟨⟨κo, hκK⟩, Subgroup.mem_top _, ?_⟩⟩
    apply coe_o_injective v
    show (fun i => ((ρ ⟨κo, hκK⟩ *ᵥ x s) i : Fv)) = fun i => (y i : Fv)
    rw [coe_intRep_mulVec]
    show (κo : GL (Fin (n + 1)) Fv).val *ᵥ _ = _
    have hgx : ((g s : orthGroup _ _) : GL (Fin (n + 1)) Fv).val *ᵥ
        (fun i => (x s i : Fv)) = (c : Fv) • e₀ := by
      rw [← hginv s, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; simp
    have hinvfix : (((φ h' : orthGroup _ _) : GL (Fin (n + 1)) Fv)⁻¹).val *ᵥ
        ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) = (c : Fv) • e₀ := by
      conv_lhs => rw [← orthEmb_mulVec_smul_e₀ v m Q' h' (c : Fv)]
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]; simp
    simp only [κo, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, ← mulVec_mulVec, hgx]
    rw [hinvfix, hσyc]
  -- denominators of the involutions and the radius
  choose cσ σ' hσ' using fun t => exists_scale_integral v ((σ t : GL (Fin (n + 1)) Fv).val)
  set cmax := Finset.univ.sup cσ
  have hct : ∀ t, cσ t ≤ cmax := fun t => Finset.le_sup (f := cσ) (Finset.mem_univ t)
  have hxstd : ∀ t, (σ t : GL (Fin (n + 1)) Fv).val *ᵥ ((c : Fv) • (e₀ : Fin (n + 1) → Fv)) ∈ std v :=
    fun t => by rw [hσx]; exact coe_mem_std v _
  have hw : ∀ t, locWeightG v m Q' t.out = locWeightG v m Q' (sigmaPtG v m Q' (σ t) (c : Fv) (hσ t) (hxstd t)) := by
    intro t
    have : h t • sigmaPtG v m Q' (σ t) (c : Fv) (hσ t) (hxstd t) = t.out := Subtype.ext (by
      rw [LocCompSetG.smul_val]
      show locAct v _ (locAct v _ (std v)) = _
      rw [← locAct_mul, ← Subgroup.coe_mul]; exact hloc t)
    rw [← this, hwinv]
  have hD : ∀ t, (stdStab Q' v).relIndex
      (stabilizer (orthGroup Q' Fv) (sigmaPtG v m Q' (σ t) (c : Fv) (hσ t) (hxstd t))) ≠ 0 := by
    intro t h0
    rw [← relIndex_stabOf_xG v m Q' (σ t) hm (hσ t) hc (x t) (hσx t) (hxstd t)] at h0
    refine index_Jsub_ne_zero v _ (σ t) (hσ t) (hσ' t) ?_
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_eq_zero_of_le_right le_top h0
  refine ⟨f + 1 + 2 * cmax, fun r hr => ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (r + cmax + 2 * e + 1)] with k hk
  have hper : ∀ s, (nearCount Qo (NF.π v) tv k r (orbitOf ρ ⊤ (x s)) : ℝ) =
      locWeightG v m Q' s.out * nearCount Qo (NF.π v) tv k r (orbitOf ρ ⊤ (c • (e₀ : Fin (n + 1) → 𝔬))) := by
    intro s
    have hσxs : (σ s : GL (Fin (n + 1)) Fv).val *ᵥ (fun i => (((c • (e₀ : Fin (n + 1) → 𝔬)) i : 𝔬) : Fv)) =
        fun i => (x s i : Fv) := by rw [hce]; exact hσx s
    have hid := nearCount_mul_relIndex_eq_gen v QS hQo hQnd ht _ (x s) hy₀ (hx s) (σ s) (hσ s) hσxs (hσ' s)
      he he' hf hf' (r := r) (k := k) (by have := hct s; omega) (by have := hct s; omega) (by omega)
    rw [relIndex_stabOf_xG v m Q' (σ s) hm (hσ s) hc (x s) (hσx s) (hxstd s),
      relIndex_stabOf_smul_e₀ v m Q' (σ s) hm (hσ s) hc (hxstd s)] at hid
    have hD' : ((stdStab Q' v).relIndex
        (stabilizer (orthGroup Q' Fv) (sigmaPtG v m Q' (σ s) (c : Fv) (hσ s) (hxstd s))) : ℝ) ≠ 0 := by
      exact_mod_cast hD s
    rw [hw s, locWeightG, div_mul_eq_mul_div, eq_div_iff hD']
    have := congrArg (Nat.cast : ℕ → ℝ) hid
    push_cast at this
    linarith
  have hsum := repCount_eq_sum_nearCount hπ Qo he he' (fun s => orbitOf ρ ⊤ (x s)) hcover
    (hdisj r (by omega)) (k := k) (by omega) (by omega)
  rw [locTypeSumG, finsum_eq_sum_of_fintype, Finset.sum_mul, hsum, Nat.cast_sum]
  exact Finset.sum_congr rfl fun s _ => (hper s).symm

end MainG

/-! ### The Zero-type scaling of near counts -/

section Scaling

open LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
  {N : ℕ}

theorem dvd_of_pow_add_dvd_pow_mul {π : R} (hπ : Irreducible π) {a b : ℕ} {x : R} (h : π ^ (a + b) ∣ π ^ a * x) :
    π ^ b ∣ x := by
  rw [pow_add] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).mp h

/-- The vectors mod $\pi^{k-j}$ with the conditions of $N_{k-2j,\,r-j}(A, t)$ imposed on a lift (an auxiliary count). -/
def midSet (Q : QuadForm R N) (π t : R) (k j r : ℕ) (A : Set (Fin N → R)) : Type _ :=
  {u : Fin N → R ⧸ Ideal.span {π ^ (k - j)} //
    π ^ (k - 2 * j) ∣ Q.eval (liftI π (k - j) u) - t ∧ ∃ a ∈ A, ∀ i, π ^ (r - j) ∣ liftI π (k - j) u i - a i}

/-- Multiplication by $\pi^j$ identifies the solutions mod $\pi^k$ near $\pi^jA$ (value $\pi^{2j}t$) with `midSet`. -/
theorem nearCount_smul_eq_mid (Q : QuadForm R N) {π : R} (hπ : Irreducible π) (t : R) (A : Set (Fin N → R))
    {j k r : ℕ} (hjr : j ≤ r) (hrk : r + j ≤ k) :
    nearCount Q π (π ^ (2 * j) * t) k r ((fun a => π ^ j • a) '' A) = Nat.card (midSet Q π t k j r A) := by
  classical
  have h2j : 2 * j ≤ k := by omega
  -- the map `u ↦ π^j lift(u) mod π^k`
  let f : midSet Q π t k j r A → {z : Fin N → R ⧸ Ideal.span {π ^ k} //
      π ^ k ∣ Q.eval (liftI π k z) - π ^ (2 * j) * t ∧
        ∃ a ∈ (fun a => π ^ j • a) '' A, ∀ i, π ^ r ∣ liftI π k z i - a i} := fun u =>
    ⟨redI π k (π ^ j • liftI π (k - j) u.1), by
      have hl := liftI_redI_dvd π k (π ^ j • liftI π (k - j) u.1)
      refine ⟨?_, ?_⟩
      · have h1 := eval_congr_of_dvd Q hl
        have h2 : π ^ k ∣ Q.eval (π ^ j • liftI π (k - j) u.1) - π ^ (2 * j) * t := by
          have hk' : π ^ k = π ^ (2 * j) * π ^ (k - 2 * j) := by rw [← pow_add]; congr 1; omega
          rw [eval_smul_gen, ← pow_mul, mul_comm j 2, ← mul_sub, hk']
          exact mul_dvd_mul_left _ u.2.1
        have := h1.add h2
        rwa [sub_add_sub_cancel] at this
      · obtain ⟨a, ha, hua⟩ := u.2.2
        refine (near_congr (le_trans (by omega) hrk) (fun i => (hl i)) _).mpr ⟨π ^ j • a, ⟨a, ha, rfl⟩, fun i => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub]
        have hr' : π ^ r = π ^ j * π ^ (r - j) := by rw [← pow_add]; congr 1; omega
        rw [hr']
        exact mul_dvd_mul_left _ (hua i)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u u' huu
      have h1 := (redI_eq_iff π k _ _).mp (congrArg Subtype.val huu)
      apply Subtype.ext
      rw [← redI_liftI π (k - j) u.1, ← redI_liftI π (k - j) u'.1, redI_eq_iff]
      intro i
      have := h1 i
      simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub] at this
      exact dvd_of_pow_add_dvd_pow_mul hπ (a := j) (by rw [show j + (k - j) = k by omega]; exact this)
    · rintro ⟨z, hz, a', ⟨a, ha, rfl⟩, hza⟩
      -- `π^j ∣ lift z`
      have hdiv : ∀ i, π ^ j ∣ liftI π k z i := by
        intro i
        have h1 := (pow_dvd_pow π hjr).trans (hza i)
        have h2 : π ^ j ∣ π ^ j * a i := dvd_mul_right _ _
        have := h1.add h2
        simp only [Pi.smul_apply, smul_eq_mul, sub_add_cancel] at this
        exact this
      choose w hw using hdiv
      have hzw : liftI π k z = π ^ j • w := funext fun i => by rw [hw i]; rfl
      set u := redI π (k - j) w
      have hlu := liftI_redI_dvd π (k - j) w
      have hu1 : π ^ (k - 2 * j) ∣ Q.eval (liftI π (k - j) u) - t := by
        have h1 : π ^ (k - 2 * j) ∣ Q.eval w - t := by
          rw [hzw, eval_smul_gen, ← pow_mul, mul_comm j 2, ← mul_sub] at hz
          exact dvd_of_pow_add_dvd_pow_mul hπ (a := 2 * j) (by rw [show 2 * j + (k - 2 * j) = k by omega]; exact hz)
        have h2 := eval_congr_of_dvd Q (fun i => (pow_dvd_pow π (show k - 2 * j ≤ k - j by omega)).trans (hlu i))
        have := h2.add h1
        rwa [sub_add_sub_cancel] at this
      have hu2 : ∃ a ∈ A, ∀ i, π ^ (r - j) ∣ liftI π (k - j) u i - a i := by
        refine ⟨a, ha, fun i => ?_⟩
        have h1 : π ^ (r - j) ∣ w i - a i := by
          have := hza i
          rw [hzw] at this
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub] at this
          exact dvd_of_pow_add_dvd_pow_mul hπ (a := j) (by rw [show j + (r - j) = r by omega]; exact this)
        have h2 := (pow_dvd_pow π (show r - j ≤ k - j by omega)).trans (hlu i)
        have := h2.add h1
        rwa [sub_add_sub_cancel] at this
      refine ⟨⟨u, hu1, hu2⟩, Subtype.ext ?_⟩
      show redI π k (π ^ j • liftI π (k - j) u) = z
      rw [← redI_liftI π k z, redI_eq_iff, hzw]
      intro i
      simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub]
      have hk' : π ^ k = π ^ j * π ^ (k - j) := by rw [← pow_add]; congr 1; omega
      rw [hk']
      exact mul_dvd_mul_left _ (hlu i)
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

/-- **The Zero-type scaling of near counts** (Hanke 2004, §3, the reduction for $\pi \mid x$ [unverified]): for $j \le r$, $r + j \le k$,
$$N_{k,r}(\pi^jA,\ \pi^{2j}t) = q^{jN}\,N_{k-2j,\,r-j}(A,\ t).$$
*Proof:* $z \equiv \pi^ja \bmod \pi^r$ forces $z = \pi^jw$, $w$ determined mod $\pi^{k-j}$ (`nearCount_smul_eq_mid`); the conditions on $w$
only depend on $w \bmod \pi^{k-2j}$, and each class mod $\pi^{k-2j}$ has $q^{jN}$ lifts mod $\pi^{k-j}$ (`card_preimage_eq`). -/
@[kb "hanke2004" "§3 (Zero type reduction) [unverified]"]
theorem nearCount_smul_pow (Q : QuadForm R N) {π : R} (hπ : Irreducible π) (t : R) (A : Set (Fin N → R))
    {j k r : ℕ} (hjr : j ≤ r) (hrk : r + j ≤ k) :
    nearCount Q π (π ^ (2 * j) * t) k r ((fun a => π ^ j • a) '' A) =
      q R ^ (j * N) * nearCount Q π t (k - 2 * j) (r - j) A := by
  classical
  rw [nearCount_smul_eq_mid Q hπ t A hjr hrk]
  have hle : Ideal.span {π ^ (k - j)} ≤ Ideal.span {π ^ (k - 2 * j)} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (by omega))
  let ψ₁ : R ⧸ Ideal.span {π ^ (k - j)} →+* R ⧸ Ideal.span {π ^ (k - 2 * j)} := Ideal.Quotient.factor hle
  let ψ : (Fin N → R ⧸ Ideal.span {π ^ (k - j)}) →+ (Fin N → R ⧸ Ideal.span {π ^ (k - 2 * j)}) :=
    (Pi.ringHom fun i => ψ₁.comp (Pi.evalRingHom _ i)).toAddMonoidHom
  have hψ : ∀ u, ψ u = redI π (k - 2 * j) (liftI π (k - j) u) := by
    intro u
    funext i
    show ψ₁ (u i) = Ideal.Quotient.mk _ (liftI π (k - j) u i)
    conv_lhs => rw [← redI_liftI π (k - j) u]
    rfl
  have hsurj : Function.Surjective ψ := by
    intro w
    refine ⟨redI π (k - j) (liftI π (k - 2 * j) w), ?_⟩
    rw [hψ, ← redI_liftI π (k - 2 * j) w, redI_eq_iff]
    intro i
    rw [redI_liftI]
    have := liftI_redI_dvd π (k - j) (liftI π (k - 2 * j) w) i
    exact (pow_dvd_pow π (by omega)).trans this
  set T : Set (Fin N → R ⧸ Ideal.span {π ^ (k - 2 * j)}) := {w | π ^ (k - 2 * j) ∣ Q.eval (liftI π (k - 2 * j) w) - t ∧
    ∃ a ∈ A, ∀ i, π ^ (r - j) ∣ liftI π (k - 2 * j) w i - a i}
  have hfinG := finite_vec (ι := Fin N) π hπ (k - j)
  have hpre : Nat.card (midSet Q π t k j r A) = Nat.card (ψ ⁻¹' T) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
    show _ ↔ ψ u ∈ T
    rw [hψ]
    have hcong := liftI_redI_dvd π (k - 2 * j) (liftI π (k - j) u)
    show _ ↔ (π ^ (k - 2 * j) ∣ Q.eval (liftI π (k - 2 * j) (redI π (k - 2 * j) (liftI π (k - j) u))) - t ∧ _)
    have he := eval_congr_of_dvd Q hcong
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by have := he.add h1; rwa [sub_add_sub_cancel] at this,
        (near_congr (show r - j ≤ k - 2 * j by omega) hcong A).mpr h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by have := (dvd_neg.mpr he).add h1; rwa [neg_sub, sub_add_sub_cancel] at this,
        (near_congr (show r - j ≤ k - 2 * j by omega) hcong A).mp h2⟩
  have hT : Nat.card (ψ ⁻¹' T) = Nat.card ψ.ker * Nat.card T :=
    card_preimage_eq ψ T fun w _ => hsurj w
  have hU : Nat.card (ψ ⁻¹' Set.univ) = Nat.card ψ.ker * Nat.card (Set.univ : Set (Fin N → R ⧸ Ideal.span {π ^ (k - 2 * j)})) :=
    card_preimage_eq ψ Set.univ fun w _ => hsurj w
  rw [Set.preimage_univ, Nat.card_univ, Nat.card_univ, Nat.card_pi, Nat.card_pi] at hU
  simp only [card_quot_pow π hπ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hU
  have hcardT : Nat.card T = nearCount Q π t (k - 2 * j) (r - j) A := rfl
  have hqpos : 0 < q R ^ ((k - 2 * j) * N) := pow_pos (q_pos (R := R)) _
  have hker : Nat.card ψ.ker = q R ^ (j * N) := by
    have e : (q R ^ (k - j)) ^ N = q R ^ (j * N) * q R ^ ((k - 2 * j) * N) := by
      rw [← pow_mul, ← pow_add]; congr 1
      rw [show k - j = j + (k - 2 * j) by omega, add_mul]
    rw [e, ← pow_mul] at hU
    exact (Nat.eq_of_mul_eq_mul_right hqpos hU).symm
  rw [hpre, hT, hker, hcardT]

/-- The orbit of $c\,y$ is $c$ times the orbit of $y$. -/
theorem orbitOf_smul {𝒦 : Type*} [Group 𝒦] (ρ : 𝒦 →* Matrix (Fin N) (Fin N) R) (H : Subgroup 𝒦) (c : R)
    (y : Fin N → R) : orbitOf ρ H (c • y) = (fun a => c • a) '' orbitOf ρ H y := by
  ext z
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    exact ⟨ρ κ *ᵥ y, ⟨κ, hκ, rfl⟩, (mulVec_smul _ _ _).symm⟩
  · rintro ⟨_, ⟨κ, hκ, rfl⟩, rfl⟩
    exact ⟨κ, hκ, mulVec_smul _ _ _⟩

end Scaling

/-! ### The local orbital identity for the base vector $\varpi^je_0$ -/

section Identity

open LocalDensity.DVR

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **Weil's local orbital identity for the imprimitive vector $\varpi^je_0$** (Weil 1982, §3.4 [unverified]; Hanke 2004, §3: the
Zero-type recursion [unverified]). Let $Q = \langle m\rangle\perp Q'$ with $Q' = Q_0'\otimes F$ ($Q_0'$ nondegenerate over $\mathcal O_F$,
$n \ge 1$ variables), $m \in F^\times$ with $m = m_o \in \mathfrak o_\mathfrak p$, $\varpi^e\,\Vert\,2m_o$, $L = \mathfrak o_\mathfrak p e_0\perp\mathfrak o_\mathfrak p^n$ and
$Q_o = \langle m_o\rangle\perp Q_0'$ over $\mathfrak o_\mathfrak p$. For every $j \ge 0$:
$$W_\mathfrak p(L, \varpi^j)\cdot\alpha_\mathfrak p(Q_o) = q^{en}\,\alpha_\mathfrak p(Q_0')\,q^{j(n-1)}\,\beta_\mathfrak p(Q_o, \varpi^{2j}m_o),$$
$W_\mathfrak p(L,\varpi^j)$ = `locTypeSumG` (the local types of the pairs (lattice, $\varpi^je_0$)), $\alpha_\mathfrak p$ = `localDensityForm`,
$\beta_\mathfrak p$ = `localDensity`. For $j = 0$ this is the identity. *Proof:* `localTypeOrbitCountG` with
$c = \varpi^j$, the scaling
$N(\varpi^jKe_0) = q^{j(n+1)}N(Ke_0)$ (`nearCount_smul_pow`), the $N(Ke_0) = |O(Q\bmod\varpi^K)e_0|$
(`card_orbitSet_eq_nearCount`)
and the fibration count $A_{\varpi^K}(L,L) = |O(Q\bmod\varpi^K)e_0|\,q^{en}A_{\varpi^K}(L',L')$
(`repCountForm_splitForm_orbit`). -/
@[kb "weil1982" "§3.4 (local fibration, imprimitive vector) [unverified]"]
theorem localIdentity_imprimitive (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) (hn : 1 ≤ n) {m : F}
    (hm : m ≠ 0) {mo : 𝔬} (hmoF : ((mo : 𝔬) : Fv) = algebraMap F Fv m) (j : ℕ) {e : ℕ}
    (he : NF.π v ^ e ∣ 2 * mo) (he' : ¬ NF.π v ^ (e + 1) ∣ 2 * mo) :
    locTypeSumG v m (Q₀'.map (algebraMap (𝓞 F) F)) (std v) (((NF.π v ^ j : 𝔬) : Fv)) *
        localDensityForm (splitForm mo (NF.Qp v Q₀')) (splitForm mo (NF.Qp v Q₀')) (NF.π v) =
      (q 𝔬 : ℝ) ^ (e * n) * localDensityForm (NF.Qp v Q₀') (NF.Qp v Q₀') (NF.π v) * (q 𝔬 : ℝ) ^ (j * (n - 1)) *
        localDensity (splitForm mo (NF.Qp v Q₀')) (NF.π v) (NF.π v ^ (2 * j) * mo) := by
  classical
  set QF' := Q₀'.map (algebraMap (𝓞 F) F)
  set Qo' := NF.Qp v Q₀'
  set Qo := splitForm mo Qo'
  have hπ := NF.irreducible_π v
  have hQo' : IsIntModel v QF' Qo' := fun y => evalIn_coe_o v Q₀' y
  have hmo : mo ≠ 0 := by
    intro h0; apply hm
    have : algebraMap F Fv m = 0 := by rw [← hmoF, h0]; rfl
    exact (map_eq_zero_iff _ (algebraMap F Fv).injective).mp this
  have hQnd : Qo.Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]
    exact mul_ne_zero (mul_ne_zero (NF.two_ne_zero' v) hmo) (NF.nondegenerate_Qp v hQ')
  have hQF' : QF'.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ'
  have hc : (NF.π v ^ j : 𝔬) ≠ 0 := pow_ne_zero _ hπ.ne_zero
  obtain ⟨r₀, hr₀⟩ := localTypeOrbitCountG v m QF' hQF' hm hQo' hmoF hQnd hc
  have h2 : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  have h4 : (4 : 𝔬) ≠ 0 := by
    rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  obtain ⟨f, hf, hf'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h4 hmo)
  obtain ⟨d, hd, hd'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hQnd
  set r := max r₀ (j + f + 1)
  set ρ := intRep v (splitForm m QF')
  have hρQ : ∀ κ, Qo.compMat (ρ κ) = Qo :=
    compMat_intRep v (isIntModel_splitForm v m QF' hQo' hmoF)
  have hsurj : ∀ X, Qo.compMat X = Qo → ∃ κ, ρ κ = X :=
    fun X hX => exists_intRep_eq v (isIntModel_splitForm v m QF' hQo' hmoF) hQnd X hX
  have e1 := localDensityForm_eventually_eq Qo' Qo' (NF.nondegenerate_Qp v hQ') (NF.π v) hπ le_rfl
  have e2 := localDensityForm_eventually_eq Qo Qo hQnd (NF.π v) hπ le_rfl
  have e3 := localDensity_eventually_eq Qo hQnd (NF.π v) hπ (NF.π v ^ (2 * j) * mo)
    (mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hmo) h2
  have hsub := Filter.tendsto_sub_atTop_nat (2 * j)
  obtain ⟨k, hk⟩ := ((hr₀ r (le_max_left _ _)).and (e3.and ((hsub.eventually e1).and ((hsub.eventually e2).and
    (Filter.eventually_ge_atTop (r + j + 2 * e + 2 * d + 2 * f + 1)))))).exists
  obtain ⟨hcount, h3, h1, h2', hk0⟩ := hk
  set K := k - 2 * j
  have hK : k = K + 2 * j := by omega
  -- the orbit of `π^j e₀`
  have hval : (NF.π v ^ j) ^ 2 * mo = NF.π v ^ (2 * j) * mo := by rw [← pow_mul, mul_comm j 2]
  rw [hval, orbitOf_smul, nearCount_smul_pow Qo hπ mo _ (by omega) (by omega)] at hcount
  have horb := card_orbitSet_eq_nearCount (n := n) hπ ρ (m := mo) Qo' hρQ hsurj hf hf' hd hd'
    (r := r - j) (k := K) (by omega) (by omega) (by omega)
  have hfib := repCountForm_splitForm_orbit (k := K) hπ he he' Qo' hd hd' (by omega) (by omega)
  rw [← horb] at hcount
  set O := Nat.card (orbitSet (Qo.map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ K}))) e₀)
  set W := locTypeSumG v m QF' (std v) (((NF.π v ^ j : 𝔬) : Fv))
  set a : ℝ := (q 𝔬 : ℝ)
  have ha : 0 < a := Nat.cast_pos.mpr (q_pos (R := 𝔬))
  -- the exponents
  have hE : (n + 1) * (n + 1) - (n + 1) * (n + 1 + 1) / 2 = (n * n - n * (n + 1) / 2) + n := by
    rw [self_exp, self_exp, Tamagawa.nat_tri_succ]
  set E' := n * n - n * (n + 1) / 2
  rw [← h1, ← h2', ← h3]
  push_cast at hcount hfib
  have hcount' : W * (a ^ (j * (n + 1)) * O) = (LocalDensity.DVR.repCount Qo (NF.π v) k (NF.π v ^ (2 * j) * mo) : ℝ) := by
    rw [← hcount]
  rw [show n + 1 - 1 = n by omega, hE, hfib, ← hcount']
  have hjn : j * (n - 1) + j * (n + 1) = 2 * j * n := by
    rcases n with _ | n'
    · omega
    · simp only [Nat.add_sub_cancel]; ring
  have hpow : a ^ (k * n) = a ^ (K * n) * (a ^ (j * (n - 1)) * a ^ (j * (n + 1))) := by
    rw [← pow_add, ← pow_add, hjn, hK]; ring_nf
  rw [hpow, show K * (E' + n) = K * E' + K * n by ring, pow_add]
  have h1' : a ^ (K * E') ≠ 0 := (pow_pos ha _).ne'
  have h2'' : a ^ (K * n) ≠ 0 := (pow_pos ha _).ne'
  have h3' : a ^ (j * (n - 1)) ≠ 0 := (pow_pos ha _).ne'
  have h4' : a ^ (j * (n + 1)) ≠ 0 := (pow_pos ha _).ne'
  push_cast
  rw [show (q 𝔬 : ℝ) = a from rfl]
  field_simp

end Identity

end QuadFormsKB.Tamagawa
