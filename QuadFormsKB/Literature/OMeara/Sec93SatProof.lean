/-
# O'Meara 93:21: existence of saturated Jordan splittings (proof)

**Setting** (as in `Sec93Sat.lean`): $R$ a Henselian discrete valuation ring with finite residue field and fraction
field $F$ of characteristic $0$ satisfying the Hilbert-symbol axioms `PadicClass.LocalHilbertField` (as in
`Sec93D18Five.lean`), $2$ not a unit of $R$ (O'Meara's dyadic local field), $(V, Q)$ a quadratic space over $F$,
lattices `Submodule R V`. Indices are $0$-based.

**Proves** (O'Meara 1963, §93E, 93:21, p. 265)
* `exists_jordan_replace`: replacing a piece $A$ of a component $L_i = A \perp B$ by a modular lattice $A'$ with
  $L = A' \perp C'$, $C' \cong B \perp \bigperp_{j \ne i} L_j$, gives a new Jordan splitting;
* `exists_hyp_split`: a $\xi\mathfrak o$-modular lattice of rank $\ge 5$ splits off a plane $\xi A(0,0)$ (93:18 (v));
* step 1 of the proof (all $\dim L_i \ge 7$) and step 2 (all $\dim L_i \ge 3$, by hyperbolic adjunction and 93:14).
-/
import QuadFormsKB.Literature.OMeara.Sec93Sat
import QuadFormsKB.Literature.OMeara.Sec91Gap
import QuadFormsKB.Literature.OMeara.Sec93D20
import QuadFormsKB.Literature.OMeara.Sec93D19
import QuadFormsKB.Literature.OMeara.Sec93Gap2
import QuadFormsKB.Literature.OMeara.Sec93EFund
import QuadFormsKB.Literature.OMeara.Sec93DNF

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Sat93

section Replace

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- The sum $\sum_{j \ne i} L_j$ of the components other than the $i$-th. -/
def others {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) : Submodule R V :=
  ⨆ j : {j : Fin t // j ≠ i}, Ls j

theorem le_others {t : ℕ} (Ls : Fin t → Submodule R V) {i j : Fin t} (h : j ≠ i) : Ls j ≤ others Ls i :=
  le_iSup (fun j : {j : Fin t // j ≠ i} => Ls j) ⟨j, h⟩

theorem others_le {t : ℕ} {Ls : Fin t → Submodule R V} {i : Fin t} {M : Submodule R V}
    (h : ∀ j, j ≠ i → Ls j ≤ M) : others Ls i ≤ M :=
  iSup_le fun j => h j.1 j.2

/-- $L = L_i \oplus \sum_{j \ne i} L_j$ for an orthogonal splitting. -/
theorem sup_others {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V} (h : IsOrthSplit Q L Ls)
    (i : Fin t) : Ls i ⊔ others Ls i = L := by
  rw [← h.iSup_eq]
  apply le_antisymm
  · exact sup_le (le_iSup Ls i) (others_le fun j _ => le_iSup Ls j)
  · refine iSup_le fun j => ?_
    by_cases hj : j = i
    · subst hj; exact le_sup_left
    · exact (le_others Ls hj).trans le_sup_right

/-- Vectors of $L_i$ are orthogonal to $\sum_{j \ne i} L_j$. -/
theorem orth_others {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V} (h : IsOrthSplit Q L Ls)
    (i : Fin t) {x : V} (hx : x ∈ Ls i) : ∀ y ∈ others Ls i, bil Q x y = 0 := by
  intro y hy
  refine Submodule.iSup_induction (fun j : {j : Fin t // j ≠ i} => Ls j) (motive := fun y => bil Q x y = 0) hy
    (fun j y hy => h.orth i j.1 (Ne.symm j.2) x hx y hy) (by simp [bil]) (fun y z hy hz => ?_)
  rw [bil_add_right, hy, hz, add_zero]

/-- **Replacing part of a Jordan component.** Let $L = L_1 \perp \cdots \perp L_t$ be a Jordan splitting,
$L_i = A \perp B$ with $B$ modular of scale $\mathfrak sL_i$, and suppose $L = A' \perp C'$ with $A'$ modular of scale
$\mathfrak sL_i$ and $f : B \perp \sum_{j \ne i} L_j \to C'$ an isometry. Then
$L = K_1 \perp \cdots \perp K_t$ with $K_i = A' \perp f(B)$ and $K_j = f(L_j)$ for $j \ne i$ is a Jordan splitting. -/
theorem exists_jordan_replace {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) {A B A' C' : Submodule R V}
    (hAB : IsOrthSum Q (Ls i) A B) (hBmod : IsModular Q (scale Q (Ls i)) B)
    (hA'mod : IsModular Q (scale Q (Ls i)) A') (hA' : IsOrthSum Q L A' C') {C : Submodule R V}
    (hC : B ⊔ others Ls i = C) (f : C ≃ₗ[R] C') (hf : ∀ x, Q (f x : V) = Q (x : V)) :
    IsJordanSplitting Q L (Function.update (fun j => imgLat f (Ls j)) i (A' ⊔ imgLat f B)) := by
  set Ks := Function.update (fun j => imgLat f (Ls j)) i (A' ⊔ imgLat f B) with hKs
  have hBi : B ≤ Ls i := hAB.sup_eq ▸ le_sup_right
  have hBC : B ≤ C := hC ▸ le_sup_left
  have hjC : ∀ j, j ≠ i → Ls j ≤ C := fun j hj => (le_others Ls hj).trans (hC ▸ le_sup_right)
  have hA'L : A' ≤ L := hA'.sup_eq ▸ le_sup_left
  have hC'L : C' ≤ L := hA'.sup_eq ▸ le_sup_right
  have hKi : Ks i = A' ⊔ imgLat f B := by simp [hKs]
  have hKj : ∀ j, j ≠ i → Ks j = imgLat f (Ls j) := fun j hj => by simp [hKs, Function.update_of_ne hj]
  have hbil := bil_eq_of_isometricLat Q Q f hf
  have hCfg : C.FG := FG.of_le hfg (hC ▸ sup_le (hBi.trans (hL.split.iSup_eq ▸ le_iSup Ls i))
    (others_le fun j _ => hL.split.iSup_eq ▸ le_iSup Ls j))
  have hC'fg : C'.FG := FG.of_le hfg hC'L
  -- orthogonality of the images
  have himg_orth : ∀ {J J' : Submodule R V}, J ≤ C → J' ≤ C → (∀ x ∈ J, ∀ y ∈ J', bil Q x y = 0) →
      ∀ x ∈ imgLat f J, ∀ y ∈ imgLat f J', bil Q x y = 0 := by
    intro J J' _ _ h x hx y hy
    obtain ⟨a, ha, rfl⟩ := (mem_imgLat f).mp hx
    obtain ⟨b, hb, rfl⟩ := (mem_imgLat f).mp hy
    rw [hbil]; exact h _ ha _ hb
  have hBj : ∀ j, j ≠ i → ∀ x ∈ B, ∀ y ∈ Ls j, bil Q x y = 0 := fun j hj x hx y hy =>
    hL.split.orth i j (Ne.symm hj) x (hBi hx) y hy
  have hA'img : ∀ (J : Submodule R V), ∀ x ∈ A', ∀ y ∈ imgLat f J, bil Q x y = 0 := fun J x hx y hy =>
    hA'.orth x hx y (imgLat_le f J hy)
  -- `K_i` against `K_j`
  have horth_i : ∀ j, j ≠ i → ∀ x ∈ A' ⊔ imgLat f B, ∀ y ∈ imgLat f (Ls j), bil Q x y = 0 := by
    intro j hj x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hx
    rw [bil_add_left, hA'img _ a ha y hy, himg_orth hBC (hjC j hj) (hBj j hj) b hb y hy, add_zero]
  have horth : ∀ j k, j ≠ k → ∀ x ∈ Ks j, ∀ y ∈ Ks k, bil Q x y = 0 := by
    intro j k hjk x hx y hy
    by_cases hj : j = i
    · subst hj
      rw [hKi] at hx; rw [hKj k (Ne.symm hjk)] at hy
      exact horth_i k (Ne.symm hjk) x hx y hy
    · rw [hKj j hj] at hx
      by_cases hk : k = i
      · subst hk
        rw [hKi] at hy
        rw [bil_comm]; exact horth_i j hj y hy x hx
      · rw [hKj k hk] at hy
        exact himg_orth (hjC j hj) (hjC k hk) (hL.split.orth j k hjk) x hx y hy
  -- modularity and scales
  have hBfg : B.FG := FG.of_le hCfg hBC
  have hA'fg : A'.FG := FG.of_le hfg hA'L
  have himgB : IsModular Q (scale Q (Ls i)) (imgLat f B) := (isModular_imgLat Q Q f hf hBC _).mpr hBmod
  have hmodi : IsModular Q (scale Q (Ls i)) (A' ⊔ imgLat f B) :=
    (isModular_sup Q hA'mod himgB hA'fg (FG.of_le hC'fg (imgLat_le f B)) (hA'img B)).1
  have hsc : ∀ j, scale Q (Ks j) = scale Q (Ls j) := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hKi]; exact hmodi.2.1
    · rw [hKj j hj]; exact scale_imgLat Q Q f hf (hjC j hj)
  have hmod : ∀ j, IsModular Q (scale Q (Ks j)) (Ks j) := by
    intro j
    rw [hsc j]
    by_cases hj : j = i
    · subst hj; rw [hKi]; exact hmodi
    · rw [hKj j hj]; exact (isModular_imgLat Q Q f hf (hjC j hj) _).mpr (hL.modular j)
  have hKL : ∀ j, Ks j ≤ L := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hKi]; exact sup_le hA'L ((imgLat_le f B).trans hC'L)
    · rw [hKj j hj]; exact (imgLat_le f _).trans hC'L
  refine ⟨⟨horth, iSupIndep_of_orth Q horth fun j => (hmod j).isRegular Q (FG.of_le hfg (hKL j)), ?_⟩, hmod, ?_⟩
  · apply le_antisymm (iSup_le hKL)
    rw [← hA'.sup_eq]
    refine sup_le (le_trans (le_sup_left : A' ≤ A' ⊔ imgLat f B) (hKi ▸ le_iSup Ks i)) ?_
    intro y hy
    have hy' : y ∈ imgLat f C := by rw [imgLat_top]; exact hy
    obtain ⟨c, -, rfl⟩ := (mem_imgLat f).mp hy'
    -- `c = b + o` with `b ∈ B`, `o ∈ ∑_{j ≠ i} L_j`
    have key : ∀ v ∈ C, ∃ hv : v ∈ C, (f ⟨v, hv⟩ : V) ∈ ⨆ j, Ks j := by
      intro v hv
      obtain ⟨b, hb, o, ho, rfl⟩ := mem_sup.mp (hC ▸ hv)
      have hoC : o ∈ C := hC ▸ (le_sup_right (a := B) ho)
      have hb' : (f ⟨b, hBC hb⟩ : V) ∈ ⨆ j, Ks j :=
        (le_sup_right : imgLat f B ≤ A' ⊔ imgLat f B).trans (hKi ▸ le_iSup Ks i)
          ((mem_imgLat f).mpr ⟨⟨b, hBC hb⟩, hb, rfl⟩)
      have ho' : ∃ hv : o ∈ C, (f ⟨o, hv⟩ : V) ∈ ⨆ j, Ks j := by
        refine Submodule.iSup_induction (fun j : {j : Fin t // j ≠ i} => Ls j)
          (motive := fun o => ∃ hv : o ∈ C, (f ⟨o, hv⟩ : V) ∈ ⨆ j, Ks j) ho ?_ ?_ ?_
        · intro j x hx
          refine ⟨hjC j.1 j.2 hx, ?_⟩
          have : (f ⟨x, hjC j.1 j.2 hx⟩ : V) ∈ Ks j.1 := by
            rw [hKj j.1 j.2]; exact (mem_imgLat f).mpr ⟨_, hx, rfl⟩
          exact le_iSup Ks j.1 this
        · refine ⟨zero_mem _, ?_⟩
          have : (⟨0, zero_mem C⟩ : C) = 0 := rfl
          rw [this, map_zero, Submodule.coe_zero]; exact zero_mem _
        · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
          refine ⟨add_mem hx hy, ?_⟩
          have : (⟨x + y, add_mem hx hy⟩ : C) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
          rw [this, map_add, Submodule.coe_add]
          exact add_mem hx' hy'
      obtain ⟨hoC', ho''⟩ := ho'
      refine ⟨hv, ?_⟩
      have : (⟨b + o, hv⟩ : C) = ⟨b, hBC hb⟩ + ⟨o, hoC'⟩ := rfl
      rw [this, map_add, Submodule.coe_add]
      exact add_mem hb' ho''
    obtain ⟨_, h⟩ := key c c.2
    exact h
  · have : (fun j => scale Q (Ks j)) = fun j => scale Q (Ls j) := funext hsc
    rw [this]; exact hL.scale_strictAnti

/-- $\sum_{j \ne i} L_j$ in the form used by `iSupIndep`. -/
theorem others_eq {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) :
    others Ls i = ⨆ (j) (_ : j ≠ i), Ls j :=
  iSup_subtype (f := fun j : {j : Fin t // j ≠ i} => Ls j.1)

/-- If $L_i = P \perp M$ in an orthogonal splitting of $L$, then $L = P \perp (M \perp \sum_{j \ne i} L_j)$. -/
theorem isOrthSum_others {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsOrthSplit Q L Ls)
    (i : Fin t) {P M : Submodule R V} (hPM : IsOrthSum Q (Ls i) P M) :
    IsOrthSum Q L P (M ⊔ others Ls i) := by
  have hPi : P ≤ Ls i := hPM.sup_eq ▸ le_sup_left
  have hMi : M ≤ Ls i := hPM.sup_eq ▸ le_sup_right
  have hdis : Disjoint (Ls i) (others Ls i) := by rw [others_eq]; exact hL.indep i
  refine ⟨fun x hx y hy => ?_, ?_, ?_⟩
  · obtain ⟨m, hm, o, ho, rfl⟩ := mem_sup.mp hy
    rw [bil_add_right, hPM.orth x hx m hm, orth_others Q hL i (hPi hx) o ho, add_zero]
  · rw [disjoint_def]
    intro v hvP hv
    obtain ⟨m, hm, o, ho, rfl⟩ := mem_sup.mp hv
    have hoi : o ∈ Ls i := by
      have : o = (m + o) - m := by abel
      rw [this]; exact sub_mem (hPi hvP) (hMi hm)
    have ho0 : o = 0 := (disjoint_def.mp hdis) o hoi ho
    subst ho0
    rw [add_zero] at hvP ⊢
    exact (disjoint_def.mp hPM.disjoint) m hvP hm
  · rw [← sup_assoc, hPM.sup_eq]; exact sup_others Q hL i

/-- $Q(\alpha x + \beta y) = 2\alpha\beta\xi$ for a hyperbolic pair $Q(x) = Q(y) = 0$, $B(x, y) = \xi$. -/
theorem Q_hyp_comb {x y : V} {ξ : F} (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = ξ) (α β : R) :
    Q (α • x + β • y) = 2 * (algebraMap R F (α * β) * ξ) := by
  rw [Q_add, ← algebraMap_smul F α x, ← algebraMap_smul F β y, QuadraticMap.map_smul, QuadraticMap.map_smul,
    bil_smul_left, bil_smul_right, hQx, hQy, hxy, map_mul]
  ring

/-- **The norm group of $C^{\mathfrak a}$** (step of O'Meara 93:21, p. 265): if $L = P \perp C$ with
$P = \mathfrak ox + \mathfrak oy \cong \xi A(0,0)$ and $\mathfrak a \subseteq \mathfrak s(C^{\mathfrak a})$, then
$\mathfrak g(L^{\mathfrak a}) \subseteq \mathfrak g(C^{\mathfrak a})$. -/
theorem normGroup_subA_le_compl {L C : Submodule R V} {x y : V} {ξ : F} (hs : IsOrthSum Q L (span R {x, y}) C)
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = ξ) {a : Submodule R F}
    (haC : a ≤ scale Q (subA Q a C)) :
    normGroup Q (subA Q a L) ≤ normGroup Q (subA Q a C) := by
  rintro _ ⟨w, ⟨hwL, hwB⟩, c, hc, rfl⟩
  have hwL' := hwL
  rw [← hs.sup_eq] at hwL
  obtain ⟨p, hp, u, hu, rfl⟩ := mem_sup.mp hwL
  obtain ⟨α, β, rfl⟩ := mem_span_pair.mp hp
  have hCL : C ≤ L := hs.sup_eq ▸ le_sup_right
  have hPL : span R {x, y} ≤ L := hs.sup_eq ▸ le_sup_left
  have hpu : bil Q (α • x + β • y) u = 0 := hs.orth _ hp u hu
  have huC : u ∈ subA Q a C := by
    refine ⟨hu, fun l hl => ?_⟩
    have h1 := hwB l (hCL hl)
    rw [bil_add_left, hs.orth _ hp l hl, zero_add] at h1
    exact h1
  -- `αξ = B(w, y) ∈ 𝔞`
  have hyL : y ∈ L := hPL (subset_span (by simp))
  have hαξ : algebraMap R F α * ξ ∈ a := by
    have h1 := hwB y hyL
    have hu0 : bil Q u y = 0 := by rw [bil_comm]; exact hs.orth y (subset_span (by simp)) u hu
    rw [bil_add_left, hu0, add_zero, bil_add_left, bil_rsmul_left, bil_rsmul_left, hxy, bil_self, hQy,
      mul_zero, add_zero] at h1
    exact h1
  have hcξ : c ∈ a := scale_subA_le Q _ L hc
  refine ⟨u, huC, algebraMap R F (α * β) * ξ + c, haC (add_mem ?_ hcξ), ?_⟩
  · have : algebraMap R F (α * β) * ξ = β • (algebraMap R F α * ξ) := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [this]; exact smul_mem _ _ hαξ
  · rw [Q_add, hpu, Q_hyp_comb Q hQx hQy hxy]; ring

end Replace

section Retarget

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Retargeting a hyperbolic plane in a Jordan component** (O'Meara 1963, 93:21, step 1, p. 265, by 93:13). Let
$L = L_1 \perp \cdots \perp L_t$ be a Jordan splitting with $\mathfrak sL_i = \xi\mathfrak o$ and
$L_i = P \perp M$, $P = \mathfrak ox + \mathfrak oy \cong \xi A(0,0)$, $M \ne 0$ being $\xi\mathfrak o$-modular. For
every $\gamma \in \mathfrak g_i = \mathfrak g(L^{\xi\mathfrak o})$ there is a Jordan splitting
$L = K_1 \perp \cdots \perp K_t$ with $K_j \cong L_j$ for $j \ne i$, $K_i = P' \perp M'$ with $M' \cong M$, and
$P' = \mathfrak ox' + \mathfrak oy'$ with $Q(x') = \gamma$, $B(x', y') = \xi$, $Q(y') = 0$. -/
theorem exists_retarget {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) {ξ : F} (hξ : ξ ≠ 0) (hsi : scale Q (Ls i) = R ∙ ξ)
    {x y : V} {M : Submodule R V} (hPM : IsOrthSum Q (Ls i) (span R {x, y}) M) (hQx : Q x = 0) (hQy : Q y = 0)
    (hxy : bil Q x y = ξ) (hMmod : IsModular Q (R ∙ ξ) M) {γ : F} (hγ : γ ∈ fundNormGroup Q L Ls i) :
    ∃ Ks : Fin t → Submodule R V, IsJordanSplitting Q L Ks ∧ (∀ j, j ≠ i → IsometricLat Q Q (Ls j) (Ks j)) ∧
      ∃ x' y' : V, ∃ M' : Submodule R V, Q x' = γ ∧ bil Q x' y' = ξ ∧ Q y' = 0 ∧
        IsOrthSum Q (Ks i) (span R {x', y'}) M' ∧ IsometricLat Q Q M M' := by
  have hs := isOrthSum_others Q hL.split i hPM
  set C := M ⊔ others Ls i with hC
  have hMC : M ≤ C := le_sup_left
  -- `ξ ∈ 𝔰(C^{ξ𝔬})`, since `M ⊆ C^{ξ𝔬}` has scale `ξ𝔬`
  have hMsub : M ≤ subA Q (R ∙ ξ) C := by
    intro m hm
    refine ⟨hMC hm, fun l hl => ?_⟩
    obtain ⟨m', hm', o, ho, rfl⟩ := mem_sup.mp hl
    have hMi : M ≤ Ls i := hPM.sup_eq ▸ le_sup_right
    rw [bil_add_right, orth_others Q hL.split i (hMi hm) o ho, add_zero, ← hMmod.2.1]
    exact bil_mem_scale Q hm hm'
  have hξC : ξ ∈ scale Q (subA Q (R ∙ ξ) C) :=
    scale_mono Q hMsub (hMmod.2.1 ▸ mem_span_singleton_self ξ)
  have hγ' : γ ∈ normGroup Q (subA Q (R ∙ ξ) C) := by
    refine normGroup_subA_le_compl Q hs hQx hQy hxy ((span_singleton_le_iff_mem _ _).mpr hξC) ?_
    have : fundNormGroup Q L Ls i = normGroup Q (subA Q (R ∙ ξ) L) := by
      rw [fundNormGroup, fundSub, hsi]
    exact this ▸ hγ
  obtain ⟨z, hz, c, hc, rfl⟩ := hγ'
  obtain ⟨x', y', α', hα', hQx', hx'y', hQy', hs', hiso⟩ :=
    exists_isOrthSum_matA Q hs hξ (α := 0) rfl (by rw [hQx, map_zero, mul_zero]) hxy hQy hz hc
  have hQx'' : Q x' = Q z + 2 * c := by
    rw [hQx', hα', map_zero, zero_add]; field_simp
  obtain ⟨f, hf⟩ := hiso
  have hMi : M ≤ Ls i := hPM.sup_eq ▸ le_sup_right
  have hBmod : IsModular Q (scale Q (Ls i)) M := hsi ▸ hMmod
  have hA'mod : IsModular Q (scale Q (Ls i)) (span R {x', y'}) := by
    rw [hsi]
    refine (D18.span_pair_isModular Q hξ (p := α') (q := 0) (e := 1) ?_ hQx' ?_ ?_).1
    · simp
    · rw [hQy', map_zero, mul_zero]
    · rw [hx'y', map_one, mul_one]
  have hJ := exists_jordan_replace Q hfg hL i hPM hBmod hA'mod hs' rfl f hf
  refine ⟨_, hJ, fun j hj => ?_, x', y', imgLat f M, hQx'', hx'y', hQy', ?_, ?_⟩
  · rw [Function.update_of_ne hj]
    exact isometricLat_imgLat Q Q f hf ((le_others Ls hj).trans le_sup_right)
  · rw [Function.update_self]
    refine ⟨fun a ha b hb => hs'.orth a ha b (imgLat_le f M hb), ?_, rfl⟩
    exact hs'.disjoint.mono_right (imgLat_le f M)
  · exact isometricLat_imgLat Q Q f hf hMC

end Retarget

section Step

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **A $\xi\mathfrak o$-modular lattice of rank $\ge 5$ splits off a plane $\xi A(0,0)$** (O'Meara 1963, 93:18 (v),
p. 261, applied to the unimodular lattice $L$ on the scaled space $V^{\xi^{-1}}$): $L = (\mathfrak ox + \mathfrak oy)
\perp K$ with $Q(x) = Q(y) = 0$, $B(x, y) = \xi$, and $K$ is $\xi\mathfrak o$-modular of rank $\operatorname{rank} L - 2$. -/
theorem exists_hyp_split (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {ξ : F} (hξ : ξ ≠ 0)
    {L : Submodule R V} (hfg : L.FG) (hL : IsModular Q (R ∙ ξ) L) (hrk : 5 ≤ finrank R L) :
    ∃ x y : V, ∃ K : Submodule R V, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = ξ ∧ IsOrthSum Q L (span R {x, y}) K ∧
      IsModular Q (R ∙ ξ) K ∧ finrank R K + 2 = finrank R L := by
  have hU := isUnimodular_smul_of_isModular Q hξ hfg hL
  obtain ⟨x, y, K, h1, h2, h3, hs⟩ := D18.omeara93_18_v_splitting (ξ⁻¹ • Q) hK h2p hfg hU hrk
  have hξ' : ξ⁻¹ ≠ 0 := inv_ne_zero hξ
  have hQ : ∀ v, Q v = ξ * (ξ⁻¹ • Q) v := fun v => by
    rw [smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hξ, one_mul]
  have hB : ∀ v w, bil Q v w = ξ * bil (ξ⁻¹ • Q) v w := fun v w => by
    rw [bil_smul_form, ← mul_assoc, mul_inv_cancel₀ hξ, one_mul]
  have hs' : IsOrthSum Q L (span R {x, y}) K :=
    ⟨fun a ha b hb => by rw [hB, hs.orth a ha b hb, mul_zero], hs.disjoint, hs.sup_eq⟩
  have hP : IsModular Q (R ∙ ξ) (span R {x, y}) ∧ finrank R (span R {x, y}) = 2 := by
    refine D18.span_pair_isModular Q hξ (p := 0) (q := 0) (e := 1) (by simp) ?_ ?_ ?_
    · rw [hQ, h1]; simp
    · rw [hQ, h2]; simp
    · rw [hB, h3]; simp
  have hrkL := isOrthSum_finrank Q hs' hfg
  have hKfg : K.FG := FG.of_le hfg (hs.sup_eq ▸ le_sup_right)
  have hK0 : K ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot, hP.2] at hrkL; omega
  -- `K` is unimodular for `ξ⁻¹Q`, hence `ξ𝔬`-modular for `Q`
  have hKU : IsUnimodular (ξ⁻¹ • Q) K := by
    have hPU : IsUnimodular (ξ⁻¹ • Q) (span R {x, y}) :=
      isUnimodular_smul_of_isModular Q hξ (FG.of_le hfg (hs.sup_eq ▸ le_sup_left)) hP.1
    exact u93_isUnimodular_of_orth (ξ⁻¹ • Q) hfg hU hPU hs hK0
  have hKmod : IsModular Q (R ∙ ξ) K := by
    have := FundAux.isModular_smul_form (ξ⁻¹ • Q) hξ hKU
    rwa [smul_smul, mul_inv_cancel₀ hξ, one_smul, mul_one] at this
  exact ⟨x, y, K, by rw [hQ, h1, mul_zero], by rw [hQ, h2, mul_zero], by rw [hB, h3, mul_one], hs', hKmod,
    by rw [hrkL, hP.2]; ring⟩

omit [CharZero F] [FiniteDimensional F V] in
/-- **The criterion of 93:21, step 1** (O'Meara 1963, p. 265): if a component $K_i$ of a Jordan splitting of $L$
contains a fundamental norm generator $a_i$ and a fundamental weight generator $b_i$ in its norm group, then
$\mathfrak gK_i = \mathfrak g_i$: indeed $\mathfrak g_i = a_i\mathfrak o^2 + b_i\mathfrak o$, and
$b_i\mathfrak o \subseteq \mathfrak gK_i$ "from the properties of the weight (§93A)" (if
$\operatorname{ord} a_i + \operatorname{ord} b_i$ is odd, by p. 254; if it is even, $b_i\mathfrak o =
2\mathfrak s_i$). -/
theorem normGroup_eq_fund_of_mem (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L)
    {t : ℕ} {Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ks) (i : Fin t) {a b : F}
    (ha : IsNormGenerator Q (fundSub Q L Ks i) a) (hb : IsWeightGenerator Q (fundSub Q L Ks i) b)
    (haK : a ∈ normGroup Q (Ks i)) (hbK : b ∈ normGroup Q (Ks i)) :
    normGroup Q (Ks i) = fundNormGroup Q L Ks i := by
  refine le_antisymm (normGroup_le_fundNormGroup Q hfg hL i) fun z hz => ?_
  have hz' : z ∈ (fundNormGroup Q L Ks i : Set F) := hz
  rw [fundNormGroup_eq_sq_add Q h2p hfg hreg hL i ha] at hz'
  obtain ⟨ε, w, hw, rfl⟩ := hz'
  refine add_mem ?_ ?_
  · rw [mul_comm]; exact mul_sq_mem_normGroup Q haK ⟨ε, rfl⟩
  have hw' : w ∈ R ∙ b := by rw [hb]; exact hw
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hreg' := isRegular_fundSub Q hfg hreg hL i
  have hne := fundSub_ne_bot Q hfg hL i
  have ha0 := ha.ne_zero Q hreg' hne
  have hb0 := weight_gen_ne_zero Q ha ha0 hb
  by_cases hev : Even (dord hπ a + dord hπ b)
  · have h2 := weight_gen_eq_of_even Q h2p hπ hreg' hne ha hb hev
    rw [h2, scale_fundSub Q hfg hL i] at hw'
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hw'
    rw [smul_eq_mul]; exact two_mul_mem_normGroup Q hc
  · have hodd : Odd (dord hπ b - dord hπ a) := by
      have : Odd (dord hπ a + dord hπ b) := Int.not_even_iff_odd.mp hev
      have h3 : dord hπ b - dord hπ a = (dord hπ a + dord hπ b) - 2 * dord hπ a := by ring
      rw [h3]; exact this.sub_even (even_two_mul _)
    have haKi : IsNormGenerator Q (Ks i) a := by
      refine ⟨haK, le_antisymm ?_ ?_⟩
      · exact (span_singleton_le_iff_mem _ _).mpr (normGroup_subset_normIdeal Q _ haK)
      · rw [ha.2]; exact normIdeal_mono Q (le_fundSub Q hfg hL i)
    exact mem_normGroup_of_odd Q h2p hπ haKi ha0 hbK hb0 hodd hw'

/-- A regular non-zero finitely generated lattice has a weight generator (from `weight_cases`). -/
theorem exists_weightGen (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L)
    (hne : L ≠ ⊥) : ∃ b : F, IsWeightGenerator Q L b := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨x, -, ha⟩ := exists_isNormGenerator_Q Q hfg
  have ha0 := ha.ne_zero Q hreg hne
  obtain ⟨m, -, hm, -, hcase⟩ := weight_cases Q h2p hπ ha ha0
  rcases hcase with h | ⟨h, -⟩
  · exact ⟨_, h.symm⟩
  · exact ⟨m, hm.symm.trans h.symm⟩

/-- Orthogonal sums reassociate: $X = A \perp Y$ and $Y = C \perp D$ give $X = C \perp (A \perp D)$. -/
theorem isOrthSum_rotate {X A Y C D : Submodule R V} (h1 : IsOrthSum Q X A Y) (h2 : IsOrthSum Q Y C D) :
    IsOrthSum Q X C (A ⊔ D) ∧ IsOrthSum Q (A ⊔ D) A D := by
  have hCY : C ≤ Y := h2.sup_eq ▸ le_sup_left
  have hDY : D ≤ Y := h2.sup_eq ▸ le_sup_right
  have hAD : IsOrthSum Q (A ⊔ D) A D := ⟨fun a ha d hd => h1.orth a ha d (hDY hd), h1.disjoint.mono_right hDY, rfl⟩
  refine ⟨⟨fun c hc v hv => ?_, ?_, ?_⟩, hAD⟩
  · obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup.mp hv
    rw [bil_add_right, bil_comm, h1.orth a ha c (hCY hc), h2.orth c hc d hd, zero_add]
  · rw [disjoint_def]
    intro v hvC hv
    obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup.mp hv
    have ha0 : a = 0 := by
      have : a = (a + d) - d := by abel
      have haY : a ∈ Y := by rw [this]; exact sub_mem (hCY hvC) (hDY hd)
      exact (disjoint_def.mp h1.disjoint) a ha haY
    subst ha0
    rw [zero_add] at hvC ⊢
    exact (disjoint_def.mp h2.disjoint) d hvC hd
  · rw [sup_comm A D, ← sup_assoc, h2.sup_eq, sup_comm, h1.sup_eq]

/-- **One step of 93:21, step 1** (O'Meara 1963, p. 265): if $\dim L_i \ge 7$, there is a Jordan splitting
$L = K_1 \perp \cdots \perp K_t$ with $\mathfrak gK_i = \mathfrak g_i$ and $K_j \cong L_j$ for $j \ne i$. Following
O'Meara: $L_i \cong \langle\xi A(0,0)\rangle \perp \langle\xi A(0,0)\rangle \perp \cdots$ by 93:18 (v), and two
applications of 93:13 turn the two planes into $\langle\xi A(\xi^{-1}a_i, 0)\rangle$ and
$\langle\xi A(\xi^{-1}b_i, 0)\rangle$. -/
theorem exists_saturate_one (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V}
    (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (i : Fin t) (hrk : 7 ≤ finrank R (Ls i)) :
    ∃ Ks : Fin t → Submodule R V, IsJordanSplitting Q L Ks ∧
      normGroup Q (Ks i) = fundNormGroup Q L Ls i ∧ ∀ j, j ≠ i → IsometricLat Q Q (Ls j) (Ks j) := by
  have hLi : Ls i ≤ L := hL.split.iSup_eq ▸ le_iSup Ls i
  have hifg : (Ls i).FG := FG.of_le hfg hLi
  obtain ⟨ξ, hξ, hsi⟩ := exists_eq_span_singleton (R := R) ((hL.modular i).2.1 ▸ scale_fg Q hifg)
    (hL.modular i).1
  have hmodi : IsModular Q (R ∙ ξ) (Ls i) := hsi ▸ hL.modular i
  -- the fundamental generators
  obtain ⟨z, -, ha⟩ := exists_isNormGenerator_Q Q (fundSub_fg Q hfg Ls i)
  obtain ⟨b, hb⟩ := exists_weightGen Q h2p (fundSub_fg Q hfg Ls i) (isRegular_fundSub Q hfg hreg hL i)
    (fundSub_ne_bot Q hfg hL i)
  have hbg : b ∈ fundNormGroup Q L Ls i :=
    normGroupIdeal_subset Q _ ((weight_bounds Q _).2.1 (hb ▸ mem_span_singleton_self b))
  -- `L_i = P₁ ⊥ M₁`, `P₁ ≅ ξA(0,0)`
  obtain ⟨x₁, y₁, M₁, hQx₁, hQy₁, hxy₁, hs₁, hM₁, hrk₁⟩ := exists_hyp_split Q hK h2p hξ hifg hmodi (by omega)
  -- first retargeting: `Q(x₁') = a`
  obtain ⟨Ks₁, hK₁, hiso₁, x₁', y₁', M₁', hQx₁', hxy₁', hQy₁', hs₁', hMM₁⟩ :=
    exists_retarget Q hfg hL i hξ hsi hs₁ hQx₁ hQy₁ hxy₁ hM₁ ha.1
  have hfund₁ : ∀ j, fundNormGroup Q L Ks₁ j = fundNormGroup Q L Ls j := fun j =>
    fundNormGroup_eq_of_isJordanSplitting hfg hL hK₁ j j rfl
  have hsc₁ : scale Q (Ks₁ i) = R ∙ ξ := by
    obtain ⟨h, hs⟩ := hL.sameJordanType Q hfg hK₁
    have hi : Fin.cast h i = i := Fin.ext (by simp)
    have := (hs i).1
    rw [hi] at this
    rw [← this, hsi]
  have hK₁i : (Ks₁ i).FG := FG.of_le hfg (hK₁.split.iSup_eq ▸ le_iSup Ks₁ i)
  have hM₁'fg : M₁'.FG := FG.of_le hK₁i (hs₁'.sup_eq ▸ le_sup_right)
  have hM₁' : IsModular Q (R ∙ ξ) M₁' := IsometricLat.isModular Q Q hMM₁ (FG.of_le hifg (hs₁.sup_eq ▸ le_sup_right)) hM₁
  have hrk₁' : finrank R M₁' = finrank R M₁ := by obtain ⟨f, -⟩ := hMM₁; exact f.finrank_eq.symm
  -- `M₁' = P₂ ⊥ B₂`
  obtain ⟨x₂, y₂, B₂, hQx₂, hQy₂, hxy₂, hs₂, hB₂, hrk₂⟩ := exists_hyp_split Q hK h2p hξ hM₁'fg hM₁' (by omega)
  obtain ⟨hrot, hrot'⟩ := isOrthSum_rotate Q hs₁' hs₂
  have hP₁'mod : IsModular Q (R ∙ ξ) (span R {x₁', y₁'}) := by
    have hx₁'s : Q x₁' ∈ R ∙ ξ := by
      rw [← hsc₁]; exact normIdeal_le_scale Q _ (Q_mem_normIdeal Q (hs₁'.sup_eq ▸ mem_sup_left
        (subset_span (by simp))))
    obtain ⟨α', hα'⟩ := mem_span_singleton.mp hx₁'s
    refine (D18.span_pair_isModular Q hξ (p := α') (q := 0) (e := 1) (by simp) ?_ ?_ ?_).1
    · rw [← hα', Algebra.smul_def, mul_comm]
    · rw [hQy₁', map_zero, mul_zero]
    · rw [hxy₁', map_one, mul_one]
  have hB₂fg : B₂.FG := FG.of_le hM₁'fg (hs₂.sup_eq ▸ le_sup_right)
  have hMod₂ : IsModular Q (R ∙ ξ) (span R {x₁', y₁'} ⊔ B₂) :=
    (isModular_sup Q hP₁'mod hB₂ (FG.of_le hK₁i (hs₁'.sup_eq ▸ le_sup_left)) hB₂fg hrot'.orth).1
  -- second retargeting: `Q(x₂') = b`
  obtain ⟨Ks₂, hK₂, hiso₂, x₂', y₂', M₂', hQx₂', -, -, hs₂', hMM₂⟩ :=
    exists_retarget Q hfg hK₁ i hξ hsc₁ hrot hQx₂ hQy₂ hxy₂ hMod₂ ((hfund₁ i).symm ▸ hbg)
  refine ⟨Ks₂, hK₂, ?_, fun j hj => adj_isometricLat_trans Q Q Q (hiso₁ j hj) (hiso₂ j hj)⟩
  have hfund₂ : fundNormGroup Q L Ks₂ i = fundNormGroup Q L Ls i :=
    fundNormGroup_eq_of_isJordanSplitting hfg hL hK₂ i i rfl
  rw [← hfund₂]
  -- `a` and `b` are in `𝔤K_i`
  have hfs : fundSub Q L Ks₂ i = fundSub Q L Ls i := by
    unfold fundSub
    obtain ⟨h, hs⟩ := hL.sameJordanType Q hfg hK₂
    have hi : Fin.cast h i = i := Fin.ext (by simp)
    have := (hs i).1
    rw [hi] at this
    rw [this]
  have hx₂'K : x₂' ∈ Ks₂ i := hs₂'.sup_eq ▸ mem_sup_left (subset_span (by simp))
  have hx₁'M : x₁' ∈ span R {x₁', y₁'} ⊔ B₂ := mem_sup_left (subset_span (by simp))
  obtain ⟨f, hf⟩ := hMM₂
  have hfx : (f ⟨x₁', hx₁'M⟩ : V) ∈ Ks₂ i := hs₂'.sup_eq ▸ mem_sup_right (f ⟨x₁', hx₁'M⟩).2
  refine normGroup_eq_fund_of_mem Q h2p hfg hreg hK₂ i (a := Q z) (b := b) (hfs ▸ ha) (hfs ▸ hb) ?_ ?_
  · have h1 : Q (f ⟨x₁', hx₁'M⟩ : V) = Q x₁' := hf _
    rw [← hQx₁', ← h1]; exact Q_mem_normGroup Q hfx
  · rw [← hQx₂']; exact Q_mem_normGroup Q hx₂'K

/-- **93:21, step 1** (O'Meara 1963, p. 265): if every component of a Jordan splitting has dimension $\ge 7$, then
$L$ has a saturated Jordan splitting. "Do all this for $i = 1$, then for $i = 2$, etc.": by induction on the set
$S$ of indices already treated (`exists_saturate_one` keeps the other components up to isometry, hence their norm
groups and dimensions). -/
theorem exists_saturated_of_seven_le (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V}
    (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (hrk : ∀ i, 7 ≤ finrank R (Ls i)) : ∃ Ks : Fin t → Submodule R V, IsSaturated Q L Ks := by
  have hS : ∀ S : Finset (Fin t), ∃ Ks : Fin t → Submodule R V, IsJordanSplitting Q L Ks ∧
      (∀ j, finrank R (Ks j) = finrank R (Ls j)) ∧ ∀ j ∈ S, normGroup Q (Ks j) = fundNormGroup Q L Ls j := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨Ls, hL, fun _ => rfl, fun _ h => absurd h (Finset.notMem_empty _)⟩
    | insert i S hiS ih =>
      obtain ⟨Ks, hKs, hrkK, hgK⟩ := ih
      obtain ⟨Ks', hKs', hg', hiso⟩ :=
        exists_saturate_one Q hK h2p hfg hreg hKs i (by rw [hrkK]; exact hrk i)
      have hfund : ∀ j, fundNormGroup Q L Ks j = fundNormGroup Q L Ls j := fun j =>
        fundNormGroup_eq_of_isJordanSplitting hfg hL hKs j j rfl
      refine ⟨Ks', hKs', fun j => ?_, fun j hj => ?_⟩
      · obtain ⟨h, hs⟩ := hKs.sameJordanType Q hfg hKs'
        have hj : Fin.cast h j = j := Fin.ext (by simp)
        have := (hs j).2.1
        rw [hj] at this
        rw [← this, hrkK]
      · by_cases hji : j = i
        · subst hji; rw [hg', hfund]
        · rw [← adj_normGroup_eq Q Q (hiso j hji)]
          exact hgK j ((Finset.mem_insert.mp hj).resolve_left hji)
  obtain ⟨Ks, hKs, -, hg⟩ := hS Finset.univ
  refine ⟨Ks, hKs, fun i => ?_⟩
  rw [hg i (Finset.mem_univ i)]
  exact (fundNormGroup_eq_of_isJordanSplitting hfg hL hKs i i rfl).symm

end Step

section Adjoin

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- Orthogonal sublattices one of which is regular are disjoint. -/
theorem disjoint_of_orth {A B : Submodule R V} (hA : IsRegular Q A) (h : ∀ x ∈ A, ∀ y ∈ B, bil Q x y = 0) :
    Disjoint A B := by
  rw [disjoint_def]
  intro v hvA hvB
  exact hA v hvA fun a ha => by rw [bil_comm]; exact h a ha v hvB

/-- Two spans of pairs are orthogonal if their generators are. -/
theorem orth_span_pair {x y a b : V} (hxa : bil Q x a = 0) (hxb : bil Q x b = 0) (hya : bil Q y a = 0)
    (hyb : bil Q y b = 0) : ∀ u ∈ span R {x, y}, ∀ v ∈ span R {a, b}, bil Q u v = 0 := by
  intro u hu v hv
  obtain ⟨α, β, rfl⟩ := mem_span_pair.mp hu
  obtain ⟨γ, δ, rfl⟩ := mem_span_pair.mp hv
  simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, hxa, hxb, hya, hyb, mul_zero,
    add_zero]

/-- **Adjoining a modular lattice to a Jordan component** (O'Meara 1963, 93:21, step 2, p. 265): if
$L = L_1 \perp \cdots \perp L_t$ is a Jordan splitting and $H \perp L$ is $\mathfrak sL_i$-modular, then
$L \perp H = L_1 \perp \cdots \perp (L_i \perp H) \perp \cdots \perp L_t$ is a Jordan splitting, and
$\dim(L_i \perp H) = \dim L_i + \dim H$. -/
theorem isJordanSplitting_adjoin {L H : Submodule R V} (hfg : L.FG) (hHfg : H.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (i : Fin t)
    (hH : IsModular Q (scale Q (Ls i)) H) (horth : ∀ x ∈ H, ∀ y ∈ L, bil Q x y = 0) :
    IsJordanSplitting Q (L ⊔ H) (Function.update Ls i (Ls i ⊔ H)) ∧
      finrank R ↥(Ls i ⊔ H) = finrank R (Ls i) + finrank R H := by
  set Ks := Function.update Ls i (Ls i ⊔ H) with hKs
  have hLj : ∀ j, Ls j ≤ L := fun j => hL.split.iSup_eq ▸ le_iSup Ls j
  have hKi : Ks i = Ls i ⊔ H := by simp [hKs]
  have hKj : ∀ j, j ≠ i → Ks j = Ls j := fun j hj => by simp [hKs, Function.update_of_ne hj]
  have hHL : ∀ x ∈ Ls i, ∀ y ∈ H, bil Q x y = 0 := fun x hx y hy => by
    rw [bil_comm]; exact horth y hy x (hLj i hx)
  obtain ⟨hmodi, hrk⟩ := isModular_sup Q (hL.modular i) hH (FG.of_le hfg (hLj i)) hHfg hHL
  have horth_i : ∀ j, j ≠ i → ∀ x ∈ Ls i ⊔ H, ∀ y ∈ Ls j, bil Q x y = 0 := by
    intro j hj x hx y hy
    obtain ⟨l, hl, h, hh, rfl⟩ := mem_sup.mp hx
    rw [bil_add_left, hL.split.orth i j (Ne.symm hj) l hl y hy, horth h hh y (hLj j hy), add_zero]
  have hor : ∀ j k, j ≠ k → ∀ x ∈ Ks j, ∀ y ∈ Ks k, bil Q x y = 0 := by
    intro j k hjk x hx y hy
    by_cases hj : j = i
    · subst hj; rw [hKi] at hx; rw [hKj k (Ne.symm hjk)] at hy
      exact horth_i k (Ne.symm hjk) x hx y hy
    · rw [hKj j hj] at hx
      by_cases hk : k = i
      · subst hk; rw [hKi] at hy
        rw [bil_comm]; exact horth_i j hj y hy x hx
      · rw [hKj k hk] at hy; exact hL.split.orth j k hjk x hx y hy
  have hsc : ∀ j, scale Q (Ks j) = scale Q (Ls j) := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hKi]; exact hmodi.2.1
    · rw [hKj j hj]
  have hmod : ∀ j, IsModular Q (scale Q (Ks j)) (Ks j) := by
    intro j
    rw [hsc j]
    by_cases hj : j = i
    · subst hj; rw [hKi]; exact hmodi
    · rw [hKj j hj]; exact hL.modular j
  have hKL : ∀ j, Ks j ≤ L ⊔ H := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hKi]; exact sup_le_sup_right (hLj _) _
    · rw [hKj j hj]; exact (hLj j).trans le_sup_left
  have hfg' : (L ⊔ H).FG := hfg.sup hHfg
  refine ⟨⟨⟨hor, iSupIndep_of_orth Q hor fun j => (hmod j).isRegular Q (FG.of_le hfg' (hKL j)), ?_⟩, hmod, ?_⟩,
    by rw [hrk]⟩
  · apply le_antisymm (iSup_le hKL)
    refine sup_le ?_ ?_
    · rw [← hL.split.iSup_eq]
      refine iSup_le fun j => ?_
      by_cases hj : j = i
      · subst hj; exact le_sup_left.trans (hKi ▸ le_iSup Ks j)
      · exact (hKj j hj) ▸ le_iSup Ks j
    · exact le_sup_right.trans (hKi ▸ le_iSup Ks i)
  · have : (fun j => scale Q (Ks j)) = fun j => scale Q (Ls j) := funext hsc
    rw [this]; exact hL.scale_strictAnti

/-- **The fundamental norm groups are not altered by splitting off a hyperbolic plane** (O'Meara 1963, §93E):
if $N = P \perp M$ with $P = \mathfrak ox + \mathfrak oy \cong \xi A(0,0)$ and $\mathfrak a \subseteq
\mathfrak s(M^{\mathfrak a})$, then $\mathfrak g(N^{\mathfrak a}) = \mathfrak g(M^{\mathfrak a})$. -/
theorem normGroup_subA_eq_compl {N M : Submodule R V} {x y : V} {ξ : F} (hs : IsOrthSum Q N (span R {x, y}) M)
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = ξ) {a : Submodule R F}
    (haM : a ≤ scale Q (subA Q a M)) : normGroup Q (subA Q a N) = normGroup Q (subA Q a M) := by
  refine le_antisymm (normGroup_subA_le_compl Q hs hQx hQy hxy haM) (normGroup_mono Q ?_)
  rintro m ⟨hmM, hm⟩
  refine ⟨hs.sup_eq ▸ mem_sup_right hmM, fun l hl => ?_⟩
  rw [← hs.sup_eq] at hl
  obtain ⟨p, hp, u, hu, rfl⟩ := mem_sup.mp hl
  rw [bil_add_right, bil_comm, hs.orth p hp m hmM, zero_add]
  exact hm u hu

/-- **The norm group of $P \perp J$** with $P \cong \xi A(0,0)$ and $J$ $\xi\mathfrak o$-modular: $\mathfrak g(P
\perp J) = \mathfrak gJ$ (since $\mathfrak gP = 2\xi\mathfrak o \subseteq \mathfrak gJ$). -/
theorem normGroup_eq_of_hyp_split {K J : Submodule R V} {x y : V} {ξ : F} (hξ : ξ ≠ 0) (hs : IsOrthSum Q K (span R {x, y}) J)
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : bil Q x y = ξ) (hJ : scale Q J = R ∙ ξ) :
    normGroup Q K = normGroup Q J := by
  refine le_antisymm ?_ (normGroup_mono Q (hs.sup_eq ▸ le_sup_right))
  rw [← hs.sup_eq, normGroup_sup_of_orth Q hs.orth]
  refine sup_le ?_ le_rfl
  rintro _ ⟨p, hp, c, hc, rfl⟩
  obtain ⟨α, β, rfl⟩ := mem_span_pair.mp hp
  have hsP : scale Q (span R {x, y}) ≤ R ∙ ξ :=
    (D18.span_pair_isModular Q hξ (p := 0) (q := 0) (e := 1) (by simp) (by rw [hQx]; simp)
      (by rw [hQy]; simp) (by rw [hxy]; simp)).1.2.1.le
  rw [Q_hyp_comb Q hQx hQy hxy]
  have : 2 * (algebraMap R F (α * β) * ξ) + 2 * c = 2 * (algebraMap R F (α * β) * ξ + c) := by ring
  rw [this]
  refine two_mul_mem_normGroup Q ?_
  rw [hJ]
  refine add_mem ?_ (hsP hc)
  rw [← Algebra.smul_def]; exact smul_mem _ _ (mem_span_singleton_self ξ)

/-- In $N = P \perp M$, $M^{\mathfrak a} \subseteq N^{\mathfrak a}$. -/
theorem subA_le_of_isOrthSum {N P M : Submodule R V} (hs : IsOrthSum Q N P M) (a : Submodule R F) :
    subA Q a M ≤ subA Q a N := by
  rintro m ⟨hmM, hm⟩
  refine ⟨hs.sup_eq ▸ mem_sup_right hmM, fun l hl => ?_⟩
  rw [← hs.sup_eq] at hl
  obtain ⟨p, hp, u, hu, rfl⟩ := mem_sup.mp hl
  rw [bil_add_right, bil_comm, hs.orth p hp m hmM, zero_add]
  exact hm u hu

/-- **Shrinking a Jordan component**: if $L = K_1 \perp \cdots \perp K_t$ is a Jordan splitting and $J \subseteq K_i$
is modular of scale $\mathfrak sK_i$, then $J \perp \sum_{j \ne i} K_j$ has the Jordan splitting obtained by
replacing $K_i$ by $J$. -/
theorem isJordanSplitting_update_sub {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ks : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ks) (i : Fin t) {J : Submodule R V} (hJ : J ≤ Ks i)
    (hJmod : IsModular Q (scale Q (Ks i)) J) :
    IsJordanSplitting Q (J ⊔ others Ks i) (Function.update Ks i J) := by
  set Ms := Function.update Ks i J with hMs
  have hMi : Ms i = J := by simp [hMs]
  have hMj : ∀ j, j ≠ i → Ms j = Ks j := fun j hj => by simp [hMs, Function.update_of_ne hj]
  have hle : ∀ j, Ms j ≤ Ks j := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hMi]; exact hJ
    · rw [hMj j hj]
  have hLj : ∀ j, Ks j ≤ L := fun j => hL.split.iSup_eq ▸ le_iSup Ks j
  have hor : ∀ j k, j ≠ k → ∀ x ∈ Ms j, ∀ y ∈ Ms k, bil Q x y = 0 := fun j k hjk x hx y hy =>
    hL.split.orth j k hjk x (hle j hx) y (hle k hy)
  have hsc : ∀ j, scale Q (Ms j) = scale Q (Ks j) := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [hMi]; exact hJmod.2.1
    · rw [hMj j hj]
  have hmod : ∀ j, IsModular Q (scale Q (Ms j)) (Ms j) := by
    intro j
    rw [hsc j]
    by_cases hj : j = i
    · subst hj; rw [hMi]; exact hJmod
    · rw [hMj j hj]; exact hL.modular j
  refine ⟨⟨hor, iSupIndep_of_orth Q hor fun j => (hmod j).isRegular Q (FG.of_le hfg ((hle j).trans (hLj j))),
    ?_⟩, hmod, ?_⟩
  · apply le_antisymm
    · refine iSup_le fun j => ?_
      by_cases hj : j = i
      · subst hj; rw [hMi]; exact le_sup_left
      · rw [hMj j hj]; exact (le_others Ks hj).trans le_sup_right
    · refine sup_le (hMi ▸ le_iSup Ms i) (others_le fun j hj => ?_)
      rw [← hMj j hj]; exact le_iSup Ms j
  · have : (fun j => scale Q (Ms j)) = fun j => scale Q (Ks j) := funext hsc
    rw [this]; exact hL.scale_strictAnti

/-- Two orthogonal hyperbolic planes $\xi A(0,0)$ form an `AdjPlaneSum` of length $2$. -/
theorem planeSum_two {X : Submodule R V} {x₁ y₁ x₂ y₂ : V} {ξ : F}
    (hs : IsOrthSum Q X (span R {x₁, y₁}) (span R {x₂, y₂})) (hQx₁ : Q x₁ = 0) (hQy₁ : Q y₁ = 0)
    (hxy₁ : bil Q x₁ y₁ = ξ) (hQx₂ : Q x₂ = 0) (hQy₂ : Q y₂ = 0) (hxy₂ : bil Q x₂ y₂ = ξ) :
    AdjPlaneSum Q ξ {0} 2 X := by
  have hp : ∀ {x y : V}, Q x = 0 → Q y = 0 → bil Q x y = ξ → AdjIsPlane Q ξ {0} (span R {x, y}) :=
    fun {x y} hQx hQy hxy => ⟨x, y, rfl, hxy, hQy, by rw [hQx]; rfl, by rw [hQx]; exact zero_mem _⟩
  exact ⟨_, _, hs, hp hQx₁ hQy₁ hxy₁, _, ⊥, (adj_isOrthSum_symm Q (adj_isOrthSum_bot Q _)),
    hp hQx₂ hQy₂ hxy₂, rfl⟩

end Adjoin

section Transport

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **Saturated splittings are carried along isometries of lattices**: if $L \cong K$ and $L$ has a saturated
Jordan splitting, so does $K$ (O'Meara 1963, §93E, p. 264: an isometry preserves the fundamental invariants). -/
theorem exists_saturated_of_isometricLat {L : Submodule R V} {K : Submodule R V'} (h : IsometricLat Q Q' L K)
    (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsSaturated Q L Ls) :
    ∃ Ks : Fin t → Submodule R V', IsSaturated Q' K Ks := by
  obtain ⟨Ks, hK, hiso, -, ⟨h0, hft⟩, -, -⟩ := exists_jordanSplitting_of_isometricLat Q Q' h hfg hL.1
  refine ⟨Ks, hK, fun i => ?_⟩
  have hc : Fin.cast h0 i = i := Fin.ext (by simp)
  have := (hft i).2.2
  rw [hc] at this
  rw [← this, ← adj_normGroup_eq Q Q' (hiso i), hL.2 i]

end Transport

section Main

universe u v

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **93:21, step 2, as an induction on the number of components of dimension $< 7$** (O'Meara 1963, p. 265).
For a component $L_i$ with $3 \le \dim L_i < 7$, make the $4$-dimensional $\mathfrak s_i$-modular hyperbolic
adjunction $H = \xi A(0,0) \perp \xi A(0,0)$ (in the space $V \perp (F^2 \perp F^2)$), so that
$L \perp H$ has the Jordan splitting with $i$-th component $L_i \perp H$ of dimension $\ge 7$; by induction it has a
saturated Jordan splitting $K_1 \perp \cdots \perp K_t$; then $K_i \cong \xi A(0,0) \perp \xi A(0,0) \perp J_i$
by 93:18 (v), $\mathfrak gJ_i = \mathfrak gK_i$, and cancelling the two hyperbolic planes (93:14) gives
$L \cong J_i \perp \sum_{j \ne i} K_j$, whose splitting is saturated. The space is allowed to vary, in the universe
`max u v` (`u` that of $F$), so that the adjoined space $V \times (F^2 \times F^2)$ is again admissible. -/
theorem exists_saturated_aux (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) (n : ℕ) :
    ∀ {V : Type (max v u)} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
      [FiniteDimensional F V] (Q : QuadraticForm F V) {L : Submodule R V}, L.FG →
      ∀ {t : ℕ} {Ls : Fin t → Submodule R V}, IsJordanSplitting Q L Ls → (∀ i, 3 ≤ finrank R (Ls i)) →
      (Finset.univ.filter fun i => finrank R (Ls i) < 7).card = n →
      ∃ Ks : Fin t → Submodule R V, IsSaturated Q L Ks := by
  classical
  induction n with
  | zero =>
    intro V _ _ _ _ _ Q L hfg t Ls hL _ hn
    refine exists_saturated_of_seven_le Q hK h2p hfg (isRegular_of_isJordanSplitting Q hfg hL) hL fun i => ?_
    by_contra h
    have hmem : i ∈ Finset.univ.filter fun i => finrank R (Ls i) < 7 := by simp [not_le.mp h]
    rw [Finset.card_eq_zero.mp hn] at hmem
    simp at hmem
  | succ n ih =>
    intro V _ _ _ _ _ Q L hfg t Ls hL h3 hn
    obtain ⟨i, hi⟩ : ∃ i, finrank R (Ls i) < 7 := by
      by_contra hc
      push Not at hc
      have : (Finset.univ.filter fun i => finrank R (Ls i) < 7) = ∅ :=
        Finset.filter_false_of_mem fun i _ => not_lt.mpr (hc i)
      rw [this] at hn; simp at hn
    have hLi : Ls i ≤ L := hL.split.iSup_eq ▸ le_iSup Ls i
    have hifg : (Ls i).FG := FG.of_le hfg hLi
    obtain ⟨ξ, hξ, hsi⟩ := exists_eq_span_singleton (R := R) ((hL.modular i).2.1 ▸ scale_fg Q hifg)
      (hL.modular i).1
    -- the adjoined space `F² ⊥ F²` with the form `ξA(0,0) ⊥ ξA(0,0)`
    let QW : QuadraticForm F ((F × F) × (F × F)) := (D18.hypForm ξ).prod (D18.hypForm ξ)
    let Q' : QuadraticForm F (V × ((F × F) × (F × F))) := Q.prod QW
    have key : ∀ a b : F × F, Q' (0, (a, b)) = 2 * ξ * (a.1 * a.2) + 2 * ξ * (b.1 * b.2) := by
      intro a b
      simp [Q', QW, QuadraticMap.prod_apply, D18.hypForm_apply]
    let E₁ : V × ((F × F) × (F × F)) := (0, ((1, 0), (0, 0)))
    let E₂ : V × ((F × F) × (F × F)) := (0, ((0, 1), (0, 0)))
    let E₃ : V × ((F × F) × (F × F)) := (0, ((0, 0), (1, 0)))
    let E₄ : V × ((F × F) × (F × F)) := (0, ((0, 0), (0, 1)))
    have hQ₁ : Q' E₁ = 0 := by simp only [E₁, key]; ring
    have hQ₂ : Q' E₂ = 0 := by simp only [E₂, key]; ring
    have hQ₃ : Q' E₃ = 0 := by simp only [E₃, key]; ring
    have hQ₄ : Q' E₄ = 0 := by simp only [E₄, key]; ring
    have hbil : ∀ {X Y : V × ((F × F) × (F × F))} {c : F}, X.1 = 0 → Y.1 = 0 →
        Q' (0, (X.2.1 + Y.2.1, X.2.2 + Y.2.2)) = Q' X + 2 * c + Q' Y → bil Q' X Y = c := by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ c hx hy h
      simp only at hx hy
      subst hx hy
      refine adj_eq_bil_of Q' ?_
      rw [show ((0 : V), x₂) + (0, y₂) = (0, (x₂.1 + y₂.1, x₂.2 + y₂.2)) from by ext <;> simp]
      exact h
    have h12 : bil Q' E₁ E₂ = ξ := hbil rfl rfl (by simp [E₁, E₂, key])
    have h34 : bil Q' E₃ E₄ = ξ := hbil rfl rfl (by simp [E₃, E₄, key])
    have h13 : bil Q' E₁ E₃ = 0 := hbil rfl rfl (by simp [E₁, E₃, key])
    have h14 : bil Q' E₁ E₄ = 0 := hbil rfl rfl (by simp [E₁, E₄, key])
    have h23 : bil Q' E₂ E₃ = 0 := hbil rfl rfl (by simp [E₂, E₃, key])
    have h24 : bil Q' E₂ E₄ = 0 := hbil rfl rfl (by simp [E₂, E₄, key])
    have hP₁₂ := D18.span_pair_isModular (R := R) Q' hξ (p := 0) (q := 0) (e := 1) (by simp) (by rw [hQ₁]; simp)
      (by rw [hQ₂]; simp) (by rw [h12]; simp)
    have hP₃₄ := D18.span_pair_isModular (R := R) Q' hξ (p := 0) (q := 0) (e := 1) (by simp) (by rw [hQ₃]; simp)
      (by rw [hQ₄]; simp) (by rw [h34]; simp)
    have hfg₁₂ : (span R {E₁, E₂}).FG := fg_span (Set.toFinite _)
    have hfg₃₄ : (span R {E₃, E₄}).FG := fg_span (Set.toFinite _)
    have horth₁₂ := orth_span_pair (R := R) Q' h13 h14 h23 h24
    set H := span R {E₁, E₂} ⊔ span R {E₃, E₄} with hHdef
    obtain ⟨hHmod, hHrk⟩ := isModular_sup Q' hP₁₂.1 hP₃₄.1 hfg₁₂ hfg₃₄ horth₁₂
    have hHfg : H.FG := hfg₁₂.sup hfg₃₄
    have hH0 : H ≤ (⊥ : Submodule R V).prod ⊤ := by
      refine sup_le ?_ ?_ <;> rw [span_le] <;> intro w hw <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw <;>
        rcases hw with rfl | rfl <;> exact ⟨(mem_bot R).mpr rfl, trivial⟩
    -- `L × 0` and its Jordan splitting
    set L₀ := L.prod (⊥ : Submodule R ((F × F) × (F × F))) with hL₀
    obtain ⟨f, hf⟩ : IsometricLat Q Q' L L₀ := adj_isometricLat_prod_bot Q QW L
    have hL₀fg : L₀.FG := by rw [hL₀, ← Submodule.map_inl]; exact hfg.map _
    have hJ₀ := isJordanSplitting_imgLat Q Q' f hf hfg hL
    have horthHL : ∀ x ∈ H, ∀ y ∈ L₀, bil Q' x y = 0 := by
      rintro ⟨x₁, x₂⟩ hx ⟨y₁, y₂⟩ hy
      have hx₁ : x₁ = 0 := (mem_bot R).mp (hH0 hx).1
      have hy₂ : y₂ = 0 := (mem_bot R).mp hy.2
      subst hx₁ hy₂
      rw [adj_bil_prod]; simp [bil]
    have hsc0 : scale Q' (imgLat f (Ls i)) = R ∙ ξ := (scale_imgLat Q Q' f hf hLi).trans hsi
    obtain ⟨hL', hrk'⟩ := isJordanSplitting_adjoin Q' hL₀fg hHfg hJ₀ i (hsc0 ▸ hHmod) horthHL
    set Ls' := Function.update (fun j => imgLat f (Ls j)) i (imgLat f (Ls i) ⊔ H) with hLs'
    have hfg' : (L₀ ⊔ H).FG := hL₀fg.sup hHfg
    have hrkj : ∀ j, j ≠ i → finrank R (Ls' j) = finrank R (Ls j) := fun j hj => by
      rw [hLs', Function.update_of_ne hj]
      exact finrank_imgLat f (hL.split.iSup_eq ▸ le_iSup Ls j)
    have hrki : finrank R (Ls' i) = finrank R (Ls i) + 4 := by
      rw [hLs', Function.update_self, hrk', finrank_imgLat f hLi, hHrk, hP₁₂.2, hP₃₄.2]
    have h3' : ∀ j, 3 ≤ finrank R (Ls' j) := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [hrki]; have := h3 j; omega
      · rw [hrkj j hj]; exact h3 j
    have hn' : (Finset.univ.filter fun j => finrank R (Ls' j) < 7).card = n := by
      have : (Finset.univ.filter fun j => finrank R (Ls' j) < 7) =
          (Finset.univ.filter fun j => finrank R (Ls j) < 7).erase i := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        by_cases hj : j = i
        · subst hj; rw [hrki]; have := h3 j; simp; omega
        · rw [hrkj j hj]; simp [hj]
      rw [this, Finset.card_erase_of_mem (by simp [hi]), hn]; rfl
    obtain ⟨K', hK'⟩ := ih Q' hfg' hL' h3' hn'
    -- the component `K'_i`
    obtain ⟨h0, hJT⟩ := hL'.sameJordanType Q' hfg' hK'.1
    have hc : Fin.cast h0 i = i := Fin.ext (by simp)
    have hscK : scale Q' (K' i) = R ∙ ξ := by
      have := (hJT i).1; rw [hc] at this
      rw [← this, hLs', Function.update_self]
      exact (isModular_sup Q' ((isModular_imgLat Q Q' f hf hLi (R ∙ ξ)).mpr (hsi ▸ hL.modular i)) hHmod
        (FG.of_le hL₀fg (imgLat_le f _)) hHfg fun x hx y hy => by
          rw [bil_comm]; exact horthHL y hy x (imgLat_le f _ hx)).1.2.1
    have hrkK : 7 ≤ finrank R (K' i) := by
      have := (hJT i).2.1; rw [hc] at this
      rw [← this, hrki]; have := h3 i; omega
    have hK'ifg : (K' i).FG := FG.of_le hfg' (hK'.1.split.iSup_eq ▸ le_iSup K' i)
    have hK'mod : IsModular Q' (R ∙ ξ) (K' i) := hscK ▸ hK'.1.modular i
    obtain ⟨x₁, y₁, M₁, hQx₁, hQy₁, hxy₁, hs₁, hM₁, hrk₁⟩ :=
      exists_hyp_split Q' hK h2p hξ hK'ifg hK'mod (by omega)
    have hM₁fg : M₁.FG := FG.of_le hK'ifg (hs₁.sup_eq ▸ le_sup_right)
    obtain ⟨x₂, y₂, J, hQx₂, hQy₂, hxy₂, hs₂, hJmod, hrk₂⟩ :=
      exists_hyp_split Q' hK h2p hξ hM₁fg hM₁ (by omega)
    obtain ⟨hA, hA'⟩ := adj_isOrthSum_assoc_left Q' hs₁ hs₂
    have hsL := isOrthSum_others Q' hK'.1.split i hA
    have hsH : IsOrthSum Q' (L₀ ⊔ H) H L₀ :=
      ⟨horthHL, disjoint_of_orth Q' (hHmod.isRegular Q' hHfg) horthHL, sup_comm _ _⟩
    have hsH₁₂ : IsOrthSum Q' H (span R {E₁, E₂}) (span R {E₃, E₄}) :=
      ⟨horth₁₂, disjoint_of_orth Q' (hP₁₂.1.isRegular Q' hfg₁₂) horth₁₂, rfl⟩
    have hcancel : IsometricLat Q' Q' (J ⊔ others K' i) L₀ :=
      adj_planeSum_cancel Q' hξ 2 (adj_isometricLat_refl Q' _) hsL hsH
        (planeSum_two Q' hA' hQx₁ hQy₁ hxy₁ hQx₂ hQy₂ hxy₂) (planeSum_two Q' hsH₁₂ hQ₁ hQ₂ h12 hQ₃ hQ₄ h34)
    -- the saturated splitting of `M = J ⊥ ∑_{j ≠ i} K'_j`
    have hJK : J ≤ K' i := hs₁.sup_eq ▸ le_sup_of_le_right (hs₂.sup_eq ▸ le_sup_right)
    have hMs := isJordanSplitting_update_sub Q' hfg' hK'.1 i hJK (hscK ▸ hJmod)
    set M := J ⊔ others K' i with hMdef
    set Ms := Function.update K' i J with hMsdef
    have hMfg : M.FG := FG.of_le hfg' (hsL.sup_eq ▸ le_sup_right)
    have hgJ : normGroup Q' J = normGroup Q' (K' i) := by
      rw [normGroup_eq_of_hyp_split Q' hξ hs₁ hQx₁ hQy₁ hxy₁ hM₁.2.1,
        normGroup_eq_of_hyp_split Q' hξ hs₂ hQx₂ hQy₂ hxy₂ hJmod.2.1]
    have hscM : ∀ j, scale Q' (Ms j) = scale Q' (K' j) := by
      intro j
      by_cases hj : j = i
      · subst hj; simp only [hMsdef, Function.update_self]; rw [hJmod.2.1, hscK]
      · simp only [hMsdef, Function.update_of_ne hj]
    have hgM : ∀ j, normGroup Q' (Ms j) = normGroup Q' (K' j) := by
      intro j
      by_cases hj : j = i
      · subst hj; simp only [hMsdef, Function.update_self]; exact hgJ
      · simp only [hMsdef, Function.update_of_ne hj]
    obtain ⟨hB₁, hB₂⟩ := adj_isOrthSum_assoc_right Q' hsL hA'
    have hsat : IsSaturated Q' M Ms := by
      refine ⟨hMs, fun j => ?_⟩
      rw [hgM, hK'.2 j, fundNormGroup, fundNormGroup, fundSub, fundSub, hscM j]
      set a := scale Q' (K' j)
      have haM : a ≤ scale Q' (subA Q' a M) := by
        have := scale_mono Q' (le_fundSub Q' hMfg hMs j)
        rw [fundSub, hscM j] at this
        exact this
      have haN : a ≤ scale Q' (subA Q' a (span R {x₂, y₂} ⊔ M)) :=
        haM.trans (scale_mono Q' (subA_le_of_isOrthSum Q' hB₂ a))
      rw [normGroup_subA_eq_compl Q' hB₁ hQx₁ hQy₁ hxy₁ haN, normGroup_subA_eq_compl Q' hB₂ hQx₂ hQy₂ hxy₂ haM]
    exact exists_saturated_of_isometricLat Q' Q
      (adj_isometricLat_trans Q' Q' Q hcancel (adj_isometricLat_symm Q Q' ⟨f, hf⟩)) hMfg hsat

/-- **Proposition 93:21** (O'Meara 1963, §93E, p. 265), proved: "Suppose $L$ has a Jordan splitting
$L = L_1 \perp \cdots \perp L_t$ in which $\dim L_i \ge 3$ for $1 \le i \le t$. Then $L$ has a saturated Jordan
splitting." Here $F$ is the fraction field of a Henselian discrete valuation ring $R$ with finite residue field, of
characteristic $0$ and satisfying the Hilbert-symbol axioms `LocalHilbertField` (true for the completions of number
fields, `HasseIsoNF.localHilbertField_adicCompletion`); the named statement `SaturatedSplittingExistence` holds for
every quadratic space over $F$. The proof is O'Meara's: `exists_saturated_aux` (step 2, by induction, with the
space $V$ replaced by `ULift V` to fix the universe), resting on `exists_saturated_of_seven_le`. -/
@[kb "omeara1963" "§93E, 93:21, p. 265"]
theorem saturatedSplittingExistence (hK : LocalHilbertField F) {V : Type*} [AddCommGroup V] [Module F V]
    [Module R V] [IsScalarTower R F V] [FiniteDimensional F V] (Q : QuadraticForm F V) :
    SaturatedSplittingExistence R Q := by
  refine ⟨fun h2p _ L _ t Ls hL h3 => ?_⟩
  have hfg : L.FG := Submodule.IsLattice.fg (A := F)
  let eF : ULift.{u} V ≃ₗ[F] V := ULift.moduleEquiv
  let eR : ULift.{u} V ≃ₗ[R] V := ULift.moduleEquiv
  have : FiniteDimensional F (ULift.{u} V) := Module.Finite.equiv eF.symm
  let Q₁ : QuadraticForm F (ULift.{u} V) := Q.comp eF.toLinearMap
  let L₁ : Submodule R (ULift.{u} V) := L.map eR.symm.toLinearMap
  have hiso : IsometricLat Q Q₁ L L₁ := ⟨eR.symm.submoduleMap L, fun x => rfl⟩
  have hfg₁ : L₁.FG := hfg.map _
  obtain ⟨Ks₁, hK₁, hiso₁, -, -, -, -⟩ := exists_jordanSplitting_of_isometricLat Q Q₁ hiso hfg hL
  have h3' : ∀ i, 3 ≤ finrank R (Ks₁ i) := fun i => by
    obtain ⟨g, -⟩ := hiso₁ i; rw [← g.finrank_eq]; exact h3 i
  obtain ⟨Ks', hsat⟩ := exists_saturated_aux hK h2p _ Q₁ hfg₁ hK₁ h3' rfl
  exact exists_saturated_of_isometricLat Q₁ Q (adj_isometricLat_symm Q Q₁ hiso) hfg₁ hsat

end Main

section NumberField

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type*} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]

/-- **Proposition 93:21 over the completion $F_\mathfrak p$ of a number field** (O'Meara 1963, §93E, p. 265):
`SaturatedSplittingExistence` holds unconditionally for every quadratic space over $F_\mathfrak p$ (the dyadic
hypothesis is part of the statement). -/
@[kb "omeara1963" "§93E, 93:21, p. 265 (completion of a number field)"]
theorem saturatedSplittingExistence_nf (Q : QuadraticForm (v.adicCompletion F) V) :
    SaturatedSplittingExistence (v.adicCompletionIntegers F) Q :=
  saturatedSplittingExistence (HasseIsoNF.localHilbertField_adicCompletion v) Q

end NumberField

end QuadFormsKB.OMeara.Sat93
