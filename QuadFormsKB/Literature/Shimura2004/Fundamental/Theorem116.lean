/-
# Shimura 2004, Theorem 11.6 (i), (ii), (v), (13.18) and Theorem 12.14 (iv), from Theorem 10.5

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 11.6 (printed
pp. 104–105), (13.18) (p. 134) and Theorem 12.14 (iv) (p. 123). Notation as in `HGenus.lean`.

**Shimura's proof, as formalized here** (left actions). Fix $h$ with $q = \varphi[h] \ne 0$ and
$\mathfrak b = \varphi(h, L)$. For $x \in L_i[q, \mathfrak b]$ choose $\alpha_x \in G = SO^\varphi(V)$ with
$x = \alpha_x h$ (Witt, `exists_so_mulVec_eq`) and put $M_x = \alpha_x^{-1}L_i$.
1. $M_x$ lies in the $G$-genus of $L$ and $\varphi(h, M_x) = \varphi(x, L_i) = \mathfrak b$; by Theorem 10.5 at
   every prime, a lattice $M = \beta L$ ($\beta\in G_{\mathbf h}$) with $\varphi(h, M) = \varphi(h, L)$ is in the
   $H$-genus: at each $v$, $\beta_v^{-1}h = c_vh$ with $c_v \in C_v$, so $\eta = \beta c \in H_{\mathbf h}$ and
   $\eta L = M$ (`mem_hGenus_of_phiIdeal`). Choose such an $\eta_x$ and put $g_i(x) = \eta_x D$,
   $D = H_{\mathbf h}\cap C$.
2. $\eta_y D \in H\eta_x D$ iff $M_y = \varepsilon M_x$ for some $\varepsilon \in H$ (`mk_mem_orbit_iff`), iff
   $\gamma L_i = L_j$ and $\gamma x = y$ for some $\gamma \in G$ ($\gamma = \alpha_y\varepsilon\alpha_x^{-1}$,
   `rel_iff`). This gives (i): the map is well defined, injective (minimality of $\{L_i\}$) and onto (a lattice
   $\eta L$ of the $H$-genus is $\gamma L_i$, and $x = \gamma^{-1}h \in L_i[q, \mathfrak b]$ because $\varphi(h, \eta
   L) = \varphi(h, L)$ is local, `phiIdeal_eq_of_mem_hGenus`).
3. (ii): $\gamma \mapsto \alpha_x^{-1}\gamma\alpha_x$ identifies the stabilizer of $x$ in $\Gamma(L_i)$ with
   $H \cap \eta_x C\eta_x^{-1}$, the stabilizer of $\eta_x D$ in $H$.
4. (v): $\Lambda[q, \mathfrak b] \ne \emptyset$ iff $\alpha^{-1}\Lambda$ is in the $H$-genus for some $\alpha$, iff
   $\Lambda$ is $G$-equivalent to some $L_i$.

**Proves** (standard axioms only)
* unconditional (Shimura's Theorem 10.5 is proved, `theorem10_5_holds`, `Theorem105.lean`; it was the named
  input `LocalTheorem10_5`):
  `theorem11_6_ii_holds` (`Theorem11_6_ii`, Theorem 11.6 (i), (ii)), `theorem11_6_v_holds` (`Theorem11_6_v`),
  `formula_13_18_holds` ((13.18)), `theorem11_6_i_definite` (Theorem 11.6 (i) and (11.7) for totally positive
  definite $\varphi$), and, with the one-class input `SumSquaresOneClass`, `theorem_12_14_iv_of_local`
  (Theorem 12.14 (iv));
* conditional on the finiteness input `HClassNumberFinite` (indefinite $\varphi$ only; it is
  proved here for definite $\varphi$): `theorem11_6_i_holds` (`Theorem11_6_i`) and so the old input
  `FundamentalTheorem11_6` (`fundamentalTheorem11_6_holds`).
-/
import QuadFormsKB.Literature.Shimura2004.Fundamental.Local
import QuadFormsKB.Citation

open NumberField IsDedekindDomain Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

attribute [local instance] invTwo latAction

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### Step 1: lattices of the $G$-genus with $\varphi(h, M) = \varphi(h, L)$ are in the $H$-genus -/

/-- A rational point of $SO^\varphi(V)$ lies in $SO^\varphi(V)_{\mathbf h}$. -/
theorem diagF_mem_soAf {γ : orthGroup Q F} (hγ : γ ∈ soSub Q F) : diagF Q γ ∈ soAf Q := by
  intro v
  change ((orthMap Q (v.adicCompletion F) γ : orthGroup Q (v.adicCompletion F)) :
    GL (Fin n) (v.adicCompletion F)).val.det = 1
  rw [orthMap_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    show (γ : GL (Fin n) F).val.det = 1 from hγ, map_one]

theorem image_image (γ δ : GL (Fin n) F) (M : Lat F n) :
    Lat.image γ (Lat.image δ M) = Lat.image (γ * δ) M :=
  Lattices.Lat.ext (glImage_mul γ δ M.1).symm

theorem image_one (M : Lat F n) : Lat.image 1 M = M := Lattices.Lat.ext (glImage_one M.1)

/-- **Step 1** (Shimura 2004, proof of Theorem 11.6, p. 104), unconditional (Theorem 10.5 is proved): if $L$ is
$\mathfrak g$-maximal, $M$ is in the $G$-genus of $L$ and $\varphi(h, M) = \varphi(h, L)$, then $M$ is in the
$H$-genus of $L$. -/
theorem mem_hGenus_of_phiIdeal (hQ : Q.Nondegenerate) (hn : 2 < n) (h92 : Cond92 Q)
    {L : Lat F n} (hL : IsGMaximal Q L) {h : Fin n → F} (hh : Q.eval h ≠ 0) {M : Lat F n}
    (hM : M ∈ soGenus Q L)
    (hφ : phiIdeal Q.toQuadraticForm h M.1 = phiIdeal Q.toQuadraticForm h L.1) :
    M ∈ hGenus Q h L := by
  obtain ⟨β, hβ, rfl⟩ := hM
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : orthGroup Q (v.adicCompletion F),
      (c : GL (Fin n) (v.adicCompletion F)).val.det = 1 ∧
      locAct v (c : GL (Fin n) (v.adicCompletion F)) (loc v L.1) = loc v L.1 ∧
      (c : GL (Fin n) (v.adicCompletion F)).val *ᵥ locVec v h =
        (((β v)⁻¹ : orthGroup Q _) : GL (Fin n) (v.adicCompletion F)).val *ᵥ locVec v h := by
    intro v
    have hev : Q.evalIn (v.adicCompletion F) (locVec v h) = algebraMap F (v.adicCompletion F) (Q.eval h) := by
      have := locForm_locVec v Q h
      rwa [QuadForm.toQuadraticForm_apply, QuadForm.toQuadraticForm_apply, eval_map_eq] at this
    refine exists_locStab_mulVec_eq Q v hQ hn h92 hL ?_ ?_ ?_
    · rw [evalIn_mulVec_of_mem Q ((β v)⁻¹).2]
    · rw [hev]; exact (map_ne_zero _).2 hh
    · have hinv : loc v L.1 = locAct v (((β v)⁻¹ : orthGroup Q _) : GL (Fin n) (v.adicCompletion F))
          (locAct v ((β v : orthGroup Q _) : GL (Fin n) (v.adicCompletion F)) (loc v L.1)) := by
        rw [← locAct_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, locAct_one]
      conv_rhs => rw [hinv]
      rw [phiIdeal_locAct Q v ((β v)⁻¹).2, ← loc_latSMul, ← locFrac_phiIdeal, ← locFrac_phiIdeal]
      exact congrArg (locFrac v) hφ.symm
  choose c hcdet hcL hch using hloc
  let cA : OAf Q := ⟨fun v => c v, by
    filter_upwards [loc_eventually_std L.2] with v hv
    change locAct v _ (std v) = std v
    rw [← hv]; exact hcL v⟩
  have hcA : cA ∈ locStab Q L := fun v => hcL v
  refine ⟨β * cA, ⟨fun v => ?_, fun v => ?_⟩, ?_⟩
  · change (((β v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)) *
      ((c v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F))).val.det = 1
    rw [Units.val_mul, det_mul, hβ v, hcdet v, one_mul]
  · change (((β v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)) *
      ((c v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F))).val *ᵥ
      locVec v h = locVec v h
    rw [Units.val_mul, ← mulVec_mulVec, hch v, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul,
      mul_inv_cancel, Subgroup.coe_one, Units.val_one, one_mulVec]
  · have hstab : cA • L = L := by
      have : cA ∈ MulAction.stabilizer (OAf Q) L := by rw [stabilizer_eq_locStab]; exact hcA
      exact this
    rw [mul_smul, hstab]

/-! ### The construction -/

section Construction

variable {Q} (hQ : Q.Nondegenerate) (hn : 2 < n) {h : Fin n → F} (hh : Q.eval h ≠ 0) {L : Lat F n}

include hQ hn hh in
theorem exists_alpha {Λ : Lat F n} {b : Submodule (𝓞 F) F} (x : solSetLat Q Λ (Q.eval h) b) :
    ∃ α : orthGroup Q F, α ∈ soSub Q F ∧ (α : GL (Fin n) F).val *ᵥ h = x.1 := by
  refine exists_so_mulVec_eq Q hQ (by omega) ?_ hh
  have := x.2.1
  rwa [QuadForm.toQuadraticForm_apply] at this

/-- $\alpha_x \in SO^\varphi(V)$ with $\alpha_x h = x$. -/
def alphaOf {Λ : Lat F n} {b : Submodule (𝓞 F) F} (x : solSetLat Q Λ (Q.eval h) b) : orthGroup Q F :=
  (exists_alpha hQ hn hh x).choose

theorem alphaOf_mem {Λ : Lat F n} {b : Submodule (𝓞 F) F} (x : solSetLat Q Λ (Q.eval h) b) :
    alphaOf hQ hn hh x ∈ soSub Q F := (exists_alpha hQ hn hh x).choose_spec.1

theorem alphaOf_mulVec {Λ : Lat F n} {b : Submodule (𝓞 F) F} (x : solSetLat Q Λ (Q.eval h) b) :
    ((alphaOf hQ hn hh x : orthGroup Q F) : GL (Fin n) F).val *ᵥ h = x.1 :=
  (exists_alpha hQ hn hh x).choose_spec.2

end Construction

/-! ### The lattices $M_x = \alpha_x^{-1}\Lambda$ -/

section LatOf

variable {Q} (hQ : Q.Nondegenerate) (hn : 2 < n) {h : Fin n → F} (hh : Q.eval h ≠ 0)

/-- $M_x = \alpha_x^{-1}\Lambda$ for $x \in \Lambda[q, \mathfrak b]$. -/
def latOf {Λ : Lat F n} {b : Submodule (𝓞 F) F} (x : solSetLat Q Λ (Q.eval h) b) : Lat F n :=
  Lat.image ((alphaOf hQ hn hh x : orthGroup Q F) : GL (Fin n) F)⁻¹ Λ

theorem image_alpha_latOf {Λ : Lat F n} {b : Submodule (𝓞 F) F} (x : solSetLat Q Λ (Q.eval h) b) :
    Lat.image ((alphaOf hQ hn hh x : orthGroup Q F) : GL (Fin n) F) (latOf hQ hn hh x) = Λ := by
  rw [latOf, image_image, mul_inv_cancel, image_one]

theorem alpha_inv_mulVec {Λ : Lat F n} {b : Submodule (𝓞 F) F} (x : solSetLat Q Λ (Q.eval h) b) :
    (((alphaOf hQ hn hh x : orthGroup Q F) : GL (Fin n) F)⁻¹).val *ᵥ x.1 = h := by
  rw [← alphaOf_mulVec hQ hn hh x, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem phiIdeal_latOf {Λ : Lat F n} {b : Submodule (𝓞 F) F} (x : solSetLat Q Λ (Q.eval h) b) :
    phiIdeal Q.toQuadraticForm h (latOf hQ hn hh x).1 = b := by
  have := phiIdeal_image Q (alphaOf hQ hn hh x).2 h (latOf hQ hn hh x)
  rw [image_alpha_latOf, alphaOf_mulVec] at this
  rw [← this]; exact x.2.2

theorem latOf_mem_soGenus {L Λ : Lat F n} (hΛ : Λ ∈ soGenus Q L) {b : Submodule (𝓞 F) F}
    (x : solSetLat Q Λ (Q.eval h) b) : latOf hQ hn hh x ∈ soGenus Q L := by
  obtain ⟨ξ, hξ, rfl⟩ := hΛ
  refine ⟨diagF Q (alphaOf hQ hn hh x)⁻¹ * ξ,
    (soAf Q).mul_mem (diagF_mem_soAf Q ((soSub Q F).inv_mem (alphaOf_mem hQ hn hh x))) hξ, ?_⟩
  rw [mul_smul]
  change latSMul Q _ _ = _
  rw [diagF_smul]
  rfl

theorem latOf_mem_hGenus (h92 : Cond92 Q) {L : Lat F n} (hL : IsGMaximal Q L)
    {Λ : Lat F n} (hΛ : Λ ∈ hGenus Q h L)
    (x : solSetLat Q Λ (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) :
    latOf hQ hn hh x ∈ hGenus Q h L :=
  mem_hGenus_of_phiIdeal Q hQ hn h92 hL hh
    (latOf_mem_soGenus hQ hn hh (hGenus_subset_soGenus Q h L hΛ) x) (phiIdeal_latOf hQ hn hh x)

/-- **Step 2** (`rel_iff`): $M_y = \varepsilon M_x$ for some $\varepsilon \in H$ iff $\gamma\Lambda_1 = \Lambda_2$
and $\gamma x = y$ for some $\gamma \in G$. -/
theorem rel_iff {Λ₁ Λ₂ : Lat F n} {b₁ b₂ : Submodule (𝓞 F) F} (x : solSetLat Q Λ₁ (Q.eval h) b₁)
    (y : solSetLat Q Λ₂ (Q.eval h) b₂) :
    (∃ ε ∈ hRat Q h, latOf hQ hn hh y = Lat.image (ε : GL (Fin n) F) (latOf hQ hn hh x)) ↔
      ∃ γ : orthGroup Q F, γ ∈ soSub Q F ∧ Lat.image (γ : GL (Fin n) F) Λ₁ = Λ₂ ∧
        (γ : GL (Fin n) F).val *ᵥ x.1 = y.1 := by
  constructor
  · rintro ⟨ε, hε, hεM⟩
    refine ⟨(alphaOf hQ hn hh y) * ε * (alphaOf hQ hn hh x)⁻¹, (soSub Q F).mul_mem ((soSub Q F).mul_mem (alphaOf_mem hQ hn hh y) hε.1)
      ((soSub Q F).inv_mem (alphaOf_mem hQ hn hh x)), ?_, ?_⟩
    · have e : Lat.image (((alphaOf hQ hn hh y) * ε * (alphaOf hQ hn hh x)⁻¹ : orthGroup Q F) : GL (Fin n) F) Λ₁ =
          Lat.image ((alphaOf hQ hn hh y : orthGroup Q F) : GL (Fin n) F)
            (Lat.image (ε : GL (Fin n) F) (latOf hQ hn hh x)) := by
        rw [latOf, image_image, image_image]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
      rw [e, ← hεM, image_alpha_latOf]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, ← mulVec_mulVec]
      rw [alpha_inv_mulVec hQ hn hh x, show (ε : GL (Fin n) F).val *ᵥ h = h from hε.2,
        alphaOf_mulVec hQ hn hh y]
  · rintro ⟨γ, hγ, hγΛ, hγx⟩
    refine ⟨(alphaOf hQ hn hh y)⁻¹ * γ * (alphaOf hQ hn hh x), ⟨(soSub Q F).mul_mem ((soSub Q F).mul_mem
      ((soSub Q F).inv_mem (alphaOf_mem hQ hn hh y)) hγ) (alphaOf_mem hQ hn hh x), ?_⟩, ?_⟩
    · change (((alphaOf hQ hn hh y)⁻¹ * γ * (alphaOf hQ hn hh x) : orthGroup Q F) : GL (Fin n) F).val *ᵥ h = h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, ← mulVec_mulVec]
      rw [alphaOf_mulVec hQ hn hh x, hγx, alpha_inv_mulVec hQ hn hh y]
    · have e : Lat.image (((alphaOf hQ hn hh y)⁻¹ * γ * (alphaOf hQ hn hh x) : orthGroup Q F) : GL (Fin n) F)
          (latOf hQ hn hh x) =
          Lat.image ((alphaOf hQ hn hh y : orthGroup Q F) : GL (Fin n) F)⁻¹ (Lat.image (γ : GL (Fin n) F) Λ₁) := by
        rw [latOf, image_image, image_image]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel, mul_one]
      rw [e, hγΛ]
      rfl

end LatOf

/-! ### Step 2: the double cosets and orbits of $H$ in terms of lattices -/

section Cosets

variable {Q} {h : Fin n → F} {L : Lat F n}

/-- The basic equivalence: $\eta_2 \in H\eta_1 D$ iff $\eta_2 L = \varepsilon\,\eta_1 L$ for some
$\varepsilon \in H$. -/
theorem coset_rel_iff (η₁ η₂ : hAf Q h) :
    (∃ e ∈ hInAf Q h, (e * η₁)⁻¹ * η₂ ∈ hStabAf Q h L) ↔
      ∃ ε ∈ hRat Q h, (η₂ : OAf Q) • L = Lat.image (ε : GL (Fin n) F) ((η₁ : OAf Q) • L) := by
  constructor
  · rintro ⟨e, he, hd⟩
    obtain ⟨ε, hε, hεe⟩ := (Subgroup.mem_subgroupOf.1 he)
    refine ⟨ε, hε, ?_⟩
    have hL : ((((e * η₁)⁻¹ * η₂ : hAf Q h)) : OAf Q) • L = L := by
      have h1 := (Subgroup.mem_subgroupOf.1 hd).2
      have : (((e * η₁)⁻¹ * η₂ : hAf Q h) : OAf Q) ∈ MulAction.stabilizer (OAf Q) L := by
        rw [stabilizer_eq_locStab]; exact h1
      exact this
    rw [← diagF_smul]
    change _ = diagF Q ε • (η₁ : OAf Q) • L
    rw [hεe, ← mul_smul]
    have : ((η₂ : hAf Q h) : OAf Q) = ((e * η₁ : hAf Q h) : OAf Q) * (((e * η₁)⁻¹ * η₂ : hAf Q h) : OAf Q) := by
      rw [← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [this, mul_smul, hL]
    rfl
  · rintro ⟨ε, hε, hη⟩
    refine ⟨⟨diagF Q ε, diagF_mem_hAf Q h hε⟩, Subgroup.mem_subgroupOf.2 ⟨ε, hε, rfl⟩, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, ?_⟩
    · exact (hAf_le_soAf Q h) (((⟨diagF Q ε, diagF_mem_hAf Q h hε⟩ * η₁)⁻¹ * η₂ : hAf Q h)).2
    · have : (((⟨diagF Q ε, diagF_mem_hAf Q h hε⟩ * η₁)⁻¹ * η₂ : hAf Q h) : OAf Q) ∈
          MulAction.stabilizer (OAf Q) L := by
        rw [MulAction.mem_stabilizer_iff]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, mul_smul]
        rw [hη, ← diagF_smul]
        change (η₁ : OAf Q)⁻¹ • (diagF Q ε)⁻¹ • diagF Q ε • (η₁ : OAf Q) • L = L
        rw [inv_smul_smul, inv_smul_smul]
      rw [stabilizer_eq_locStab] at this
      exact this

/-- $\eta_2 D$ is in the $H$-orbit of $\eta_1 D$ iff $\eta_2 L = \varepsilon\,\eta_1 L$, $\varepsilon \in H$. -/
theorem mk_mem_orbit_iff (η₁ η₂ : hAf Q h) :
    (QuotientGroup.mk η₂ : hAf Q h ⧸ hStabAf Q h L) ∈ orbit (hInAf Q h) (QuotientGroup.mk η₁) ↔
      ∃ ε ∈ hRat Q h, (η₂ : OAf Q) • L = Lat.image (ε : GL (Fin n) F) ((η₁ : OAf Q) • L) := by
  rw [← coset_rel_iff]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, e.2, ?_⟩
    have : (QuotientGroup.mk ((e : hAf Q h) * η₁) : hAf Q h ⧸ hStabAf Q h L) = QuotientGroup.mk η₂ := he
    exact QuotientGroup.eq.1 this
  · rintro ⟨e, he, hd⟩
    exact ⟨⟨e, he⟩, QuotientGroup.eq.2 hd⟩

/-- Two elements of $H_{\mathbf h}$ give the same double coset $H\eta D$ iff $\eta_2 L = \varepsilon\,\eta_1 L$,
$\varepsilon \in H$. -/
theorem dc_mk_eq_iff (η₁ η₂ : hAf Q h) :
    (DoubleCoset.mk (hInAf Q h) (hStabAf Q h L) η₁ = DoubleCoset.mk (hInAf Q h) (hStabAf Q h L) η₂) ↔
      ∃ ε ∈ hRat Q h, (η₂ : OAf Q) • L = Lat.image (ε : GL (Fin n) F) ((η₁ : OAf Q) • L) := by
  rw [← coset_rel_iff, DoubleCoset.eq]
  constructor
  · rintro ⟨e, he, d, hd, rfl⟩
    refine ⟨e, he, ?_⟩
    simpa [mul_assoc] using hd
  · rintro ⟨e, he, hd⟩
    exact ⟨e, he, _, hd, by group⟩

/-- The stabilizer of $\eta D$ in $H$: $\varepsilon \in H$ fixes $\eta D$ iff $\varepsilon\,\eta L = \eta L$. -/
theorem smul_mk_eq_iff {ε : orthGroup Q F} (hε : ε ∈ hRat Q h) (η : hAf Q h) :
    ((⟨⟨diagF Q ε, diagF_mem_hAf Q h hε⟩, Subgroup.mem_subgroupOf.2 ⟨ε, hε, rfl⟩⟩ : hInAf Q h) •
        (QuotientGroup.mk η : hAf Q h ⧸ hStabAf Q h L) = QuotientGroup.mk η) ↔
      Lat.image (ε : GL (Fin n) F) ((η : OAf Q) • L) = (η : OAf Q) • L := by
  have e1 : ((⟨⟨diagF Q ε, diagF_mem_hAf Q h hε⟩, Subgroup.mem_subgroupOf.2 ⟨ε, hε, rfl⟩⟩ : hInAf Q h) •
      (QuotientGroup.mk η : hAf Q h ⧸ hStabAf Q h L)) =
      QuotientGroup.mk (⟨diagF Q ε, diagF_mem_hAf Q h hε⟩ * η) := rfl
  rw [e1, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨-, hst⟩
    have : ((((⟨diagF Q ε, diagF_mem_hAf Q h hε⟩ * η)⁻¹ * η : hAf Q h)) : OAf Q) ∈
        MulAction.stabilizer (OAf Q) L := by rw [stabilizer_eq_locStab]; exact hst
    rw [MulAction.mem_stabilizer_iff] at this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, mul_smul] at this
    have h2 : (diagF Q ε)⁻¹ • ((η : OAf Q) • L) = (η : OAf Q) • L := by
      have h3 := congrArg (fun M => (η : OAf Q) • M) this
      simp only [smul_inv_smul] at h3
      exact h3
    rw [← diagF_smul]
    change diagF Q ε • (η : OAf Q) • L = _
    rw [smul_eq_iff_eq_inv_smul]
    exact h2.symm
  · intro hfix
    refine ⟨(hAf_le_soAf Q h) (((⟨diagF Q ε, diagF_mem_hAf Q h hε⟩ * η)⁻¹ * η : hAf Q h)).2, ?_⟩
    have : ((((⟨diagF Q ε, diagF_mem_hAf Q h hε⟩ * η)⁻¹ * η : hAf Q h)) : OAf Q) ∈
        MulAction.stabilizer (OAf Q) L := by
      rw [MulAction.mem_stabilizer_iff]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, mul_smul]
      rw [← diagF_smul] at hfix
      change diagF Q ε • (η : OAf Q) • L = _ at hfix
      conv_lhs => rw [← hfix]
      rw [inv_smul_smul, inv_smul_smul]
    rw [stabilizer_eq_locStab] at this
    exact this

end Cosets

/-! ### Theorem 11.6 (i), (ii) -/

section Main

variable {Q} (hQ : Q.Nondegenerate) (hn : 2 < n) (h92 : Cond92 Q) {L : Lat F n}
  (hL : IsGMaximal Q L) {h : Fin n → F} (hh : Q.eval h ≠ 0)

include h92 hL in
theorem exists_etaOf {Λ : Lat F n} (hΛ : Λ ∈ hGenus Q h L)
    (x : solSetLat Q Λ (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) :
    ∃ η : hAf Q h, (η : OAf Q) • L = latOf hQ hn hh x := by
  obtain ⟨η, hη, he⟩ := latOf_mem_hGenus hQ hn hh h92 hL hΛ x
  exact ⟨⟨η, hη⟩, he⟩

/-- $\eta_x \in H_{\mathbf h}$ with $\eta_x L = M_x$. -/
def etaOf {Λ : Lat F n} (hΛ : Λ ∈ hGenus Q h L)
    (x : solSetLat Q Λ (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) : hAf Q h :=
  (exists_etaOf hQ hn h92 hL hh hΛ x).choose

theorem etaOf_smul {Λ : Lat F n} (hΛ : Λ ∈ hGenus Q h L)
    (x : solSetLat Q Λ (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) :
    (etaOf hQ hn h92 hL hh hΛ x : OAf Q) • L = latOf hQ hn hh x :=
  (exists_etaOf hQ hn h92 hL hh hΛ x).choose_spec

/-- The orbit relation of $H$ on the classes $\eta_x D$, in terms of the solutions. -/
theorem etaOf_orbit_iff {Λ₁ Λ₂ : Lat F n} (hΛ₁ : Λ₁ ∈ hGenus Q h L) (hΛ₂ : Λ₂ ∈ hGenus Q h L)
    (x : solSetLat Q Λ₁ (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1))
    (y : solSetLat Q Λ₂ (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) :
    (QuotientGroup.mk (etaOf hQ hn h92 hL hh hΛ₂ y) : hAf Q h ⧸ hStabAf Q h L) ∈
        orbit (hInAf Q h) (QuotientGroup.mk (etaOf hQ hn h92 hL hh hΛ₁ x)) ↔
      ∃ γ : orthGroup Q F, γ ∈ soSub Q F ∧ Lat.image (γ : GL (Fin n) F) Λ₁ = Λ₂ ∧
        (γ : GL (Fin n) F).val *ᵥ x.1 = y.1 := by
  rw [mk_mem_orbit_iff, etaOf_smul, etaOf_smul]
  exact rel_iff hQ hn hh x y

/-- **Theorem 11.6 (ii)** for one solution: the stabilizer of $x$ in $\Gamma(\Lambda)$ and the stabilizer
$H\cap\eta_xC\eta_x^{-1}$ of $\eta_xD$ in $H$ have the same order ($\gamma \mapsto \alpha_x^{-1}\gamma\alpha_x$). -/
theorem card_stabilizer_eq {Λ : Lat F n} (hΛ : Λ ∈ hGenus Q h L)
    (x : solSetLat Q Λ (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) :
    Nat.card (stabilizer (gammaLat Q Λ) x) =
      Nat.card (stabilizer (hInAf Q h)
        (QuotientGroup.mk (etaOf hQ hn h92 hL hh hΛ x) : hAf Q h ⧸ hStabAf Q h L)) := by
  set α := alphaOf hQ hn hh x with hαdef
  set M := latOf hQ hn hh x with hMdef
  have hαx : (α : GL (Fin n) F).val *ᵥ h = x.1 := alphaOf_mulVec hQ hn hh x
  have hαinv : ((α : GL (Fin n) F)⁻¹).val *ᵥ x.1 = h := alpha_inv_mulVec hQ hn hh x
  have hαM : Lat.image (α : GL (Fin n) F) M = Λ := image_alpha_latOf hQ hn hh x
  have hMα : Lat.image ((α : GL (Fin n) F)⁻¹) Λ = M := rfl
  have hαso : α ∈ soSub Q F := alphaOf_mem hQ hn hh x
  let T := {ε : orthGroup Q F // ε ∈ hRat Q h ∧ Lat.image (ε : GL (Fin n) F) M = M}
  -- the stabilizer of `x` in `Γ(Λ)` is `T`
  have hfix : ∀ γ : stabilizer (gammaLat Q Λ) x,
      ((γ.1.1 : orthGroup Q F) : GL (Fin n) F).val *ᵥ x.1 = x.1 := fun γ =>
    congrArg Subtype.val (mem_stabilizer_iff.1 γ.2)
  have hstabΛ : ∀ γ : stabilizer (gammaLat Q Λ) x, Lat.image ((γ.1.1 : orthGroup Q F) : GL (Fin n) F) Λ = Λ :=
    fun γ => Lattices.Lat.ext γ.1.2.2
  let f1 : stabilizer (gammaLat Q Λ) x → T := fun γ => ⟨α⁻¹ * γ.1.1 * α, ⟨(soSub Q F).mul_mem
    ((soSub Q F).mul_mem ((soSub Q F).inv_mem hαso) γ.1.2.1) hαso, by
      change ((α⁻¹ * γ.1.1 * α : orthGroup Q F) : GL (Fin n) F).val *ᵥ h = h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, ← mulVec_mulVec]
      rw [hαx, hfix γ, hαinv]⟩, by
    rw [← hMα, image_image, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel,
      mul_one, ← image_image, hstabΛ γ]⟩
  have hf1 : Function.Bijective f1 := by
    constructor
    · intro γ δ hγδ
      have := congrArg (fun t : T => α * t.1 * α⁻¹) hγδ
      simp only [f1, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] at this
      exact Subtype.ext (Subtype.ext this)
    · intro ε
      have hmem : α * ε.1 * α⁻¹ ∈ gammaLat Q Λ := ⟨(soSub Q F).mul_mem ((soSub Q F).mul_mem hαso ε.2.1.1)
        ((soSub Q F).inv_mem hαso), by
          change glImage _ Λ.1 = Λ.1
          have : Lat.image (((α * ε.1 * α⁻¹ : orthGroup Q F)) : GL (Fin n) F) Λ = Λ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rw [← image_image, ← image_image, hMα, ε.2.2, hαM]
          exact congrArg Subtype.val this⟩
      refine ⟨⟨⟨α * ε.1 * α⁻¹, hmem⟩, ?_⟩, ?_⟩
      · rw [mem_stabilizer_iff]
        apply Subtype.ext
        change ((α * ε.1 * α⁻¹ : orthGroup Q F) : GL (Fin n) F).val *ᵥ x.1 = x.1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, ← mulVec_mulVec]
        rw [hαinv, show ((ε.1 : orthGroup Q F) : GL (Fin n) F).val *ᵥ h = h from ε.2.1.2, hαx]
      · apply Subtype.ext
        simp only [f1, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
  -- `T` is the stabilizer of `η_x D` in `H`
  have hηM : (etaOf hQ hn h92 hL hh hΛ x : OAf Q) • L = M := etaOf_smul hQ hn h92 hL hh hΛ x
  let f2 : T → stabilizer (hInAf Q h)
      (QuotientGroup.mk (etaOf hQ hn h92 hL hh hΛ x) : hAf Q h ⧸ hStabAf Q h L) := fun ε =>
    ⟨⟨⟨diagF Q ε.1, diagF_mem_hAf Q h ε.2.1⟩, Subgroup.mem_subgroupOf.2 ⟨ε.1, ε.2.1, rfl⟩⟩, by
      exact mem_stabilizer_iff.2 ((smul_mk_eq_iff (L := L) ε.2.1 _).2 (by rw [hηM]; exact ε.2.2))⟩
  have hf2 : Function.Bijective f2 := by
    constructor
    · intro ε δ hεδ
      have := congrArg (fun t => ((t.1.1 : hAf Q h) : OAf Q)) hεδ
      exact Subtype.ext (diagF_injective Q this)
    · intro t
      obtain ⟨ε, hε, hεe⟩ := Subgroup.mem_subgroupOf.1 t.1.2
      have ht : t.1 = ⟨⟨diagF Q ε, diagF_mem_hAf Q h hε⟩, Subgroup.mem_subgroupOf.2 ⟨ε, hε, rfl⟩⟩ :=
        Subtype.ext (Subtype.ext hεe.symm)
      have h2 : t.1 • (QuotientGroup.mk (etaOf hQ hn h92 hL hh hΛ x) : hAf Q h ⧸ hStabAf Q h L) =
          QuotientGroup.mk (etaOf hQ hn h92 hL hh hΛ x) := mem_stabilizer_iff.1 t.2
      rw [ht] at h2
      have h3 := (smul_mk_eq_iff (L := L) hε _).1 h2
      rw [hηM] at h3
      exact ⟨⟨ε, hε, h3⟩, Subtype.ext ht.symm⟩
  exact Nat.card_congr ((Equiv.ofBijective f1 hf1).trans (Equiv.ofBijective f2 hf2))

end Main

theorem ne_zero_of_eval {h : Fin n → F} (hh : Q.eval h ≠ 0) : h ≠ 0 := by
  rintro rfl
  exact hh (by simp [QuadForm.evalIn])

/-! ### The covering family -/

section Cover

variable {Q} (hQ : Q.Nondegenerate) (hn : 2 < n) (h92 : Cond92 Q) {L : Lat F n}
  (hL : IsGMaximal Q L) {h : Fin n → F} (hh : Q.eval h ≠ 0) {I : Type} {Ls : I → Lat F n}
  (hcov : IsHGenusCover Q h L Ls)

include hcov in
/-- **Surjectivity** (Shimura 2004, proof of Theorem 11.6 (i)): for every $\eta \in H_{\mathbf h}$ there are $i$
and $x \in L_i[q, \mathfrak b]$ with $M_x = \varepsilon\,\eta L$, $\varepsilon \in H$. -/
theorem exists_sol_of_hAf (η : hAf Q h) :
    ∃ (i : I) (x : solSetLat Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)),
      ∃ ε ∈ hRat Q h, latOf hQ hn hh x = Lat.image (ε : GL (Fin n) F) ((η : OAf Q) • L) := by
  have hM : (η : OAf Q) • L ∈ hGenus Q h L := ⟨η.1, η.2, rfl⟩
  obtain ⟨i, γ, hγ, hγM⟩ := hcov.cover _ hM
  have hx : ((γ : GL (Fin n) F)⁻¹).val *ᵥ h ∈ solSetLat Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1) := by
    refine ⟨?_, ?_⟩
    · change Q.toQuadraticForm _ = _
      rw [toQuadraticForm_mulVec_of_mem Q ((orthGroup Q F).inv_mem γ.2), QuadForm.toQuadraticForm_apply]
    · change phiIdeal _ _ (Ls i).1 = _
      have := phiIdeal_image Q γ.2 (((γ : GL (Fin n) F)⁻¹).val *ᵥ h) (Ls i)
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, hγM] at this
      rw [← this]
      exact phiIdeal_eq_of_mem_hGenus Q hQ (ne_zero_of_eval Q hh) hM
  let x : solSetLat Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1) := ⟨_, hx⟩
  refine ⟨i, x, (alphaOf hQ hn hh x)⁻¹ * γ⁻¹, ⟨(soSub Q F).mul_mem ((soSub Q F).inv_mem (alphaOf_mem hQ hn hh x))
    ((soSub Q F).inv_mem hγ), ?_⟩, ?_⟩
  · change (((alphaOf hQ hn hh x)⁻¹ * γ⁻¹ : orthGroup Q F) : GL (Fin n) F).val *ᵥ h = h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, ← mulVec_mulVec]
    exact alpha_inv_mulVec hQ hn hh x
  · rw [← hγM, image_image, latOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel, mul_one]

end Cover

/-! ### Theorem 11.6 (i), (ii), (v) -/

/-- **Theorem 11.6 (i), (ii)** (Shimura 2004, p. 104), unconditional (Theorem 10.5 is
proved, `localTheorem10_5_holds`)
(Theorem 10.5): the proposition `Theorem11_6_ii`. -/
@[kb "shimura2004" "Thm. 11.6 (i), (ii), p. 104 (from Theorem 10.5)"]
theorem theorem11_6_ii_holds : Theorem11_6_ii := by
  intro F _ _ n Q hQ hn h92 L hL h hh b I Ls hcov
  refine ⟨finite_of_isHGenusCover Q hQ hcov,
    fun i x => QuotientGroup.mk (etaOf hQ hn h92 hL hh (hcov.mem i) x), ?_, ?_, ?_, ?_⟩
  · intro i x y
    rw [etaOf_orbit_iff]
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨γ.1, γ.2.1, Lattices.Lat.ext γ.2.2, rfl⟩
    · rintro ⟨γ, hγ, hγΛ, hγx⟩
      exact ⟨⟨γ, hγ, congrArg Subtype.val hγΛ⟩, Subtype.ext hγx⟩
  · intro i j x y hxy
    rw [etaOf_orbit_iff] at hxy
    obtain ⟨γ, hγ, hγΛ, -⟩ := hxy
    exact hcov.minimal i j ⟨γ, hγ, hγΛ⟩
  · intro z
    induction z using QuotientGroup.induction_on with | H η => ?_
    obtain ⟨i, x, ε, hε, hεx⟩ := exists_sol_of_hAf hQ hn hh hcov η
    refine ⟨i, x, ?_⟩
    rw [mk_mem_orbit_iff, etaOf_smul]
    exact ⟨ε, hε, hεx⟩
  · intro i x
    exact card_stabilizer_eq hQ hn h92 hL hh (hcov.mem i) x

/-- **(13.18)** (Shimura 2004, p. 134; Theorem 13.12 (13.17b) in the totally definite case), unconditional (Theorem 10.5 is
proved): the proposition `Formula13_18`. -/
@[kb "shimura2004" "(13.18), p. 134 (from Theorem 10.5)"]
theorem formula_13_18_holds : Formula13_18 :=
  formula_13_18 ⟨theorem11_6_ii_holds⟩

/-- **Theorem 11.6 (v)** (Shimura 2004, p. 104), unconditional (Theorem 10.5 is
proved, `localTheorem10_5_holds`)
(Theorem 10.5): the proposition `Theorem11_6_v`. -/
@[kb "shimura2004" "Thm. 11.6 (v), p. 104 (from Theorem 10.5)"]
theorem theorem11_6_v_holds : Theorem11_6_v := by
  intro F _ _ n Q hQ hn h92 L hL h hh b I Ls hcov Λ hΛ
  constructor
  · rintro ⟨x, hx⟩
    let x' : solSetLat Q Λ (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1) := ⟨x, hx⟩
    have hM := mem_hGenus_of_phiIdeal Q hQ hn h92 hL hh (latOf_mem_soGenus hQ hn hh hΛ x')
      (phiIdeal_latOf hQ hn hh x')
    obtain ⟨i, γ, hγ, hγM⟩ := hcov.cover _ hM
    refine ⟨i, alphaOf hQ hn hh x' * γ, (soSub Q F).mul_mem (alphaOf_mem hQ hn hh x') hγ, ?_⟩
    rw [Subgroup.coe_mul, ← image_image, hγM]
    exact image_alpha_latOf hQ hn hh x'
  · rintro ⟨i, γ, hγ, hγΛ⟩
    refine ⟨(γ : GL (Fin n) F).val *ᵥ h, ?_⟩
    rw [← hγΛ]
    apply mem_solSetLat_image Q γ.2
    refine ⟨by rw [QuadForm.toQuadraticForm_apply], ?_⟩
    exact phiIdeal_eq_of_mem_hGenus Q hQ (ne_zero_of_eval Q hh) (hcov.mem i)

/-! ### Theorem 11.6 (i) and (11.7) -/

theorem hClassRel_equivalence (h : Fin n → F) : Equivalence (HClassRel Q h) where
  refl M := ⟨1, (hRat Q h).one_mem, image_one M⟩
  symm := by
    rintro M N ⟨ε, hε, rfl⟩
    exact ⟨ε⁻¹, (hRat Q h).inv_mem hε, by rw [Subgroup.coe_inv, image_image, inv_mul_cancel, image_one]⟩
  trans := by
    rintro M N P ⟨ε, hε, rfl⟩ ⟨δ, hδ, rfl⟩
    exact ⟨δ * ε, (hRat Q h).mul_mem hδ hε, by rw [Subgroup.coe_mul, image_image]⟩

section Card

variable {Q} (hQ : Q.Nondegenerate) (hn : 2 < n) (h92 : Cond92 Q) {L : Lat F n}
  (hL : IsGMaximal Q L) {h : Fin n → F} (hh : Q.eval h ≠ 0) {I : Type} {Ls : I → Lat F n}
  (hcov : IsHGenusCover Q h L Ls)

theorem orbitRel_iff {i : I} (x y : solSetLat Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) :
    (∃ γ ∈ gammaLat Q (Ls i), (γ : GL (Fin n) F).val *ᵥ x.1 = y.1) ↔
      ∃ γ : orthGroup Q F, γ ∈ soSub Q F ∧ Lat.image (γ : GL (Fin n) F) (Ls i) = Ls i ∧
        (γ : GL (Fin n) F).val *ᵥ x.1 = y.1 := by
  constructor
  · rintro ⟨γ, hγ, hγx⟩; exact ⟨γ, hγ.1, Lattices.Lat.ext hγ.2, hγx⟩
  · rintro ⟨γ, hγ, hγΛ, hγx⟩; exact ⟨γ, ⟨hγ, congrArg Subtype.val hγΛ⟩, hγx⟩

/-- Shimura's map $\bigsqcup_i L_i[q,\mathfrak b]/\Gamma(L_i) \to H\backslash H_{\mathbf h}/D$,
$x \mapsto H\eta_xD$. -/
def toDC : (Σ i, solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) → hDoubleCosets Q h L := fun p =>
  Quot.lift (fun x => DoubleCoset.mk (hInAf Q h) (hStabAf Q h L) (etaOf hQ hn h92 hL hh (hcov.mem p.1) x)) (by
    intro x y hxy
    refine (dc_mk_eq_iff _ _).2 ?_
    rw [etaOf_smul, etaOf_smul, rel_iff]
    exact (orbitRel_iff x y).1 hxy) p.2

theorem toDC_bijective : Function.Bijective (toDC hQ hn h92 hL hh hcov) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    induction x using Quot.ind with | mk x => ?_
    induction y using Quot.ind with | mk y => ?_
    have h1 : DoubleCoset.mk (hInAf Q h) (hStabAf Q h L) (etaOf hQ hn h92 hL hh (hcov.mem i) x) =
        DoubleCoset.mk (hInAf Q h) (hStabAf Q h L) (etaOf hQ hn h92 hL hh (hcov.mem j) y) := hxy
    rw [dc_mk_eq_iff, etaOf_smul, etaOf_smul, rel_iff] at h1
    obtain ⟨γ, hγ, hγΛ, hγx⟩ := h1
    obtain rfl := hcov.minimal i j ⟨γ, hγ, hγΛ⟩
    have : (Quot.mk _ x : solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) = Quot.mk _ y :=
      Quot.sound ((orbitRel_iff x y).2 ⟨γ, hγ, hγΛ, hγx⟩)
    rw [this]
  · intro z
    obtain ⟨η, rfl⟩ := Quotient.exists_rep z
    obtain ⟨i, x, ε, hε, hεx⟩ := exists_sol_of_hAf hQ hn hh hcov η
    refine ⟨⟨i, Quot.mk _ x⟩, ?_⟩
    change DoubleCoset.mk (hInAf Q h) (hStabAf Q h L) (etaOf hQ hn h92 hL hh (hcov.mem i) x) =
      DoubleCoset.mk (hInAf Q h) (hStabAf Q h L) η
    symm
    rw [dc_mk_eq_iff, etaOf_smul]
    exact ⟨ε, hε, hεx⟩

/-- Shimura's bijection $\bigsqcup_i L_i[q,\mathfrak b]/\Gamma(L_i) \to \{H\text{-classes in the }
H\text{-genus of } L\}$, $x \mapsto$ the $H$-class of $M_x = \alpha_x^{-1}L_i$. -/
def toHClass : (Σ i, solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) → hClassesInHGenus Q h L := fun p =>
  Quot.lift (fun x => Quot.mk _ ⟨latOf hQ hn hh x, latOf_mem_hGenus hQ hn hh h92 hL (hcov.mem p.1) x⟩) (by
    intro x y hxy
    apply Quot.sound
    obtain ⟨ε, hε, hεe⟩ := (rel_iff hQ hn hh x y).2 ((orbitRel_iff x y).1 hxy)
    exact ⟨ε, hε, hεe.symm⟩) p.2

theorem toHClass_bijective : Function.Bijective (toHClass hQ hn h92 hL hh hcov) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    induction x using Quot.ind with | mk x => ?_
    induction y using Quot.ind with | mk y => ?_
    have h1 := Quot.eqvGen_exact hxy
    rw [Equivalence.eqvGen_iff ((hClassRel_equivalence Q h).comap Subtype.val)] at h1
    obtain ⟨ε, hε, hεe⟩ := h1
    obtain ⟨γ, hγ, hγΛ, hγx⟩ := (rel_iff hQ hn hh x y).1 ⟨ε, hε, hεe.symm⟩
    obtain rfl := hcov.minimal i j ⟨γ, hγ, hγΛ⟩
    have : (Quot.mk _ x : solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) = Quot.mk _ y :=
      Quot.sound ((orbitRel_iff x y).2 ⟨γ, hγ, hγΛ, hγx⟩)
    rw [this]
  · intro z
    induction z using Quot.ind with | mk M => ?_
    obtain ⟨η, hη, hηM⟩ := M.2
    obtain ⟨i, x, ε, hε, hεx⟩ := exists_sol_of_hAf hQ hn hh hcov ⟨η, hη⟩
    refine ⟨⟨i, Quot.mk _ x⟩, ?_⟩
    apply Quot.sound
    refine ⟨ε⁻¹, (hRat Q h).inv_mem hε, ?_⟩
    change Lat.image _ (latOf hQ hn hh x) = M.1
    rw [hεx, Subgroup.coe_inv, image_image, inv_mul_cancel, image_one]
    exact hηM

include hQ hn h92 hL hh hcov in
/-- **Theorem 11.6 (i) and (11.7)**, given that each $L_i[q,\mathfrak b]/\Gamma(L_i)$ is finite. -/
theorem theorem11_6_i_of_finite (hfin : ∀ i, Finite (solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1))) :
    Finite I ∧ (∀ i, Finite (solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1))) ∧
      Nonempty ((Σ i, solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) ≃ hClassesInHGenus Q h L) ∧
      Nat.card (hDoubleCosets Q h L) = ∑ᶠ i, Nat.card (solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) := by
  have hI : Finite I := finite_of_isHGenusCover Q hQ hcov
  refine ⟨hI, hfin, ⟨Equiv.ofBijective _ (toHClass_bijective hQ hn h92 hL hh hcov)⟩, ?_⟩
  have : Fintype I := Fintype.ofFinite I
  rw [← Nat.card_congr (Equiv.ofBijective _ (toDC_bijective hQ hn h92 hL hh hcov)), Nat.card_sigma,
    finsum_eq_sum_of_fintype]

include hQ hn h92 hL hh hcov in
/-- Each $L_i[q,\mathfrak b]/\Gamma(L_i)$ embeds in $H\backslash H_{\mathbf h}/D$. -/
theorem finite_solOrbits_of_finite_dc [Finite (hDoubleCosets Q h L)] (i : I) :
    Finite (solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) :=
  Finite.of_injective (fun x => toDC hQ hn h92 hL hh hcov ⟨i, x⟩) fun x y hxy =>
    eq_of_heq (Sigma.mk.inj_iff.1 ((toDC_bijective hQ hn h92 hL hh hcov).1 hxy)).2

end Card

/-- **Cited input: finiteness of $H\backslash H_{\mathbb A}/(H_{\mathbb A}\cap C)$** (the finiteness of class
numbers of $H = SO^\varphi(W)$ relative to an open compact subgroup, used by Shimura for the finiteness assertions
of Theorem 11.6 (i); for indefinite $\varphi$ it rests on reduction theory). Not proved here; for totally positive
definite $\varphi$ it is not needed (`theorem11_6_i_definite`). -/
@[kb "shimura2004" "Thm. 11.6 (i), p. 104 (finiteness of H\\H_𝔸/(H_𝔸 ∩ C), as an input)"]
structure HClassNumberFinite : Prop where
  finite : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate → 2 < n →
    ∀ (L : Lat F n) (h : Fin n → F), Q.eval h ≠ 0 → Finite (hDoubleCosets Q h L)

/-- **Theorem 11.6 (i) and (11.7)** (Shimura 2004, p. 104), *conditional on the named input*
`HClassNumberFinite` (finiteness of the class number of $H$): the proposition
`Theorem11_6_i`. -/
@[kb "shimura2004" "Thm. 11.6 (i) and (11.7), p. 104 (from Theorem 10.5 and the finiteness of class numbers)"]
theorem theorem11_6_i_holds (hfin : HClassNumberFinite) : Theorem11_6_i := by
  intro F _ _ n Q hQ hn h92 L hL h hh b I Ls hcov
  have := hfin.finite F n Q hQ hn L h hh
  exact theorem11_6_i_of_finite hQ hn h92 hL hh hcov
    (finite_solOrbits_of_finite_dc hQ hn h92 hL hh hcov)

/-- The old input `FundamentalTheorem11_6` holds, conditional on `HClassNumberFinite` (proved:
`fundamentalTheorem11_6_of_local`). -/
theorem fundamentalTheorem11_6_holds (hfin : HClassNumberFinite) :
    FundamentalTheorem11_6 :=
  ⟨theorem11_6_i_holds hfin⟩

/-- **Theorem 11.6 (i) and (11.7) for totally positive definite $\varphi$** (Shimura 2004, p. 104), unconditional
(Theorem 10.5 is proved): the conclusion of `Theorem11_6_i` when $F$ is totally real and $\varphi$
totally positive definite (the solution sets are then finite, `finite_solSetLat`). -/
@[kb "shimura2004" "Thm. 11.6 (i) and (11.7), p. 104 (totally definite case, from Theorem 10.5)"]
theorem theorem11_6_i_definite {F : Type} [Field F] [NumberField F] {n : ℕ}
    {Q : QuadForm F n} (hQ : Q.Nondegenerate) (hpd : IsTotallyPosDef Q) (hn : 2 < n) (h92 : Cond92 Q)
    {L : Lat F n} (hL : IsGMaximal Q L) {h : Fin n → F} (hh : Q.eval h ≠ 0) {I : Type} {Ls : I → Lat F n}
    (hcov : IsHGenusCover Q h L Ls) :
    Finite I ∧ (∀ i, Finite (solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1))) ∧
      Nonempty ((Σ i, solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) ≃
        hClassesInHGenus Q h L) ∧
      Nat.card (hDoubleCosets Q h L) =
        ∑ᶠ i, Nat.card (solOrbits Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) := by
  refine theorem11_6_i_of_finite hQ hn h92 hL hh hcov fun i => ?_
  have : Finite (solSetLat Q (Ls i) (Q.eval h) (phiIdeal Q.toQuadraticForm h L.1)) :=
    (finite_solSetLat hpd (Ls i) _ _).to_subtype
  exact Finite.of_surjective (Quot.mk _) (fun z => Quot.exists_rep z)

theorem sosQ_eval (n : ℕ) (x : Fin n → ℚ) : (sosQ n).eval x = ∑ i, x i ^ 2 := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- The sum of $n$ squares is totally positive definite. -/
theorem sosQ_totallyPosDef (n : ℕ) : IsTotallyPosDef (sosQ n) := by
  intro x hx σ
  have hσ : σ ((sosQ n).eval x) = (((sosQ n).eval x : ℚ) : ℂ) := by
    have := σ.commutes ((sosQ n).eval x)
    simpa using this
  rw [hσ]
  have hpos : 0 < (sosQ n).eval x := by
    rw [sosQ_eval]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    have hi' : x i ≠ 0 := hi
    exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi')))
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i))
  have h2 := Complex.zero_lt_real.2 (show (0 : ℝ) < ((sosQ n).eval x : ℝ) by exact_mod_cast hpos)
  simpa using h2

/-- **Theorem 12.14 (iv)** (Shimura 2004, p. 123), *conditional on the named input*
`SumSquaresOneClass` (one class in the genus, [S02a, Lemma 1.6]): the proposition
`Theorem12_14_iv`. Shimura's argument: the genus is one class, so $\{L_i\} = \{L\}$ in (11.7). -/
@[kb "shimura2004" "Thm. 12.14 (iv), p. 123 (from Theorem 10.5 and one class in the genus)"]
theorem theorem_12_14_iv_of_local (h1 : SumSquaresOneClass) : Theorem12_14_iv := by
  intro n hn L hL h hpos hh
  have hb : (letI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
      phiIdeal (sosQ n).toQuadraticForm h L.1) = 1 := hh.2
  have hcov : IsHGenusCover (sosQ n) h L (fun _ : Unit => L) :=
    { mem := fun _ => mem_hGenus_self _ h L
      cover := fun M hM => ⟨(), h1.one_class n hn L hL M (hGenus_subset_soGenus _ h L hM)⟩
      minimal := fun _ _ _ => rfl }
  have hn2 : 2 < n := by simp at hn; omega
  obtain ⟨-, hfin, -, hcard⟩ := theorem11_6_i_definite (sosQ_nondegenerate n) (sosQ_totallyPosDef n) hn2
    (sosQ_cond92 n) hL hpos.ne' hcov
  simp only [hb] at hfin hcard
  refine ⟨hfin (), ?_⟩
  rw [hcard, finsum_unique]

end QuadFormsKB.Shimura2004
