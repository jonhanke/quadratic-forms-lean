/-
# Hanke, AWS 2009 notes, Ch. 4: the group theory behind the adelic constructions

J. Hanke, *Quadratic Forms and Automorphic Forms* (2009 Arizona Winter School notes,
arXiv:1105.5759 v3), bibkey `hanke2011aws`. Page numbers are the printed ones (they equal the PDF
page numbers). The list D1, D2, … of the notes' derivations is in `AWS/Overview.lean`.

This file isolates the **purely group-theoretic** content of §3.5, §4.2 and §4.5–§4.6. Everything
here is stated for an arbitrary group `G` (think $G = O(V_{\mathbb{A}})$ or $\mathrm{SL}_2(\mathbb{A})$)
acting on a set `X` (think: lattices in $V$), a subgroup `Γ` (the rational points $O(V)$, embedded
diagonally) and a subgroup `K` (an adelic stabilizer $\mathrm{Stab}_{\mathbb{A}}(L)$), and proved
without any hypotheses. The concrete adelic groups are in `AWS/Adelic.lean`.

Main results:
- `dosetEquivClasses` (D16, p. 62): $\Gamma\backslash G/\mathrm{Stab}_G(x) \simeq$ the $\Gamma$-orbits on
  the $G$-orbit of $x$ ("$O(V)\backslash O(V_\mathbb{A})/\mathrm{Stab}_\mathbb{A}(L) \leftrightarrow$
  classes in $\mathrm{Gen}(L)$").
- `card_stabilizer_smul` (used in (4.11)): $\mathrm{Aut}(\alpha L) = \Gamma \cap \alpha K \alpha^{-1}$.
- `mem_doset_mul_iff` (D19, (4.14)–(4.16)).
- `class_subset_spinorGenus`, `spinorGenus_subset_genus` (D16, §3.5).
- `IsAdelicAutomorphic`, `isAdelicAutomorphic_of_biInvariant` (D12, D17, §4.2 conditions 1–3, end of §4.5).
- `exists_unique_lift`, `lift_mul_right` (D11, §4.2, the adelic lift (4.2) via strong approximation).
-/
import Mathlib
import QuadFormsKB.Citation

open MulAction

namespace QuadFormsKB.AWS

variable {G X : Type*} [Group G] [MulAction G X]

/-! ### D16: double cosets and classes in the genus -/

/-- **The class relation on the genus** (abstractly). For a group $G$ acting on $X$, a subgroup
$\Gamma \le G$ and $x \in X$, two elements $y, y'$ of the orbit $G \cdot x$ ("the genus of $x$") are
related iff $\gamma \cdot y = y'$ for some $\gamma \in \Gamma$ ("they lie in the same class").

In the notes (p. 62) $G = O(V_\mathbb{A})$, $\Gamma = O(V)$, $X$ = the lattices in $(V,Q)$, and "two
lattices in $(V,Q)$ are in the same class if they are isometric, hence they differ by the action of
an element of $O(V)$". -/
def classSetoid (Γ : Subgroup G) (x : X) : Setoid (orbit G x) where
  r y y' := ∃ γ ∈ Γ, γ • (y : X) = y'
  iseqv := by
    refine ⟨fun y => ⟨1, Γ.one_mem, one_smul _ _⟩, ?_, ?_⟩
    · rintro y y' ⟨γ, hγ, h⟩
      exact ⟨γ⁻¹, Γ.inv_mem hγ, by rw [← h, inv_smul_smul]⟩
    · rintro y y' y'' ⟨γ, hγ, h⟩ ⟨δ, hδ, h'⟩
      exact ⟨δ * γ, Γ.mul_mem hδ hγ, by rw [mul_smul, h, h']⟩

/-- **The set of classes in the genus** of $x$: the quotient of the orbit $G \cdot x$ by the class
relation `classSetoid`. -/
abbrev ClassesInGenus (Γ : Subgroup G) (x : X) : Type _ := Quotient (classSetoid Γ x)

/-- The double coset $\Gamma g\, \mathrm{Stab}_G(x)$ determines the class of $g \cdot x$. -/
private theorem doset_rel_iff (Γ : Subgroup G) (x : X) (g g' : G) :
    DoubleCoset.setoid (Γ : Set G) (stabilizer G x) g g' ↔ ∃ γ ∈ Γ, γ • (g • x) = g' • x := by
  rw [DoubleCoset.rel_iff]
  constructor
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    exact ⟨γ, hγ, by rw [mul_smul, mul_smul, (mem_stabilizer_iff.mp hk), smul_smul]⟩
  · rintro ⟨γ, hγ, h⟩
    refine ⟨γ, hγ, (γ * g)⁻¹ * g', ?_, by group⟩
    rw [mem_stabilizer_iff, mul_smul, ← h, ← mul_smul γ g x, inv_smul_smul]

/-- **D16 (p. 62): double cosets $\leftrightarrow$ classes in the genus.** For a group $G$ acting on $X$,
a subgroup $\Gamma$ and $x \in X$, the map $\Gamma g\,\mathrm{Stab}_G(x) \mapsto [g \cdot x]$ is a
bijection
$$\Gamma \backslash G / \mathrm{Stab}_G(x) \;\xrightarrow{\ \sim\ }\; \{\Gamma\text{-orbits in } G\cdot x\}.$$
With $G = O(V_\mathbb{A})$, $\Gamma = O(V)$, $x = L$ and $G \cdot L = \mathrm{Gen}(L)$ (Lemma 4.5.2,
`AWS.orbit_eq_genus`) this is the notes' bijection
$O(V)\backslash O(V_\mathbb{A})/\mathrm{Stab}_\mathbb{A}(L) \leftrightarrow$ classes in $\mathrm{Gen}(L)$. -/
@[kb "hanke2011aws" "§4.5, p. 62"]
noncomputable def dosetEquivClasses (Γ : Subgroup G) (x : X) :
    DoubleCoset.Quotient (Γ : Set G) (stabilizer G x) ≃ ClassesInGenus Γ x :=
  Equiv.ofBijective
    (Quotient.lift (fun g => (⟦⟨g • x, mem_orbit x g⟩⟧ : ClassesInGenus Γ x)) (by
      intro g g' h
      exact Quotient.sound ((doset_rel_iff Γ x g g').mp h)))
    (by
      constructor
      · intro q q'
        induction q using Quotient.inductionOn
        induction q' using Quotient.inductionOn
        intro h
        exact Quotient.sound ((doset_rel_iff Γ x _ _).mpr (Quotient.exact h))
      · intro c
        induction c using Quotient.inductionOn with
        | h y =>
          obtain ⟨y, g, rfl⟩ := y
          exact ⟨⟦g⟧, rfl⟩)

@[simp] theorem dosetEquivClasses_mk (Γ : Subgroup G) (x : X) (g : G) :
    dosetEquivClasses Γ x (DoubleCoset.mk Γ (stabilizer G x) g) = ⟦⟨g • x, mem_orbit x g⟩⟧ := rfl

/-- **$G/\mathrm{Stab}_G(x) \simeq G\cdot x$** (p. 62, "$O(V_\mathbb{A})/\mathrm{Stab}_\mathbb{A}(L)
\leftrightarrow \mathrm{Gen}(L)$, $h_\mathbb{A} \mapsto h_\mathbb{A}L$"): the orbit–stabilizer
bijection, from Mathlib (`MulAction.orbitEquivQuotientStabilizer`). -/
@[kb "hanke2011aws" "§4.5, p. 62"]
noncomputable def quotientStabilizerEquivOrbit (x : X) : G ⧸ stabilizer G x ≃ orbit G x :=
  (orbitEquivQuotientStabilizer G x).symm

/-- **The conjugate subgroup** $\alpha K \alpha^{-1}$ of a subgroup $K \le G$. -/
abbrev conjSub (α : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj α).toMonoidHom

theorem mem_conjSub {α h : G} {K : Subgroup G} : h ∈ conjSub α K ↔ α⁻¹ * h * α ∈ K := by
  simp only [conjSub, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- **The stabilizer of a translate** (used for $K_{i,\mathbb{A}} = \alpha_i K_\mathbb{A}\alpha_i^{-1}$,
§4.6, p. 63): $\mathrm{Stab}_G(\alpha \cdot x) = \alpha\,\mathrm{Stab}_G(x)\,\alpha^{-1}$. -/
theorem stabilizer_smul (α : G) (x : X) : stabilizer G (α • x) = conjSub α (stabilizer G x) :=
  stabilizer_smul_eq_stabilizer_map_conj α x

/-- **The automorphism group of $\alpha \cdot x$** (used in (4.11), p. 64: "$O(V_F) \cap K_{i,\mathbb{A}}$
is the finite group of rational automorphisms $\mathrm{Aut}(L_i)$"). The rational stabilizer
$\Gamma \cap \mathrm{Stab}_G(\alpha x)$ equals $\Gamma \cap \alpha\,\mathrm{Stab}_G(x)\,\alpha^{-1}$, so the
two have the same cardinality. -/
@[kb "hanke2011aws" "§4.6, (4.11), p. 64"]
theorem card_stabilizer_smul (Γ : Subgroup G) (α : G) (x : X) :
    Nat.card (Γ ⊓ stabilizer G (α • x) : Subgroup G) =
      Nat.card (Γ ⊓ conjSub α (stabilizer G x) : Subgroup G) := by
  rw [stabilizer_smul]

/-! ### D19: (4.14)–(4.16) -/

/-- **D19, (4.14)–(4.16), p. 64.** Let $\alpha_i$ ($i \in I$) be representatives of distinct double
cosets $\Gamma \alpha_i K$. For $h \in K$:
$$\alpha_i h \in \Gamma \alpha_j K \iff \alpha_i \in \Gamma\alpha_j K \iff i = j.$$
(The notes write the last step as "$\alpha_i = \alpha_j$".) -/
@[kb "hanke2011aws" "§4.6, (4.14)-(4.16), p. 64"]
theorem mem_doset_mul_iff {ι : Type*} (Γ K : Subgroup G) (α : ι → G)
    (hα : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j) {h : G} (hh : h ∈ K) (i j : ι) :
    α i * h ∈ DoubleCoset.doubleCoset (α j) Γ K ↔ i = j := by
  constructor
  · intro hmem
    apply hα
    rw [DoubleCoset.eq]
    obtain ⟨γ, hγ, k, hk, e⟩ := DoubleCoset.mem_doubleCoset.mp hmem
    refine ⟨γ⁻¹, Γ.inv_mem hγ, h * k⁻¹, K.mul_mem hh (K.inv_mem hk), ?_⟩
    rw [show α j = γ⁻¹ * (γ * α j * k) * k⁻¹ by group, ← e]
    group
  · rintro rfl
    exact DoubleCoset.mem_doubleCoset.mpr ⟨1, Γ.one_mem, h, hh, by group⟩

/-! ### D8: class ⊆ spinor genus ⊆ genus (§3.5) -/

/-- **The class of $x$:** $\Gamma \cdot x$ (with $\Gamma = O(V)$: the lattices isometric to $L$ inside $V$). -/
def classOf (Γ : Subgroup G) (x : X) : Set X := {y | ∃ γ ∈ Γ, y = γ • x}

/-- **The spinor genus of $x$** (§3.5, p. 53), abstractly: $\mathrm{Spn}(x) = \Gamma\,\kappa \cdot x =
\{\sigma \cdot y : \sigma \in \Gamma,\ y \in \kappa \cdot x\}$, where $\kappa \le G$ plays the role of the
adelic spinor kernel $\prod_v \kappa(V_v)$ ("$L'$ is locally spinor equivalent to $L$ after performing a
global isometry (in $O(V)$)"). -/
def spinorGenus (Γ κ : Subgroup G) (x : X) : Set X := {y | ∃ γ ∈ Γ, ∃ k ∈ κ, y = γ • k • x}

/-- **§3.5, p. 53: the class is contained in the spinor genus** ("the local equivalence defining the
genus is weaker than the corresponding global equivalence defining classes"). -/
@[kb "hanke2011aws" "§3.5, p. 53"]
theorem class_subset_spinorGenus (Γ κ : Subgroup G) (x : X) : classOf Γ x ⊆ spinorGenus Γ κ x := by
  rintro y ⟨γ, hγ, rfl⟩
  exact ⟨γ, hγ, 1, κ.one_mem, by rw [one_smul]⟩

/-- **§3.5, p. 53: the spinor genus is contained in the genus** $G \cdot x$. -/
@[kb "hanke2011aws" "§3.5, p. 53"]
theorem spinorGenus_subset_genus (Γ κ : Subgroup G) (x : X) : spinorGenus Γ κ x ⊆ orbit G x := by
  rintro y ⟨γ, -, k, -, rfl⟩
  exact ⟨γ * k, by simp [mul_smul]⟩

/-! ### D12: adelic automorphic forms (§4.2, conditions 1–3) -/

/-- **Adelic automorphic form, conditions (1)–(3) of §4.2 (pp. 57–58)**, for a group `G`
($= G_\mathbb{A}$) with rational subgroup `Γ` ($= G(F)$), central subgroup `Z` ($= Z_\mathbb{A}$) and
subgroup `Kf` (the finite part of $K_\mathbb{A}$). A function $F : G \to \mathbb{C}$ is automorphic if

1. `left_inv`: $F(\gamma g) = F(g)$ for $\gamma \in \Gamma$;
2. `central`: there is a character $\psi : Z \to \mathbb{C}^\times$ with $F(zg) = \psi(z)F(g)$;
3. `kFinite`: the right translates $g \mapsto F(gk)$, $k \in K_f$, span a finite-dimensional
   **complex** vector space.

Conditions (4) (smoothness, $\mathfrak{z}_\infty$-finiteness) and (5) (moderate growth) are omitted:
as the notes say (p. 58), "in the case where $G$ is an orthogonal group of a definite quadratic form
conditions (4) and (5) can be safely omitted because the archimedean component is already compact".

*Erratum (candidate; pending author):* condition (3) says "finite-dimensional vector space over $F$"
and condition (4) "over $F_\infty$"; the functions are complex-valued, so both spans are over
$\mathbb{C}$. Condition (2) prints "$Z_\mathbb{A} : Z(\mathbb{A})$" for "$Z_\mathbb{A} := Z(\mathbb{A})$",
and (3) writes the translate as $F(g_\mathbb{A}\cdot k_f)$ while quantifying over $k_\mathbb{A}$. -/
@[kb "hanke2011aws" "§4.2, conditions (1)-(3), pp. 57-58"]
structure IsAdelicAutomorphic (Γ Z Kf : Subgroup G) (F : G → ℂ) : Prop where
  left_inv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g
  central : ∃ ψ : Z →* ℂˣ, ∀ z : Z, ∀ g, F (z * g) = (ψ z : ℂ) * F g
  kFinite : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kf => fun g => F (g * k)))

/-- **D17 (end of §4.5, p. 62): bi-invariant functions are automorphic.** If $F$ is left
$\Gamma$-invariant and right $K$-invariant, and the centre $Z$ lies in $K$ and is central, then $F$
satisfies conditions (1)–(3) with trivial central character, for any $K_f \le K$.

Applied to the characteristic functions $\Phi_{L_i}$ of the double cosets $O(V)\alpha_i K_\mathbb{A}$ and to
the constant function $1$ (`isAdelicAutomorphic_indicator_doset`), this is the notes' "both of
these functions are adelic automorphic forms in the sense of §4.2". (For $O(V)$ the centre is
$\{\pm 1\}$ at every place, which lies in every lattice stabilizer.) -/
@[kb "hanke2011aws" "§4.5, p. 62"]
theorem isAdelicAutomorphic_of_biInvariant (Γ Z K Kf : Subgroup G) (hKf : Kf ≤ K) (hZK : Z ≤ K)
    (hZ : ∀ z ∈ Z, ∀ g : G, z * g = g * z) (F : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g)
    (hr : ∀ k ∈ K, ∀ g, F (g * k) = F g) : IsAdelicAutomorphic Γ Z Kf F := by
  refine ⟨hl, ⟨1, fun z g => ?_⟩, ?_⟩
  · simp only [MonoidHom.one_apply, Units.val_one, one_mul]
    rw [hZ z z.2 g, hr z (hZK z.2)]
  · have : Set.range (fun k : Kf => fun g => F (g * k)) ⊆ {F} := by
      rintro _ ⟨k, rfl⟩
      exact funext fun g => hr k (hKf k.2) g
    have hle := Submodule.span_mono (R := ℂ) this
    exact Submodule.finiteDimensional_of_le hle

/-- **The characteristic function of a double coset** $\Gamma\alpha K$ (the notes' $\Phi_{L_i}$, p. 62),
with values in $\mathbb{C}$. -/
noncomputable def dosetIndicator (Γ K : Subgroup G) (α : G) : G → ℂ :=
  (DoubleCoset.doubleCoset α Γ K).indicator 1

theorem dosetIndicator_left (Γ K : Subgroup G) (α : G) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    dosetIndicator Γ K α (γ * g) = dosetIndicator Γ K α g := by
  unfold dosetIndicator
  by_cases h : g ∈ DoubleCoset.doubleCoset α Γ K
  · have h' : γ * g ∈ DoubleCoset.doubleCoset α Γ K := by
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp h
      exact DoubleCoset.mem_doubleCoset.mpr ⟨γ * a, Γ.mul_mem hγ ha, b, hb, by group⟩
    simp [h, h']
  · have h' : γ * g ∉ DoubleCoset.doubleCoset α Γ K := by
      intro h'
      obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.mp h'
      exact h (DoubleCoset.mem_doubleCoset.mpr ⟨γ⁻¹ * a, Γ.mul_mem (Γ.inv_mem hγ) ha, b, hb, by
        rw [mul_assoc, mul_assoc, ← mul_assoc a, ← e]; group⟩)
    simp [h, h']

theorem dosetIndicator_right (Γ K : Subgroup G) (α : G) {k : G} (hk : k ∈ K) (g : G) :
    dosetIndicator Γ K α (g * k) = dosetIndicator Γ K α g := by
  unfold dosetIndicator
  by_cases h : g ∈ DoubleCoset.doubleCoset α Γ K
  · have h' : g * k ∈ DoubleCoset.doubleCoset α Γ K := by
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp h
      exact DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b * k, K.mul_mem hb hk, by group⟩
    simp [h, h']
  · have h' : g * k ∉ DoubleCoset.doubleCoset α Γ K := by
      intro h'
      obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.mp h'
      exact h (DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), by
        rw [← mul_assoc, ← e]; group⟩)
    simp [h, h']

/-- **D17 for $\Phi_{L_i}$ and $1$ (p. 62).** The characteristic function of a double coset
$\Gamma\alpha K$, and the constant function $1$, are adelic automorphic forms (conditions (1)–(3))
whenever the centre $Z$ is central and contained in $K$. -/
@[kb "hanke2011aws" "§4.5, p. 62"]
theorem isAdelicAutomorphic_indicator_doset (Γ Z K Kf : Subgroup G) (hKf : Kf ≤ K) (hZK : Z ≤ K)
    (hZ : ∀ z ∈ Z, ∀ g : G, z * g = g * z) (α : G) :
    IsAdelicAutomorphic Γ Z Kf (dosetIndicator Γ K α) ∧ IsAdelicAutomorphic Γ Z Kf 1 :=
  ⟨isAdelicAutomorphic_of_biInvariant Γ Z K Kf hKf hZK hZ _
      (fun _ hγ g => dosetIndicator_left Γ K α hγ g) (fun _ hk g => dosetIndicator_right Γ K α hk g),
    isAdelicAutomorphic_of_biInvariant Γ Z K Kf hKf hZK hZ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩

/-! ### D11: the adelic lift through strong approximation (§4.2, (4.2)) -/

/-- **D11 (§4.2, (4.2) and the two bullet points, p. 57): extending a function from an open subgroup
to a left-$\Gamma$-invariant function.** Let $U \le G$ be a subgroup (in the notes
$U = \mathrm{SL}_2(\mathbb{R}) \times K_f(N)$) with $G = \Gamma U$ (*strong approximation*, the
hypothesis `hSA`), and let $\varphi : G \to \mathbb{C}$ be invariant on $U$ under $\Gamma \cap U$:
$\varphi(\gamma u) = \varphi(u)$ whenever $u, \gamma u \in U$, $\gamma \in \Gamma$. Then there is a unique
$F : G \to \mathbb{C}$ with $F(\gamma g) = F(g)$ for all $\gamma \in \Gamma$ and $F = \varphi$ on $U$.

*Update (candidate; pending author):* the notes define $\mathcal{F}(g_\mathbb{A}) :=
(f|_{k,\chi,\mathbb{A}}\, g_\mathbb{A})(i)$ by a formula involving $\chi_p(d_p)$, which only makes sense
for $g_p \in K_p(N)$ (for general $g_p \in \mathrm{SL}_2(\mathbb{Q}_p)$, $d_p \notin \mathbb{Z}_p$), so the
formula defines $\mathcal{F}$ on $U = \mathrm{SL}_2(\mathbb{R}) \times K_f(N)$ only, and the bullet
"$\mathcal{F}(g'g_\mathbb{A}) = \mathcal{F}(g_\mathbb{A})$ for all $g' \in \mathrm{SL}_2(\mathbb{Q})$" is then
the *definition* of $\mathcal{F}$ on all of $\mathrm{SL}_2(\mathbb{A})$ via strong approximation
$\mathrm{SL}_2(\mathbb{A}) = \mathrm{SL}_2(\mathbb{Q})\,U$; this theorem is that step. -/
@[kb "hanke2011aws" "§4.2, (4.2), p. 57"]
theorem exists_unique_lift (Γ U : Subgroup G) (hSA : ∀ g : G, ∃ γ ∈ Γ, ∃ u ∈ U, g = γ * u)
    (φ : G → ℂ) (hφ : ∀ γ ∈ Γ, ∀ u ∈ U, γ * u ∈ U → φ (γ * u) = φ u) :
    ∃! F : G → ℂ, (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) ∧ ∀ u ∈ U, F u = φ u := by
  classical
  -- choose a decomposition of each g
  choose γ hγ u hu hg using hSA
  refine ⟨fun g => φ (u g), ⟨?_, ?_⟩, ?_⟩
  · intro δ hδ g
    -- δ g = (δ γ_g) u_g = γ_{δg} u_{δg}, so u_{δg} = (γ_{δg}⁻¹ δ γ_g) u_g
    have e1 : u (δ * g) = (γ (δ * g))⁻¹ * (δ * g) := eq_inv_mul_of_mul_eq (hg (δ * g)).symm
    have e : u (δ * g) = (γ (δ * g))⁻¹ * δ * γ g * u g := by
      calc u (δ * g) = (γ (δ * g))⁻¹ * (δ * (γ g * u g)) := by rw [e1, ← hg g]
        _ = _ := by group
    simp only
    rw [e]
    exact hφ _ (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hγ _)) hδ) (hγ g)) _ (hu g) (e ▸ hu (δ * g))
  · intro v hv
    -- v = γ_v u_v with v, u_v ∈ U, so γ_v ∈ Γ ∩ U and φ(v) = φ(γ_v u_v) = φ(u_v)
    simp only
    have hv' : γ v * u v ∈ U := by rw [← hg v]; exact hv
    calc φ (u v) = φ (γ v * u v) := (hφ _ (hγ v) _ (hu v) hv').symm
      _ = φ v := by rw [← hg v]
  · rintro F ⟨hF1, hF2⟩
    funext g
    conv_lhs => rw [hg g]
    rw [hF1 _ (hγ g), hF2 _ (hu g)]

/-- **D11, second bullet of p. 57 (right equivariance).** In the situation of `exists_unique_lift`,
if moreover $\varphi(uk) = \varepsilon(k)\,\varphi(u)$ for $u \in U$, $k \in K_f \le U$ and a function
$\varepsilon$, then the lift satisfies $F(gk) = \varepsilon(k) F(g)$ for all $g \in G$. -/
@[kb "hanke2011aws" "§4.2, p. 57"]
theorem lift_mul_right (Γ U Kf : Subgroup G) (hKf : Kf ≤ U) (F φ : G → ℂ) (ε : G → ℂ)
    (hSA : ∀ g : G, ∃ γ ∈ Γ, ∃ u ∈ U, g = γ * u)
    (hF1 : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) (hF2 : ∀ u ∈ U, F u = φ u)
    (hε : ∀ u ∈ U, ∀ k ∈ Kf, φ (u * k) = ε k * φ u) (g : G) {k : G} (hk : k ∈ Kf) :
    F (g * k) = ε k * F g := by
  obtain ⟨γ, hγ, u, hu, rfl⟩ := hSA g
  rw [mul_assoc, hF1 _ hγ, hF1 _ hγ, hF2 _ (U.mul_mem hu (hKf hk)), hF2 _ hu, hε _ hu _ hk]

end QuadFormsKB.AWS
