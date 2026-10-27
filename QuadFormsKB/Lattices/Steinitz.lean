/-
# Steinitz's theorem for lattices over $\mathcal O_F$, and freeness of the genus of $\mathcal O_F^n$

**Setting.** $F$ a number field, $V = F^n$, an $\mathcal O_F$-lattice $M \subseteq V$ (`Submodule.IsLattice F M`). No class-number
hypothesis: $\mathcal O_F$ is only a Dedekind domain.

**Main results.**
* `exists_spanSingleton_mul_add_eq_one`: for nonzero fractional ideals $\mathfrak a, \mathfrak b$ there are $\alpha, \beta \in F$ with
  $\alpha\mathfrak a + \beta\mathfrak b = \mathcal O_F$ (via `IsDedekindDomain.exists_sup_span_eq`).
* `exists_split`: if $\ell(K) = \mathfrak a \ne 0$ for a functional $\ell$, then $\mathfrak a w \subseteq K$ for some $w$ with $\ell(w) = 1$
  (projectivity of $\mathfrak a$, by hand).
* `exists_functional`: a submodule containing two independent vectors has a functional with $\ell(K) = \mathcal O_F$.
* `exists_free_part`, **`exists_gl_free_part`**: $M \subseteq F^{m+1}$ has a basis $\gamma$ of $F^{m+1}$ with $\gamma e_i \in M$ and
  $(\gamma^{-1}x)_i \in \mathcal O_F$ for $x \in M$, $i < m$ (0-based indices; $e_m$ is the last basis vector).
* **`exists_eq_glImage_steinitzLat`** (Steinitz): $M = \gamma(\mathcal O_F^m \oplus \mathfrak c)$, i.e. $M \cong \mathcal O_F^{n-1} \oplus \mathfrak c$.
* **`exists_latOf_of_loc`**: if $M_\mathfrak p = g_\mathfrak p\,\mathfrak o_\mathfrak p^{n}$ with $\det g_\mathfrak p \in \mathfrak o_\mathfrak p^\times$ for every
  $\mathfrak p$ (trivial Steinitz class), then $M = \gamma\mathcal O_F^n$ is free.
* **`exists_latOf_of_sameGenus`**: for $Q$ nondegenerate, **every lattice in the genus of $\mathcal O_F^n$ is free**, over every number
  field ($g_\mathfrak p \in O(V)(F_\mathfrak p)$ has $\det g_\mathfrak p = \pm1$). This discharges the hypothesis `GenusFree` without
  $h_F = 1$ (`HilbertModular/SteinitzGenus.lean`).

**Route.** No structure theory of modules over Dedekind domains is used (Mathlib has none). Free directions are split off one
at a time with functionals $\ell$, $\ell(M) = \mathcal O_F$ (coprime scaling of two fractional ideals); the last coordinate is a
fractional ideal $\mathfrak c$. Freeness is then local: $\mathfrak c = (\det\gamma_0)^{-1}\mathcal O_F$ by two local estimates (the
adjugate of $\gamma_0^{-1}g_\mathfrak p$, and determinants of vectors of $M$), and the local–global principle for
lattices (`mem_iff_forall_loc`). The Steinitz class is not defined as an element of the class group; only its
triviality is used.

Sources: Steinitz, *Rechteckige Systeme und Moduln in algebraischen Zahlkörpern I*, Math. Ann. 71 (1911) 328–354
[unverified]; O'Meara (1963), §81 (81:5, p. 212, lattices over Dedekind domains), §82.
-/
import QuadFormsKB.Lattices.FreeBridge

open NumberField FractionalIdeal Matrix
open scoped nonZeroDivisors

namespace QuadFormsKB.Lattices.Steinitz

set_option linter.unusedSectionVars false

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

local notation "ιO" => algebraMap (𝓞 F) F

/-- **Coprime scaling of fractional ideals**: for nonzero fractional ideals $\mathfrak a, \mathfrak b$ of $\mathcal O_F$ there are
$\alpha, \beta \in F$ with $\alpha\mathfrak a + \beta\mathfrak b = \mathcal O_F$. *Proof:* $\alpha\mathfrak a = A$ and $d\mathfrak b^{-1} = B$ are
integral; `IsDedekindDomain.exists_sup_span_eq` gives $g$ with $AB + (g) = B$; then $\beta = g/d$ works since
$(A + gB^{-1})B = B$. -/
@[kb "omeara1963" "§22C, 22:5 and 22:9, pp. 48, 50 (coprime scaling of fractional ideals); 22:5c, p. 48 is a consequence"]
theorem exists_spanSingleton_mul_add_eq_one {I J : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0) :
    ∃ α β : F, spanSingleton (𝓞 F)⁰ α * I + spanSingleton (𝓞 F)⁰ β * J = 1 := by
  obtain ⟨a, A, ha, hIA⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  obtain ⟨d, B, hd, hJB⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J⁻¹
  have ha' : ιO a ≠ 0 := by simpa using (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha
  have hd' : ιO d ≠ 0 := by simpa using (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd
  have hA : A ≠ ⊥ := by
    rintro rfl
    apply hI; rw [hIA, coeIdeal_bot, mul_zero]
  have hB : B ≠ ⊥ := by
    rintro rfl
    apply inv_ne_zero hJ; rw [hJB, coeIdeal_bot, mul_zero]
  have hB0 : (B : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by rwa [Ne, coeIdeal_eq_zero]
  obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (show A * B ≤ B from Ideal.mul_le_right)
    (mul_ne_zero hA hB)
  refine ⟨ιO a, ιO g * (ιO d)⁻¹, ?_⟩
  have e1 : spanSingleton (𝓞 F)⁰ (ιO a) * I = A := by
    rw [hIA, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha', map_one, one_mul]
  have e2 : J = spanSingleton (𝓞 F)⁰ (ιO d) * (B : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    rw [← inv_inv J, hJB, mul_inv, spanSingleton_inv, inv_inv]
  have e3 : spanSingleton (𝓞 F)⁰ (ιO g * (ιO d)⁻¹) * J =
      spanSingleton (𝓞 F)⁰ (ιO g) * (B : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    rw [e2, ← mul_assoc, ← map_mul, mul_assoc, inv_mul_cancel₀ hd', mul_one]
  rw [e1, e3]
  apply mul_right_cancel₀ hB0
  rw [one_mul, add_mul, mul_assoc, inv_mul_cancel₀ hB0, mul_one, ← coeIdeal_mul,
    ← coeIdeal_span_singleton, ← coeIdeal_sup, hg]


variable {n : ℕ}

local notation "V" => Fin n → F

/-- A submodule of an f.g. submodule, mapped by a linear functional, is a fractional ideal. -/
theorem isFractional_map {K M : Submodule (𝓞 F) V} (hM : M.FG) (hKM : K ≤ M) (ℓ : V →ₗ[F] F) :
    IsFractional (𝓞 F)⁰ (K.map (ℓ.restrictScalars (𝓞 F))) :=
  isFractional_of_le (J := ⟨_, isFractional_of_fg (hM.map (ℓ.restrictScalars (𝓞 F)))⟩)
    (Submodule.map_mono hKM)

theorem smul_mem_of_mem_one {K : Submodule (𝓞 F) V} {c : F} (hc : c ∈ (1 : FractionalIdeal (𝓞 F)⁰ F))
    {x : V} (hx : x ∈ K) : c • x ∈ K := by
  obtain ⟨c', rfl⟩ := (mem_one_iff _).mp hc
  rw [algebraMap_smul]; exact K.smul_mem c' hx

/-- **Splitting off a rank-one piece** (the projectivity of a fractional ideal, by hand): if $\ell(K) = \mathfrak a \ne 0$ then there is
$w$ with $\ell(w) = 1$ and $\mathfrak a w \subseteq K$, so $K = (K \cap \ker\ell) \oplus \mathfrak a w$. *Proof:* $1 = \sum a_ib_i$ with
$a_i = \ell(k_i) \in \mathfrak a$, $b_i \in \mathfrak a^{-1}$; take $w = \sum b_ik_i$. -/
theorem exists_split {K M : Submodule (𝓞 F) V} (hM : M.FG) (hKM : K ≤ M) (ℓ : V →ₗ[F] F)
    {u : V} (hu : u ∈ K) (hℓu : ℓ u ≠ 0) : ∃ w : V, ℓ w = 1 ∧ ∀ k ∈ K, ℓ k • w ∈ K := by
  classical
  set A : FractionalIdeal (𝓞 F)⁰ F := ⟨_, isFractional_map hM hKM ℓ⟩
  have hmemA : ∀ a, a ∈ A ↔ ∃ k ∈ K, ℓ k = a := fun a => by
    change a ∈ K.map (ℓ.restrictScalars (𝓞 F)) ↔ _
    rw [Submodule.mem_map]; rfl
  have hA : A ≠ 0 := by
    intro h
    have : ℓ u ∈ A := (hmemA _).mpr ⟨u, hu, rfl⟩
    rw [h, mem_zero_iff] at this
    exact hℓu this
  let T : Submodule (𝓞 F) F :=
    { carrier := {x | ∃ w : V, ℓ w = x ∧ ∀ k ∈ K, ℓ k • w ∈ K}
      add_mem' := by
        rintro _ _ ⟨w₁, rfl, h₁⟩ ⟨w₂, rfl, h₂⟩
        exact ⟨w₁ + w₂, map_add ℓ w₁ w₂, fun k hk => by rw [smul_add]; exact K.add_mem (h₁ k hk) (h₂ k hk)⟩
      zero_mem' := ⟨0, map_zero ℓ, fun k _ => by rw [smul_zero]; exact K.zero_mem⟩
      smul_mem' := by
        rintro c _ ⟨w, rfl, h⟩
        refine ⟨c • w, ?_, fun k hk => ?_⟩
        · rw [← algebraMap_smul F c w, map_smul, smul_eq_mul, Algebra.smul_def]
        · rw [← algebraMap_smul F c w, smul_comm, algebraMap_smul]
          exact K.smul_mem c (h k hk) }
  have hle : ((A * A⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) ≤ T := by
    rw [coe_mul]
    refine Submodule.mul_le.mpr fun a ha b hb => ?_
    obtain ⟨k₀, hk₀, rfl⟩ := (hmemA a).mp ha
    refine ⟨b • k₀, by rw [map_smul, smul_eq_mul, mul_comm], fun k hk => ?_⟩
    rw [smul_smul]
    refine smul_mem_of_mem_one ?_ hk₀
    rw [mul_comm]
    exact (mem_inv_iff hA).mp hb _ ((hmemA _).mpr ⟨k, hk, rfl⟩)
  have h1 : (1 : F) ∈ ((A * A⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
    rw [mul_inv_cancel₀ hA]; exact (mem_one_iff _).mpr ⟨1, map_one _⟩
  obtain ⟨w, hw, hwK⟩ := hle h1
  exact ⟨w, hw, hwK⟩

/-- **A functional with $\ell(K) = \mathcal O_F$** on a module containing two independent vectors (the rank-$\ge 2$ step of Steinitz's
theorem). Given $u, u' \in K$ and functionals with $\ell_1(u) = 1$, $\ell_1(u') = 0$, $\ell_2(u') = 1$, split $K = K' \oplus \mathfrak a w$
($K' = K \cap \ker\ell_1$, `exists_split`), put $\ell_2' = \ell_2 - \ell_2(w)\ell_1$ and $\mathfrak b = \ell_2'(K')$; then
$(\alpha\ell_1 + \beta\ell_2')(K) = \alpha\mathfrak a + \beta\mathfrak b$, which is $\mathcal O_F$ for suitable $\alpha, \beta$
(`exists_spanSingleton_mul_add_eq_one`). -/
theorem exists_functional {K M : Submodule (𝓞 F) V} (hM : M.FG) (hKM : K ≤ M) {u u' : V} (hu : u ∈ K)
    (hu' : u' ∈ K) (ℓ₁ ℓ₂ : V →ₗ[F] F) (h11 : ℓ₁ u = 1) (h12 : ℓ₁ u' = 0) (h22 : ℓ₂ u' = 1) :
    ∃ ℓ : V →ₗ[F] F, (∀ k ∈ K, ℓ k ∈ (algebraMap (𝓞 F) F).range) ∧ ∃ s ∈ K, ℓ s = 1 := by
  classical
  obtain ⟨w, hw1, hwK⟩ := exists_split hM hKM ℓ₁ hu (by rw [h11]; exact one_ne_zero)
  set ℓ₂' : V →ₗ[F] F := ℓ₂ - ℓ₂ w • ℓ₁ with hℓ₂'
  have hℓ₂'w : ℓ₂' w = 0 := by simp [hℓ₂', hw1]
  set K' : Submodule (𝓞 F) V := K ⊓ LinearMap.ker (ℓ₁.restrictScalars (𝓞 F))
  have hK'K : K' ≤ M := inf_le_left.trans hKM
  set A : FractionalIdeal (𝓞 F)⁰ F := ⟨_, isFractional_map hM hKM ℓ₁⟩
  set B : FractionalIdeal (𝓞 F)⁰ F := ⟨_, isFractional_map hM hK'K ℓ₂'⟩
  have hmemA : ∀ a, a ∈ A ↔ ∃ k ∈ K, ℓ₁ k = a := fun a => by
    change a ∈ K.map (ℓ₁.restrictScalars (𝓞 F)) ↔ _
    rw [Submodule.mem_map]; rfl
  have hmemB : ∀ b, b ∈ B ↔ ∃ k ∈ K', ℓ₂' k = b := fun b => by
    change b ∈ K'.map (ℓ₂'.restrictScalars (𝓞 F)) ↔ _
    rw [Submodule.mem_map]; rfl
  have hu'K' : u' ∈ K' := ⟨hu', by simp [h12]⟩
  have hA : A ≠ 0 := fun h => by
    have : (1 : F) ∈ A := (hmemA 1).mpr ⟨u, hu, h11⟩
    rw [h, mem_zero_iff] at this; exact one_ne_zero this
  have hB : B ≠ 0 := fun h => by
    have : (1 : F) ∈ B := (hmemB 1).mpr ⟨u', hu'K', by simp [hℓ₂', h22, h12]⟩
    rw [h, mem_zero_iff] at this; exact one_ne_zero this
  obtain ⟨α, β, hαβ⟩ := exists_spanSingleton_mul_add_eq_one hA hB
  have hmem : ∀ x, x ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) ↔ ∃ a ∈ A, ∃ b ∈ B, α * a + β * b = x := by
    intro x
    rw [← hαβ]
    change x ∈ ((spanSingleton (𝓞 F)⁰ α * A + spanSingleton (𝓞 F)⁰ β * B : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F) ↔ _
    rw [coe_add, Submodule.add_eq_sup, Submodule.mem_sup]
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      obtain ⟨a, ha, rfl⟩ := mem_singleton_mul.mp hy
      obtain ⟨b, hb, rfl⟩ := mem_singleton_mul.mp hz
      exact ⟨a, ha, b, hb, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨_, mem_singleton_mul.mpr ⟨a, ha, rfl⟩, _, mem_singleton_mul.mpr ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨α • ℓ₁ + β • ℓ₂', fun k hk => ?_, ?_⟩
  · -- `ℓ(k) = α ℓ₁(k) + β ℓ₂'(k - ℓ₁(k) w)`
    have hk' : k - ℓ₁ k • w ∈ K' := ⟨K.sub_mem hk (hwK k hk), by simp [hw1]⟩
    obtain ⟨c, hc⟩ := (mem_one_iff _).mp ((hmem _).mpr ⟨ℓ₁ k, (hmemA _).mpr ⟨k, hk, rfl⟩,
      ℓ₂' (k - ℓ₁ k • w), (hmemB _).mpr ⟨_, hk', rfl⟩, rfl⟩)
    refine ⟨c, hc.trans ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_sub, map_smul, hℓ₂'w,
      mul_zero, sub_zero]
  · obtain ⟨a, ha, b, hb, hab⟩ := (hmem 1).mp ((mem_one_iff _).mpr ⟨1, map_one _⟩)
    obtain ⟨k₁, hk₁, rfl⟩ := (hmemA a).mp ha
    obtain ⟨k₂, hk₂, rfl⟩ := (hmemB b).mp hb
    refine ⟨ℓ₁ k₁ • w + k₂, K.add_mem (hwK k₁ hk₁) hk₂.1, ?_⟩
    have h2 : ℓ₁ k₂ = 0 := hk₂.2
    rw [← hab]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add, map_smul, hw1,
      hℓ₂'w, h2]
    ring


/-- Two vectors that are not proportional admit "dual" functionals. -/
theorem exists_dual_pair {u u' : V} (hu : u ≠ 0) (hu' : u' ∉ Submodule.span F {u}) :
    ∃ ℓ₁ ℓ₂ : V →ₗ[F] F, ℓ₁ u = 1 ∧ ℓ₁ u' = 0 ∧ ℓ₂ u' = 1 := by
  obtain ⟨f, hf, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu' inferInstance
  have hu2 : u ∉ Submodule.span F {u'} := by
    intro h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
    have hc : c ≠ 0 := by rintro rfl; exact hu (zero_smul _ _)
    exact hu' (Submodule.mem_span_singleton.mpr ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩)
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu2 inferInstance
  have hgu' : g u' = 0 := by
    have : g u' ∈ (Submodule.span F {u'}).map g := Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self u')
    rw [hg0] at this; exact (Submodule.mem_bot F).mp this
  refine ⟨(g u)⁻¹ • g, (f u')⁻¹ • f, ?_, ?_, ?_⟩
  · simp [inv_mul_cancel₀ hg]
  · simp [hgu']
  · simp [inv_mul_cancel₀ hf]

theorem intSmul_mem {M : Submodule (𝓞 F) V} {c : F} (hc : c ∈ (algebraMap (𝓞 F) F).range) {x : V}
    (hx : x ∈ M) : c • x ∈ M := by
  obtain ⟨c', rfl⟩ := hc
  rw [algebraMap_smul]; exact M.smul_mem c' hx

/-- **$k$ free directions** ($k < n$): vectors $s_0, \dots, s_{k-1} \in M$ and functionals $\ell_0, \dots, \ell_{k-1}$ with
$\ell_i(M) \subseteq \mathcal O_F$ and $\ell_i(s_j) = \delta_{ij}$, so that $M = \bigoplus_i\mathcal O_Fs_i \oplus (M \cap \bigcap_i\ker\ell_i)$.
Induction on $k$ with `exists_functional` applied to $K = M \cap \bigcap_i\ker\ell_i$, which contains two independent vectors because
$M$ spans $F^n$ and $k + 1 < n$. -/
theorem exists_free_part {M : Submodule (𝓞 F) V} (hM : M.IsLattice F) :
    ∀ k, k < n → ∃ (s : Fin k → V) (ℓ : Fin k → V →ₗ[F] F), (∀ i, s i ∈ M) ∧
      (∀ i, ∀ x ∈ M, ℓ i x ∈ (algebraMap (𝓞 F) F).range) ∧ (∀ i j, ℓ i (s j) = if i = j then 1 else 0) := by
  classical
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨s, ℓ, hs, hℓ, hδ⟩ := ih (by omega)
    set K : Submodule (𝓞 F) V := M ⊓ ⨅ i, LinearMap.ker ((ℓ i).restrictScalars (𝓞 F)) with hKdef
    have hmemK : ∀ x, x ∈ K ↔ x ∈ M ∧ ∀ i, ℓ i x = 0 := fun x => by
      simp [hKdef, Submodule.mem_iInf]
    set proj : V →ₗ[F] V := LinearMap.id - ∑ i, (ℓ i).smulRight (s i) with hproj
    have hprojx : ∀ x, proj x = x - ∑ i, ℓ i x • s i := fun x => by simp [hproj]
    have hprojK : ∀ x ∈ M, proj x ∈ K := by
      intro x hx
      refine (hmemK _).mpr ⟨?_, fun j => ?_⟩
      · rw [hprojx]
        exact M.sub_mem hx (M.sum_mem fun i _ => intSmul_mem (hℓ i x hx) (hs i))
      · rw [hprojx, map_sub, map_sum]
        simp only [map_smul, hδ, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
        rw [eq_comm] at *
        simp
    have hdecomp : ∀ x, x = proj x + ∑ i, ℓ i x • s i := fun x => by rw [hprojx]; abel
    -- two independent vectors in `K`
    have htwo : ∃ u ∈ K, ∃ u' ∈ K, u ≠ 0 ∧ u' ∉ Submodule.span F {u} := by
      by_contra hcon
      push Not at hcon
      set u₀ : V := if h : ∃ u ∈ K, u ≠ 0 then h.choose else 0
      have hu₀ : ∀ x ∈ K, x ∈ Submodule.span F {u₀} := by
        intro x hx
        by_cases h : ∃ u ∈ K, u ≠ 0
        · have := hcon _ h.choose_spec.1 x hx h.choose_spec.2
          simpa [u₀, h] using this
        · push Not at h
          rw [h x hx]; exact Submodule.zero_mem _
      have hle : (⊤ : Submodule F V) ≤ Submodule.span F (Set.range (Fin.snoc s u₀ : Fin (k + 1) → V)) := by
        rw [← hM.span_eq_top]
        refine Submodule.span_le.mpr fun x hx => ?_
        rw [hdecomp x]
        refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨i.castSucc, by simp⟩))
        have h1 := hu₀ _ (hprojK x hx)
        exact Submodule.span_le.mpr (by
          rintro _ rfl; exact Submodule.subset_span ⟨Fin.last k, by simp⟩) h1
      have h1 := Submodule.finrank_mono hle
      have h2 := finrank_range_le_card (R := F) (Fin.snoc s u₀ : Fin (k + 1) → V)
      rw [finrank_top, Module.finrank_fin_fun] at h1
      rw [Fintype.card_fin] at h2
      change Module.finrank F (Submodule.span F _) ≤ _ at h2
      omega
    obtain ⟨u, hu, u', hu', hu0, hu'u⟩ := htwo
    obtain ⟨ℓ₁, ℓ₂, h11, h12, h22⟩ := exists_dual_pair hu0 hu'u
    obtain ⟨ℓ', hℓ', s', hs', hℓs'⟩ := exists_functional hM.fg inf_le_left hu hu' ℓ₁ ℓ₂ h11 h12 h22
    have hs'K := (hmemK s').mp hs'
    refine ⟨Fin.snoc s s', Fin.snoc ℓ (ℓ' ∘ₗ proj), fun i => ?_, fun i x hx => ?_, fun i j => ?_⟩
    · induction i using Fin.lastCases with
      | last => simpa using hs'K.1
      | cast i => simpa using hs i
    · induction i using Fin.lastCases with
      | last => simpa using hℓ' _ (hprojK x hx)
      | cast i => simpa using hℓ i x hx
    · have hprojs : ∀ j, proj (s j) = 0 := fun j => by
        rw [hprojx]
        simp [hδ]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          have : proj s' = s' := by rw [hprojx]; simp [hs'K.2]
          simp [this, hℓs']
        | cast j => simp [hprojs j, (Fin.castSucc_lt_last j).ne']
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp [hs'K.2 i, (Fin.castSucc_lt_last i).ne]
        | cast j => simp [hδ]


/-- The complement of the free directions: $x - \sum_i\ell_i(x)s_i \in M \cap \bigcap_i\ker\ell_i$. -/
theorem sub_sum_mem {k : ℕ} {M : Submodule (𝓞 F) V} {s : Fin k → V} {ℓ : Fin k → V →ₗ[F] F}
    (hs : ∀ i, s i ∈ M) (hℓ : ∀ i, ∀ x ∈ M, ℓ i x ∈ (algebraMap (𝓞 F) F).range)
    (hδ : ∀ i j, ℓ i (s j) = if i = j then 1 else 0) {x : V} (hx : x ∈ M) :
    x - ∑ i, ℓ i x • s i ∈ M ∧ ∀ j, ℓ j (x - ∑ i, ℓ i x • s i) = 0 := by
  classical
  refine ⟨M.sub_mem hx (M.sum_mem fun i _ => intSmul_mem (hℓ i x hx) (hs i)), fun j => ?_⟩
  rw [map_sub, map_sum]
  simp [hδ]

/-- **Steinitz's theorem, the free part** ($n = m + 1$): every $\mathcal O_F$-lattice $M \subseteq F^{m+1}$ has a basis $\gamma$ of $F^{m+1}$
with $\gamma e_i \in M$ and $(\gamma^{-1}x)_i \in \mathcal O_F$ for all $x \in M$ and $i < m$; hence
$M = \gamma(\mathcal O_F^m \oplus \mathfrak c)$ with $\mathfrak c = \{(\gamma^{-1}x)_m : x \in M\}$ a fractional ideal (`eq_glImage_steinitzLat`).
The columns are $s_0, \dots, s_{m-1}$ of `exists_free_part` and a nonzero $w \in M \cap \bigcap_i\ker\ell_i$. -/
@[kb "omeara1963" "§81B, 81:5, p. 212; cassels1978 Ch. 7, Notes, p. 109"]
theorem exists_gl_free_part {m : ℕ} {M : Submodule (𝓞 F) (Fin (m + 1) → F)} (hM : M.IsLattice F) :
    ∃ γ : GL (Fin (m + 1)) F, (∀ i : Fin m, γ.val *ᵥ Pi.single i.castSucc 1 ∈ M) ∧
      ∀ x ∈ M, ∀ i : Fin m, (γ⁻¹.val *ᵥ x) i.castSucc ∈ (algebraMap (𝓞 F) F).range := by
  classical
  obtain ⟨s, ℓ, hs, hℓ, hδ⟩ := exists_free_part hM m (by omega)
  have hw : ∃ w ∈ M, (∀ i, ℓ i w = 0) ∧ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : (⊤ : Submodule F (Fin (m + 1) → F)) ≤ Submodule.span F (Set.range s) := by
      rw [← hM.span_eq_top]
      refine Submodule.span_le.mpr fun x hx => ?_
      obtain ⟨h1, h2⟩ := sub_sum_mem hs hℓ hδ hx
      have h0 := hcon _ h1 h2
      rw [sub_eq_zero] at h0
      rw [h0]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_range_le_card (R := F) s
    rw [finrank_top, Module.finrank_fin_fun] at h1
    rw [Fintype.card_fin] at h2
    change Module.finrank F (Submodule.span F _) ≤ _ at h2
    omega
  obtain ⟨w, hwM, hwℓ, hw0⟩ := hw
  set col : Fin (m + 1) → Fin (m + 1) → F := Fin.snoc s w with hcol
  set γM : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.of fun r c => col c r
  have hγcol : ∀ c, γM *ᵥ Pi.single c 1 = col c := fun c => by
    ext r; rw [Matrix.mulVec_single_one]; rfl
  have hℓcol : ∀ i c, ℓ i (col c) = if c = i.castSucc then 1 else 0 := by
    intro i c
    induction c using Fin.lastCases with
    | last => simp [hcol, hwℓ, (Fin.castSucc_lt_last i).ne']
    | cast j => simp [hcol, hδ, eq_comm]
  have hli : LinearIndependent F col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hcs : ∀ i : Fin m, g i.castSucc = 0 := by
      intro i
      have := congrArg (ℓ i) hg
      rw [map_sum, map_zero] at this
      simpa [hℓcol] using this
    have hlast : g (Fin.last m) = 0 := by
      rw [Fin.sum_univ_castSucc] at hg
      simp only [hcs, zero_smul, Finset.sum_const_zero, zero_add] at hg
      have : col (Fin.last m) = w := by simp [hcol]
      rw [this] at hg
      exact (smul_eq_zero.mp hg).resolve_right hw0
    intro c
    induction c using Fin.lastCases with
    | last => exact hlast
    | cast i => exact hcs i
  have hu : IsUnit γM := by
    refine Matrix.linearIndependent_col_iff_isUnit.mp ?_
    convert hli using 1
    funext c; ext r; rfl
  refine ⟨hu.unit, fun i => ?_, fun x hx i => ?_⟩
  · change γM *ᵥ _ ∈ M
    rw [hγcol]; simpa [hcol] using hs i
  · set y := (hu.unit⁻¹ : GL (Fin (m + 1)) F).val *ᵥ x
    have hx' : x = ∑ c, y c • col c := by
      simp_rw [← hγcol]
      have := sum_smul_col hu.unit y
      change ∑ j, y j • (γM *ᵥ Pi.single j 1) = γM *ᵥ y at this
      rw [this]
      change x = (hu.unit : GL (Fin (m + 1)) F).val *ᵥ ((hu.unit⁻¹ : GL (Fin (m + 1)) F).val *ᵥ x)
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have h1 : ℓ i x = y i.castSucc := by
      rw [hx', map_sum]
      simp [hℓcol]
    rw [← h1]; exact hℓ i x hx


/-! ### Freeness from local data -/

section Local

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- A matrix over $F_\mathfrak p$ with integral entries has integral determinant. -/
theorem valued_det_le_one {A : Matrix (Fin n) (Fin n) Fv} (hA : ∀ i j, Valued.v (A i j) ≤ 1) :
    Valued.v A.det ≤ 1 := by
  set B : Matrix (Fin n) (Fin n) 𝔬 := Matrix.of fun i j => toO v _ (hA i j)
  have hAB : A = B.map (algebraMap 𝔬 Fv) := by ext i j; rfl
  rw [hAB, show (B.map (algebraMap 𝔬 Fv)).det = algebraMap 𝔬 Fv B.det from (RingHom.map_det _ _).symm]
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (B.det).2

variable {v}

/-- **Determinants of vectors of $M$ are integral at $\mathfrak p$** when $M_\mathfrak p = g\,\mathfrak o_\mathfrak p^n$ with $\det g$ a unit. -/
theorem valued_det_le_one_of_cols {M : Submodule (𝓞 F) V} {g : GL (Fin n) Fv}
    (hg : locAct v g (std v) = loc v M) (hdet : Valued.v g.val.det = 1) {X : Matrix (Fin n) (Fin n) F}
    (hX : ∀ j, X *ᵥ Pi.single j 1 ∈ M) : Valued.v (algebraMap F Fv X.det) ≤ 1 := by
  set Xv := X.map (algebraMap F Fv)
  have hXv : ∀ j, ∃ z ∈ std v, g.val *ᵥ z = Xv *ᵥ Pi.single j 1 := by
    intro j
    have h1 : Xv *ᵥ Pi.single j 1 = locVec v (X *ᵥ Pi.single j 1) := by
      rw [locVec_mulVec, locVec_single, map_one]
    rw [h1]
    exact mem_locAct.mp (hg ▸ locVec_mem_loc v (hX j))
  have hY : ∀ i j, Valued.v ((g⁻¹.val * Xv) i j) ≤ 1 := by
    intro i j
    obtain ⟨z, hz, hgz⟩ := hXv j
    have hent : ∀ (B : Matrix (Fin n) (Fin n) Fv) i j, B i j = (B *ᵥ Pi.single j 1) i := by
      intro B i j; rw [Matrix.mulVec_single_one]; rfl
    have : (g⁻¹.val * Xv) i j = z i := by
      rw [hent (g⁻¹.val * Xv) i j, ← Matrix.mulVec_mulVec, ← hgz, Matrix.mulVec_mulVec,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [this]
    simpa using hz i
  have e : Xv = g.val * (g⁻¹.val * Xv) := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  rw [RingHom.map_det]
  change Valued.v Xv.det ≤ 1
  rw [e, Matrix.det_mul, map_mul, hdet, one_mul]
  exact valued_det_le_one v hY

end Local

/-- **A lattice which is locally $g_\mathfrak p\,\mathfrak o_\mathfrak p^{m+1}$ with $\det g_\mathfrak p$ a unit everywhere is free** (its Steinitz class
is trivial): $M = \gamma\mathcal O_F^{m+1}$. *Proof.* Take $\gamma_0$ from `exists_gl_free_part`, so $M = \gamma_0(\mathcal O_F^m \oplus \mathfrak c)$, and
$c = (\det\gamma_0)^{-1}$. (a) $\gamma_0(ce_m) \in M$: locally $g^{-1}\gamma_0ce_m = A^{-1}ce_m$ with $A = \gamma_0^{-1}g$, and
$A^{-1}ce_m = (\det g)^{-1}\operatorname{adj}(A)e_m$, whose entries are minors of the first $m$ rows of $A$, which are integral.
(b) $\det\gamma_0\cdot(\gamma_0^{-1}x)_m = \det(\gamma_0e_0, \dots, \gamma_0e_{m-1}, x) \in \mathcal O_F$ for $x \in M$
(`valued_det_le_one_of_cols`). So $\mathfrak c = c\,\mathcal O_F$ and $M = \gamma_0\operatorname{diag}(1, \dots, 1, c)\,\mathcal O_F^{m+1}$. -/
@[kb "omeara1963" "§81B, 81:5, p. 212"]
theorem exists_latOf_of_loc {m : ℕ} {M : Submodule (𝓞 F) (Fin (m + 1) → F)} (hM : M.IsLattice F)
    (hloc : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ g : GL (Fin (m + 1)) (v.adicCompletion F),
      locAct v g (std v) = loc v M ∧ Valued.v g.val.det = 1) :
    ∃ γ : GL (Fin (m + 1)) F, M = latOf γ := by
  classical
  obtain ⟨γ₀, hγ₁, hγ₂⟩ := exists_gl_free_part hM
  have hdet0 : γ₀.val.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp γ₀.isUnit |>.ne_zero
  set c : F := (γ₀.val.det)⁻¹ with hc
  -- (a) `γ₀ (c e_m) ∈ M`
  have ha : γ₀.val *ᵥ Pi.single (Fin.last m) c ∈ M := by
    rw [mem_iff_forall_loc hM]
    intro v
    obtain ⟨g, hg, hdet⟩ := hloc v
    rw [← hg, mem_locAct]
    set Γ := Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ₀
    set A := Γ⁻¹ * g
    -- rows `< m` of `A` are integral
    have hrow : ∀ (r : Fin m) (j : Fin (m + 1)), Valued.v (A.val r.castSucc j) ≤ 1 := by
      intro r j
      have hmem : g.val *ᵥ Pi.single j 1 ∈ loc v M := hg ▸ mem_locAct.mpr ⟨_, by
        intro i; by_cases h : i = j <;> simp [h], rfl⟩
      have key : ∀ y ∈ loc v M, Valued.v ((Γ⁻¹.val *ᵥ y) r.castSucc) ≤ 1 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨x, hx, rfl⟩ := hy
          have : Γ⁻¹.val *ᵥ locVec v x = locVec v (γ₀⁻¹.val *ᵥ x) := by
            rw [locVec_mulVec]; rfl
          rw [this, locVec_apply]
          obtain ⟨a, ha⟩ := hγ₂ x hx r
          rw [← ha, ← IsScalarTower.algebraMap_apply]
          exact valued_int_le_one v a
        | zero => simp
        | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact Valuation.map_add_le _ hy hz
        | smul a y _ hy =>
          rw [Matrix.mulVec_smul]
          change Valued.v ((a : v.adicCompletion F) * _) ≤ 1
          rw [map_mul]
          exact mul_le_one' ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp a.2) hy
      have := key _ hmem
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
    have hdetA : A.val.det * algebraMap F (v.adicCompletion F) γ₀.val.det = g.val.det := by
      have hΓ : Γ * A = g := by simp [A]
      have h1 : Γ.val.det = algebraMap F (v.adicCompletion F) γ₀.val.det := (RingHom.map_det _ _).symm
      rw [← h1, mul_comm, ← Matrix.det_mul, ← Units.val_mul, hΓ]
    refine ⟨g⁻¹.val *ᵥ locVec v (γ₀.val *ᵥ Pi.single (Fin.last m) c), fun i => ?_, ?_⟩
    · have e1 : g⁻¹.val *ᵥ locVec v (γ₀.val *ᵥ Pi.single (Fin.last m) c) =
          A⁻¹.val *ᵥ Pi.single (Fin.last m) (algebraMap F (v.adicCompletion F) c) := by
        rw [locVec_mulVec, locVec_single, Matrix.mulVec_mulVec]
        congr 1
      rw [e1]
      simp only [Matrix.mulVec, dotProduct_single]
      rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
        neg_zero, WithZero.exp_zero, mul_comm, ← mul_assoc, map_mul]
      have hu : Valued.v (algebraMap F (v.adicCompletion F) c * Ring.inverse A.val.det) = 1 := by
        have hA0 : A.val.det ≠ 0 := fun h => by
          rw [h, zero_mul] at hdetA
          rw [← hdetA, map_zero] at hdet; exact zero_ne_one hdet
        rw [Ring.inverse_eq_inv', hc, map_inv₀, ← mul_inv, mul_comm, hdetA, map_inv₀, hdet, inv_one]
      rw [hu, one_mul, Matrix.adjugate_apply]
      refine valued_det_le_one v fun r j => ?_
      induction r using Fin.lastCases with
      | last =>
        rw [Matrix.updateRow_self]
        by_cases h : j = i <;> simp [h]
      | cast r =>
        rw [Matrix.updateRow_ne (Fin.castSucc_lt_last r).ne]
        exact hrow r j
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  -- (b) the last coordinate
  have hb : ∀ x ∈ M, (γ₀⁻¹.val *ᵥ x) (Fin.last m) * γ₀.val.det ∈ (algebraMap (𝓞 F) F).range := by
    intro x hx
    set z := γ₀⁻¹.val *ᵥ x
    set X := γ₀.val * (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F).updateCol (Fin.last m) z
    have hXdet : X.det = z (Fin.last m) * γ₀.val.det := by
      rw [Matrix.det_mul, mul_comm, ← Matrix.cramer_apply, Matrix.cramer_one]
      rfl
    have hXcol : ∀ j, X *ᵥ Pi.single j 1 ∈ M := by
      intro j
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
      induction j using Fin.lastCases with
      | last =>
        rw [show ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F).updateCol (Fin.last m) z).col (Fin.last m) = z by
          ext r; simp [Matrix.col]]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        exact hx
      | cast i =>
        rw [show ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F).updateCol (Fin.last m) z).col i.castSucc =
            Pi.single i.castSucc 1 by
          ext r; simp [Matrix.col, Matrix.one_apply, Pi.single_apply]]
        exact hγ₁ i
    rw [← hXdet]
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun v => ?_
    obtain ⟨g, hg, hdet⟩ := hloc v
    rw [← valued_algebraMap v]
    exact valued_det_le_one_of_cols hg hdet hXcol
  -- (c) `M = γ₀ diag(1, …, 1, c) 𝓞^{m+1}`
  set d : Fin (m + 1) → F := Fin.snoc (fun _ => (1 : F)) c with hd
  have hdu : IsUnit (Matrix.diagonal d) := by
    refine Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i => ?_)
    induction i using Fin.lastCases with
    | last => simpa [hd, hc] using hdet0
    | cast i => simp [hd]
  refine ⟨γ₀ * hdu.unit, ?_⟩
  have hmul : ∀ y, (γ₀ * hdu.unit).val *ᵥ y = γ₀.val *ᵥ (fun i => d i * y i) := by
    intro y
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, IsUnit.unit_spec]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
  ext x
  rw [latOf, mem_glImage]
  constructor
  · intro hx
    set z := γ₀⁻¹.val *ᵥ x
    refine ⟨Fin.snoc (fun i => z i.castSucc) (z (Fin.last m) * γ₀.val.det), ?_, ?_⟩
    · rw [mem_intVec]
      intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hb x hx
      | cast i => rw [Fin.snoc_castSucc]; exact hγ₂ x hx i
    · rw [hmul]
      have : (fun i => d i * (Fin.snoc (fun i => z i.castSucc) (z (Fin.last m) * γ₀.val.det) :
          Fin (m + 1) → F) i) = z := by
        funext i
        induction i using Fin.lastCases with
        | last => simp [hd, hc]; field_simp
        | cast i => simp [hd]
      rw [this, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    rw [hmul, ← sum_smul_col]
    refine M.sum_mem fun j _ => ?_
    obtain ⟨a, ha'⟩ := (mem_intVec.mp hy) j
    induction j using Fin.lastCases with
    | last =>
      have e : (d (Fin.last m) * y (Fin.last m)) • (γ₀.val *ᵥ Pi.single (Fin.last m) 1) =
          y (Fin.last m) • (γ₀.val *ᵥ Pi.single (Fin.last m) c) := by
        rw [show Pi.single (Fin.last m) c = c • (Pi.single (Fin.last m) 1 : Fin (m + 1) → F) by
          rw [← Pi.single_smul', smul_eq_mul, mul_one], Matrix.mulVec_smul, smul_smul]
        simp [hd, mul_comm]
      rw [e]
      exact intSmul_mem ⟨a, ha'⟩ ha
    | cast i =>
      have e : d i.castSucc * y i.castSucc = y i.castSucc := by simp [hd]
      rw [e]
      exact intSmul_mem ⟨a, ha'⟩ (hγ₁ i)


/-- **Every lattice in the genus of $\mathcal O_F^n$ is free** for a nondegenerate form $Q$ ($\det H \ne 0$), over every number field:
$M = \gamma\mathcal O_F^n$. Locally $M_\mathfrak p = g_\mathfrak p\mathfrak o_\mathfrak p^n$ with $g_\mathfrak p \in O(V)(F_\mathfrak p)$, and
$g^{\mathsf T}Hg = H$ forces $\det g_\mathfrak p = \pm1$; apply `exists_latOf_of_loc`. (The Steinitz class of $M$ is
$\prod_\mathfrak p\mathfrak p^{v_\mathfrak p(\det g_\mathfrak p)} = 1$; O'Meara 81:5, p. 212; lattices in one genus have equal volumes, §102A, p. 299.) -/
@[kb "omeara1963" "§102A, p. 297; §81B, 81:5, p. 212"]
theorem exists_latOf_of_sameGenus (Q : QuadForm F n) (hQ : Q.Nondegenerate) {M : Submodule (𝓞 F) V}
    (hM : M.IsLattice F) (hg : SameGenus Q intVec M) : ∃ γ : GL (Fin n) F, M = latOf γ := by
  classical
  cases n with
  | zero =>
    refine ⟨1, ?_⟩
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    simp only [Submodule.zero_mem]
  | succ m =>
    refine exists_latOf_of_loc hM fun v => ?_
    obtain ⟨g, hgO, hgM⟩ := hg v
    refine ⟨g, by rwa [loc_intVec] at hgM, ?_⟩
    have h1 := congrArg Matrix.det ((mem_orthGroup Q).mp hgO)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
    have hH : (Q.hessian.map (algebraMap F (v.adicCompletion F))).det ≠ 0 := by
      rw [show (Q.hessian.map (algebraMap F (v.adicCompletion F))).det =
          algebraMap F (v.adicCompletion F) Q.hessian.det from (RingHom.map_det _ _).symm]
      exact (_root_.map_ne_zero _).mpr hQ
    have h2 : g.val.det ^ 2 = 1 := by
      have : g.val.det ^ 2 * (Q.hessian.map (algebraMap F (v.adicCompletion F))).det =
          1 * (Q.hessian.map (algebraMap F (v.adicCompletion F))).det := by
        rw [one_mul]; conv_rhs => rw [← h1]
        ring
      exact mul_right_cancel₀ hH this
    have h3 : Valued.v g.val.det ^ 2 = 1 := by rw [← map_pow, h2, map_one]
    exact sq_eq_one.mp h3

/-- The lattice $\mathcal O_F^m \oplus \mathfrak c \subseteq F^{m+1}$ (first $m$ coordinates integral, last in $\mathfrak c$). -/
def steinitzLat {m : ℕ} (𝔠 : Submodule (𝓞 F) F) : Submodule (𝓞 F) (Fin (m + 1) → F) where
  carrier := {x | (∀ i : Fin m, x i.castSucc ∈ (algebraMap (𝓞 F) F).range) ∧ x (Fin.last m) ∈ 𝔠}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨fun i => ?_, 𝔠.add_mem hx' hy'⟩
    obtain ⟨a, ha⟩ := hx i; obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by simp [ha, hb]⟩
  zero_mem' := ⟨fun _ => ⟨0, by simp⟩, 𝔠.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨fun i => ?_, 𝔠.smul_mem c hx'⟩
    obtain ⟨a, ha⟩ := hx i
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

/-- **Steinitz's theorem (existence of the normal form)**: every $\mathcal O_F$-lattice $M \subseteq F^{m+1}$ is
$M = \gamma(\mathcal O_F^m \oplus \mathfrak c)$ for some $\gamma \in \mathrm{GL}_{m+1}(F)$ and an $\mathcal O_F$-submodule $\mathfrak c \subseteq F$
(a fractional ideal), i.e. $M \cong \mathcal O_F^m \oplus \mathfrak c$ (Steinitz 1911; O'Meara 81:5, p. 212). -/
@[kb "omeara1963" "§81B, 81:5, p. 212"]
theorem exists_eq_glImage_steinitzLat {m : ℕ} {M : Submodule (𝓞 F) (Fin (m + 1) → F)} (hM : M.IsLattice F) :
    ∃ (γ : GL (Fin (m + 1)) F) (𝔠 : Submodule (𝓞 F) F), M = glImage γ (steinitzLat 𝔠) := by
  classical
  obtain ⟨γ, hγ₁, hγ₂⟩ := exists_gl_free_part hM
  set 𝔠 : Submodule (𝓞 F) F :=
    (glImage γ⁻¹ M).map ((LinearMap.proj (R := F) (φ := fun _ : Fin (m + 1) => F) (Fin.last m)).restrictScalars (𝓞 F))
  refine ⟨γ, 𝔠, ?_⟩
  have hinv : ∀ x, γ.val *ᵥ (γ⁻¹.val *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  ext x
  rw [mem_glImage]
  constructor
  · intro hx
    refine ⟨γ⁻¹.val *ᵥ x, ⟨fun i => hγ₂ x hx i, ?_⟩, hinv x⟩
    exact ⟨γ⁻¹.val *ᵥ x, mulVec_mem_glImage hx, rfl⟩
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    obtain ⟨z, ⟨x', hx', rfl⟩, hz⟩ := hy'
    -- `y = Σ_{i<m} y_i e_i + (γ⁻¹ x')_m e_m` and `γ⁻¹x' - Σ_{i<m} (γ⁻¹x')_i e_i` is in `γ⁻¹ M`
    have hdec : ∀ w : Fin (m + 1) → F, w = ∑ i : Fin m, w i.castSucc • Pi.single i.castSucc 1 +
        w (Fin.last m) • Pi.single (Fin.last m) 1 := fun w => by
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [Fin.sum_univ_castSucc]
      simp [← Pi.single_smul']
    have hγe : ∀ i : Fin m, Pi.single i.castSucc 1 ∈ glImage γ⁻¹ M := fun i => by
      have := mulVec_mem_glImage (γ := γ⁻¹) (hγ₁ i)
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
    have hlast : (γ⁻¹.val *ᵥ x') (Fin.last m) • (Pi.single (Fin.last m) 1 : Fin (m + 1) → F) ∈ glImage γ⁻¹ M := by
      have h1 := (glImage γ⁻¹ M).sub_mem (mulVec_mem_glImage (γ := γ⁻¹) hx')
        ((glImage γ⁻¹ M).sum_mem fun i (_ : i ∈ Finset.univ) =>
          intSmul_mem (hγ₂ x' hx' i) (hγe i))
      rwa [show γ⁻¹.val *ᵥ x' - ∑ i : Fin m, (γ⁻¹.val *ᵥ x') i.castSucc •
          Pi.single i.castSucc 1 = (γ⁻¹.val *ᵥ x') (Fin.last m) • Pi.single (Fin.last m) 1 by
        rw [sub_eq_iff_eq_add']; exact hdec _] at h1
    have hy2 : y ∈ glImage γ⁻¹ M := by
      rw [hdec y]
      refine (glImage γ⁻¹ M).add_mem ((glImage γ⁻¹ M).sum_mem fun i _ => intSmul_mem (hy i) (hγe i)) ?_
      have : y (Fin.last m) = (γ⁻¹.val *ᵥ x') (Fin.last m) := hz.symm
      rw [this]; exact hlast
    obtain ⟨x'', hx'', e⟩ := mem_glImage.mp hy2
    rw [← e, hinv]
    exact hx''

end

end QuadFormsKB.Lattices.Steinitz
