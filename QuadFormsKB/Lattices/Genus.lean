/-
# Lattices over $\mathcal O_F$: orthogonal groups, classes and the genus

**Layer:** the quadratic space $V = F^n$ with the form $Q$ = `Q : QuadForm F n` over a number field $F$
(Hessian $H = C + C^{\mathsf T}$, so $Q(x) = \tfrac12 x^{\mathsf T}Hx$), and lattices $L \subseteq V$ over $\mathcal O_F$
(`Lattices/Local.lean`). Every finite-dimensional quadratic space over $F$ is isometric to one of these
(`Lattices/Basic.lean`).

**Defines**
* `orthGroup Q R` $= O(V)(R) = \{g \in \mathrm{GL}_n(R) : g^{\mathsf T} H g = H\}$ for an $F$-algebra $R$ ($F$, $F_\mathfrak p$);
* `glImage γ L` $= \gamma L$ for $\gamma \in \mathrm{GL}_n(F)$ and `locAct g M` $= gM$ for $g \in \mathrm{GL}_n(F_\mathfrak p)$;
* `IsIsometric Q L M`: $M = \gamma L$ for some $\gamma \in O(V)(F)$ (same **class**);
* `SameGenus Q L M`: for every finite prime $\mathfrak p$, $M_\mathfrak p = g_\mathfrak p L_\mathfrak p$ for some
  $g_\mathfrak p \in O(V)(F_\mathfrak p)$ (same **genus**; at the infinite places both lattices span the same space
  $V \otimes F_w$, so there is no further condition);
* `autLat Q L` $= O(L) = \{\gamma \in O(V)(F) : \gamma L = L\}$ (the **automorphism group** $\mathrm{Aut}(L)$);
* `IsIntegral Q L`: $Q(L) \subseteq \mathcal O_F$.

**Proves** that classes lie in genera (`IsIsometric.sameGenus`), that both are equivalence relations,
$(\gamma L)_\mathfrak p = \gamma L_\mathfrak p$ (`loc_glImage`), that $\gamma \in O(V)(F)$ stabilizes $\mathfrak o_\mathfrak p^n$ for
almost all $\mathfrak p$ (`eventually_locAct_std`). That integrality is a genus invariant is
`SameGenus.isIntegral` (`Lattices/Finite.lean`).

*Conventions:* $O(V)$ includes improper isometries ($\det = -1$), as `Siegel.Aut` does for $F = \mathbb Q$.
O'Meara 1963, §82 (classes, $O(L)$), §102 (genus) [unverified]; for $F = \mathbb Q$ the AWS notes §4.5
(`AWS.latGenus`, `AWS.autLat`).
-/
import QuadFormsKB.Lattices.Local

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-! ### The orthogonal group -/

section Orth

variable (Q : QuadForm F n)

/-- **The orthogonal group** $O(V)(R) = \{g \in \mathrm{GL}_n(R) : g^{\mathsf T} H g = H\}$ of $(F^n, Q)$ over an
$F$-algebra $R$, with $H$ = `Q.hessian` the Hessian of $Q$ (so $Q(x) = \tfrac12 x^{\mathsf T} H x$). For $R = F$ or
$F_\mathfrak p$ this is the group of $g$ with $Q(gx) = Q(x)$ (`mem_orthGroup_iff_eval`). -/
@[kb "omeara1963" "§42, O(V) [unverified]"]
def orthGroup (R : Type*) [CommRing R] [Algebra F R] : Subgroup (GL (Fin n) R) where
  carrier := {g | g.valᵀ * Q.hessian.map (algebraMap F R) * g.val = Q.hessian.map (algebraMap F R)}
  mul_mem' {a b} ha hb := by
    change a.valᵀ * _ * a.val = _ at ha
    change b.valᵀ * _ * b.val = _ at hb
    change (a * b).valᵀ * _ * (a * b).val = _
    rw [Units.val_mul, transpose_mul]
    calc b.valᵀ * a.valᵀ * Q.hessian.map (algebraMap F R) * (a.val * b.val)
        = b.valᵀ * (a.valᵀ * Q.hessian.map (algebraMap F R) * a.val) * b.val := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]
  one_mem' := by change (1 : GL (Fin n) R).valᵀ * _ * (1 : GL (Fin n) R).val = _; simp
  inv_mem' {a} ha := by
    change a.valᵀ * _ * a.val = _ at ha
    change a⁻¹.valᵀ * _ * a⁻¹.val = _
    calc a⁻¹.valᵀ * Q.hessian.map (algebraMap F R) * a⁻¹.val
        = a⁻¹.valᵀ * (a.valᵀ * Q.hessian.map (algebraMap F R) * a.val) * a⁻¹.val := by rw [ha]
      _ = (a.val * a⁻¹.val)ᵀ * Q.hessian.map (algebraMap F R) * (a.val * a⁻¹.val) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.mul_inv]; simp

theorem mem_orthGroup {R : Type*} [CommRing R] [Algebra F R] {g : GL (Fin n) R} :
    g ∈ orthGroup Q R ↔ g.valᵀ * Q.hessian.map (algebraMap F R) * g.val = Q.hessian.map (algebraMap F R) :=
  Iff.rfl

/-- $Q(x)$ in terms of the Hessian: $2\,Q(x) = x^{\mathsf T} H x$ over any $F$-algebra. -/
theorem two_mul_evalIn {R : Type*} [CommRing R] [Algebra F R] (x : Fin n → R) :
    2 * Q.evalIn R x = x ⬝ᵥ (Q.hessian.map (algebraMap F R) *ᵥ x) := by
  rw [QuadForm.evalIn_eq_dotProduct, QuadForm.hessian, Matrix.map_add _ (map_add _), add_mulVec, dotProduct_add,
    Matrix.transpose_map, mulVec_transpose, dotProduct_comm x (vecMul x _), ← dotProduct_mulVec]
  ring

/-- **Isometries preserve $Q$:** for $g \in O(V)(R)$, $Q(gx) = Q(x)$ (over an $F$-algebra $R$ in which $2$ is not a
zero divisor, e.g. $F$ or $F_\mathfrak p$). -/
theorem evalIn_mulVec_of_mem {R : Type*} [CommRing R] [Algebra F R] [IsDomain R] [CharZero R]
    {g : GL (Fin n) R} (hg : g ∈ orthGroup Q R) (x : Fin n → R) :
    Q.evalIn R (g.val *ᵥ x) = Q.evalIn R x := by
  have h2 : (2 : R) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  rw [two_mul_evalIn, two_mul_evalIn]
  conv_rhs => rw [← (mem_orthGroup Q).mp hg, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]

/-- **Base change of isometries** $O(V)(F) \to O(V)(R)$ (entrywise `algebraMap F R`). -/
def orthMap (R : Type*) [CommRing R] [Algebra F R] : orthGroup Q F →* orthGroup Q R where
  toFun γ := ⟨GeneralLinearGroup.map (algebraMap F R) (γ : GL (Fin n) F), by
    have hγ := (mem_orthGroup Q).mp γ.2
    rw [mem_orthGroup]
    have : ((GeneralLinearGroup.map (algebraMap F R) (γ : GL (Fin n) F)).val) =
        (γ : GL (Fin n) F).val.map (algebraMap F R) := rfl
    rw [this, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    have e : Q.hessian.map (algebraMap F F) = Q.hessian := by simp
    rw [e] at hγ
    exact congrArg (·.map (algebraMap F R)) hγ⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp

@[simp] theorem orthMap_val (R : Type*) [CommRing R] [Algebra F R] (γ : orthGroup Q F) :
    ((orthMap Q R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      (γ : GL (Fin n) F).val.map (algebraMap F R) := rfl

end Orth

/-! ### Images of lattices -/

/-- **The image** $\gamma L$ of an $\mathcal O_F$-submodule $L \subseteq F^n$ under $\gamma \in \mathrm{GL}_n(F)$. -/
def glImage (γ : GL (Fin n) F) (L : Submodule (𝓞 F) (Fin n → F)) : Submodule (𝓞 F) (Fin n → F) :=
  L.map ((Matrix.mulVecLin γ.val).restrictScalars (𝓞 F))

theorem mem_glImage {γ : GL (Fin n) F} {L : Submodule (𝓞 F) (Fin n → F)} {x : Fin n → F} :
    x ∈ glImage γ L ↔ ∃ y ∈ L, γ.val *ᵥ y = x := Iff.rfl

theorem mulVec_mem_glImage {γ : GL (Fin n) F} {L : Submodule (𝓞 F) (Fin n → F)} {y : Fin n → F}
    (hy : y ∈ L) : γ.val *ᵥ y ∈ glImage γ L := ⟨y, hy, rfl⟩

theorem glImage_one (L : Submodule (𝓞 F) (Fin n → F)) : glImage 1 L = L := by
  ext x; simp [glImage]

theorem glImage_mul (γ δ : GL (Fin n) F) (L : Submodule (𝓞 F) (Fin n → F)) :
    glImage (γ * δ) L = glImage γ (glImage δ L) := by
  ext x
  simp only [glImage, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
    Units.val_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨δ.val *ᵥ y, ⟨y, hy, rfl⟩, by rw [mulVec_mulVec]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, by rw [mulVec_mulVec]⟩

/-- $\mathrm{GL}_n$ acts surjectively: $\gamma(\gamma^{-1}x) = x$. -/
theorem mulVec_inv_mulVec {R : Type*} [CommRing R] (g : GL (Fin n) R) (x : Fin n → R) :
    g.val *ᵥ (g⁻¹.val *ᵥ x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

/-- **The image of a lattice is a lattice.** -/
theorem glImage_isLattice (γ : GL (Fin n) F) {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) :
    (glImage γ L).IsLattice F where
  fg := hL.fg.map _
  span_eq_top := by
    rw [glImage, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image,
      hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact fun x => ⟨γ⁻¹.val *ᵥ x, mulVec_inv_mulVec γ x⟩

/-! ### The local action -/

section LocalAction

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The action of $\mathrm{GL}_n(F_\mathfrak p)$ on $\mathfrak o_\mathfrak p$-submodules** of $F_\mathfrak p^n$: $g \cdot M = gM$. -/
def locAct (g : GL (Fin n) Fv) (M : Submodule 𝔬 (Fin n → Fv)) : Submodule 𝔬 (Fin n → Fv) :=
  M.map ((Matrix.mulVecLin g.val).restrictScalars 𝔬)

variable {v}

theorem mem_locAct {g : GL (Fin n) Fv} {M : Submodule 𝔬 (Fin n → Fv)} {x : Fin n → Fv} :
    x ∈ locAct v g M ↔ ∃ y ∈ M, g.val *ᵥ y = x := Iff.rfl

theorem locAct_one (M : Submodule 𝔬 (Fin n → Fv)) : locAct v 1 M = M := by
  ext x; simp [locAct]

theorem locAct_mul (g h : GL (Fin n) Fv) (M : Submodule 𝔬 (Fin n → Fv)) :
    locAct v (g * h) M = locAct v g (locAct v h M) := by
  ext x
  simp only [locAct, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
    Units.val_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨h.val *ᵥ y, ⟨y, hy, rfl⟩, by rw [mulVec_mulVec]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, by rw [mulVec_mulVec]⟩

theorem locAct_inv_locAct (g : GL (Fin n) Fv) (M : Submodule 𝔬 (Fin n → Fv)) :
    locAct v g⁻¹ (locAct v g M) = M := by
  rw [← locAct_mul, inv_mul_cancel, locAct_one]

theorem locAct_eq_iff {g : GL (Fin n) Fv} {M N : Submodule 𝔬 (Fin n → Fv)} :
    locAct v g M = N ↔ M = locAct v g⁻¹ N := by
  constructor
  · rintro rfl; rw [locAct_inv_locAct]
  · rintro rfl; rw [← locAct_mul, mul_inv_cancel, locAct_one]

/-- **The image of a local lattice is a local lattice.** -/
theorem locAct_isLattice (g : GL (Fin n) Fv) {M : Submodule 𝔬 (Fin n → Fv)} (hM : M.IsLattice Fv) :
    (locAct v g M).IsLattice Fv where
  fg := hM.fg.map _
  span_eq_top := by
    rw [locAct, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image,
      hM.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact fun x => ⟨g⁻¹.val *ᵥ x, mulVec_inv_mulVec g x⟩

variable (v) in
/-- The coordinatewise embedding commutes with matrices: $\iota(\gamma y) = \gamma\,\iota(y)$. -/
theorem locVec_mulVec (γ : Matrix (Fin n) (Fin n) F) (y : Fin n → F) :
    locVec v (γ *ᵥ y) = γ.map (algebraMap F Fv) *ᵥ locVec v y := by
  funext i
  simp only [locVec_apply]
  exact RingHom.map_mulVec (algebraMap F Fv) γ y i

variable (v) in
/-- **Localization commutes with images:** $(\gamma L)_\mathfrak p = \gamma L_\mathfrak p$. -/
theorem loc_glImage (γ : GL (Fin n) F) (L : Submodule (𝓞 F) (Fin n → F)) :
    loc v (glImage γ L) = locAct v (GeneralLinearGroup.map (algebraMap F Fv) γ) (loc v L) := by
  rw [loc, locAct, loc, Submodule.map_span]
  congr 1
  ext x
  simp only [glImage, Submodule.map_coe, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
    Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨locVec v y, ⟨y, hy, rfl⟩, (locVec_mulVec v _ y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨γ.val *ᵥ y, ⟨y, hy, rfl⟩, locVec_mulVec v _ y⟩

variable (v) in
/-- $(\mathcal O_F^n)_\mathfrak p = \mathfrak o_\mathfrak p^n$. -/
theorem loc_intVec : loc v (intVec : Submodule (𝓞 F) (Fin n → F)) = std v := by
  refine loc_eq_std_of_not_mem v (d := 1) (fun x hx => by rwa [one_smul])
    (fun x hx => by rwa [one_smul]) ?_
  intro h; exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

end LocalAction

/-- $\mathcal O_F^n$ is a lattice. -/
theorem intVec_isLattice : (intVec : Submodule (𝓞 F) (Fin n → F)).IsLattice F :=
  isLattice_of_global_bounds one_ne_zero (fun x hx => by rwa [one_smul]) (fun x hx => by rwa [one_smul])

/-- **A rational $\gamma \in \mathrm{GL}_n(F)$ stabilizes $\mathfrak o_\mathfrak p^n$ for almost all $\mathfrak p$**
(apply `loc_eventually_std` to the lattice $\gamma\,\mathcal O_F^n$). -/
theorem eventually_locAct_std (γ : GL (Fin n) F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      locAct v (GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ) (std v) = std v := by
  filter_upwards [loc_eventually_std (glImage_isLattice γ intVec_isLattice)] with v hv
  have := loc_glImage v γ intVec
  rw [loc_intVec, hv] at this
  exact this.symm

/-! ### Classes, the genus, automorphism groups -/

section Genus

variable (Q : QuadForm F n)

/-- **Isometric lattices (same class)** in $(V, Q) = (F^n, Q)$: $M = \gamma L$ for some isometry
$\gamma \in O(V)(F)$ (O'Meara §82 [unverified]; AWS notes p. 62 for $F = \mathbb Q$). -/
@[kb "omeara1963" "§82, cls L [unverified]"]
def IsIsometric (L M : Submodule (𝓞 F) (Fin n → F)) : Prop :=
  ∃ γ ∈ orthGroup Q F, glImage γ L = M

/-- **Same genus** in $(V, Q)$: for every finite prime $\mathfrak p$ of $F$ there is a local isometry
$g_\mathfrak p \in O(V)(F_\mathfrak p)$ with $g_\mathfrak p L_\mathfrak p = M_\mathfrak p$ (O'Meara §102 [unverified];
for $F = \mathbb Q$, `AWS.latGenus`). At an infinite place $w$, both $L$ and $M$ span the same space $V \otimes F_w$, so
"$L_w \cong M_w$" holds automatically and is not part of the definition. -/
@[kb "omeara1963" "§102, gen L [unverified]"]
def SameGenus (L M : Submodule (𝓞 F) (Fin n → F)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ g ∈ orthGroup Q (v.adicCompletion F), locAct v g (loc v L) = loc v M

/-- **The automorphism group** $O(L) = \mathrm{Aut}(L) = \{\gamma \in O(V)(F) : \gamma L = L\}$ (O'Meara §82
[unverified]; `AWS.autLat` for $F = \mathbb Q$). -/
@[kb "omeara1963" "§82, O(L) [unverified]"]
def autLat (L : Submodule (𝓞 F) (Fin n → F)) : Subgroup (orthGroup Q F) where
  carrier := {γ | glImage (γ : GL (Fin n) F) L = L}
  mul_mem' {a b} ha hb := by
    change glImage (((a * b : orthGroup Q F)) : GL (Fin n) F) L = L
    rw [Subgroup.coe_mul, glImage_mul, show glImage (b : GL (Fin n) F) L = L from hb]; exact ha
  one_mem' := glImage_one L
  inv_mem' {a} ha := by
    change glImage (((a⁻¹ : orthGroup Q F)) : GL (Fin n) F) L = L
    rw [Subgroup.coe_inv]
    conv_lhs => rw [← show glImage (a : GL (Fin n) F) L = L from ha]
    rw [← glImage_mul, inv_mul_cancel, glImage_one]

theorem mem_autLat {L : Submodule (𝓞 F) (Fin n → F)} {γ : orthGroup Q F} :
    γ ∈ autLat Q L ↔ glImage (γ : GL (Fin n) F) L = L := Iff.rfl

/-- **Integral lattice:** $Q(x) \in \mathcal O_F$ for every $x \in L$. -/
@[kb "omeara1963" "§82 (integral lattice) [unverified]"]
def IsIntegral (L : Submodule (𝓞 F) (Fin n → F)) : Prop :=
  ∀ x ∈ L, Q.evalIn F x ∈ (algebraMap (𝓞 F) F).range

theorem IsIsometric.refl (L : Submodule (𝓞 F) (Fin n → F)) : IsIsometric Q L L :=
  ⟨1, (orthGroup Q F).one_mem, glImage_one L⟩

theorem IsIsometric.symm {L M : Submodule (𝓞 F) (Fin n → F)} (h : IsIsometric Q L M) :
    IsIsometric Q M L := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact ⟨γ⁻¹, (orthGroup Q F).inv_mem hγ, by rw [← glImage_mul, inv_mul_cancel, glImage_one]⟩

theorem IsIsometric.trans {L M N : Submodule (𝓞 F) (Fin n → F)} (h : IsIsometric Q L M)
    (h' : IsIsometric Q M N) : IsIsometric Q L N := by
  obtain ⟨γ, hγ, rfl⟩ := h
  obtain ⟨δ, hδ, rfl⟩ := h'
  exact ⟨δ * γ, (orthGroup Q F).mul_mem hδ hγ, glImage_mul _ _ _⟩

theorem SameGenus.refl (L : Submodule (𝓞 F) (Fin n → F)) : SameGenus Q L L :=
  fun _ => ⟨1, Subgroup.one_mem _, locAct_one _⟩

theorem SameGenus.symm {L M : Submodule (𝓞 F) (Fin n → F)} (h : SameGenus Q L M) :
    SameGenus Q M L := by
  intro v
  obtain ⟨g, hg, he⟩ := h v
  exact ⟨g⁻¹, Subgroup.inv_mem _ hg, (locAct_eq_iff.mp he).symm⟩

theorem SameGenus.trans {L M N : Submodule (𝓞 F) (Fin n → F)} (h : SameGenus Q L M)
    (h' : SameGenus Q M N) : SameGenus Q L N := by
  intro v
  obtain ⟨g, hg, he⟩ := h v
  obtain ⟨g', hg', he'⟩ := h' v
  exact ⟨g' * g, Subgroup.mul_mem _ hg' hg, by rw [locAct_mul, he, he']⟩

/-- **A class lies in a genus:** isometric lattices are in the same genus (localize the global isometry). -/
@[kb "omeara1963" "§102 [unverified]"]
theorem IsIsometric.sameGenus {L M : Submodule (𝓞 F) (Fin n → F)} (h : IsIsometric Q L M) :
    SameGenus Q L M := by
  obtain ⟨γ, hγ, rfl⟩ := h
  intro v
  exact ⟨orthMap Q (v.adicCompletion F) ⟨γ, hγ⟩, (orthMap Q _ ⟨γ, hγ⟩).2,
    (loc_glImage v γ L).symm⟩

end Genus

end QuadFormsKB.Lattices
