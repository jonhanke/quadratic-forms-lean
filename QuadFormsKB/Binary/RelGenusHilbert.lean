import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelGenus
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Literature.LocalGlobal.NumberFieldLocal
import QuadFormsKB.Literature.HasseNorm.LocalIndexTwo

/-!
# Genus characters over $F$ by Hilbert symbols, at every place

Let $E/F$ be a quadratic extension of number fields, $\sigma$ its nontrivial automorphism (`conj`). We fix once and
for all an element $\theta \in \mathcal O_E$ with $\sigma(\theta) = -\theta \ne 0$ (`relGen`, e.g. $\theta = y - \sigma(y)$ for any
$y \in \mathcal O_E \setminus \mathcal O_F$) and put $\delta = \theta^2 \in F^\times$ (`relD`), so $E = F(\sqrt\delta)$.

* **Norms** (`exists_norm_eq_sq_sub`, `norm_add_mul_relGen`): $N_{E/F}(u + w\theta) = u^2 - \delta w^2$, and every $z \in E$ is
  $u + w\theta$ with $u, w \in F$; so $N(E^\times) = \{u^2 - \delta w^2 \ne 0\}$, and $x \in F^\times$ is a norm iff $(\delta, x)_F = 1$
  (`hilbertSymbol_relD_eq_one_iff`).
* **The genus character at a place $v$** (`genusSym`): $\psi_v(x) = (\delta, x)_v$ for $x \in F^\times$, the Hilbert symbol over
  the completion $F_v$, at **every** place: finite, dyadic or not, and infinite. Its kernel is the local norm group
  $\{u^2 - \delta w^2\} \subseteq F_v^\times$ of $F_v(\sqrt\delta)/F_v$ (`genusSym_eq_one_iff`; for $v$ finite this is the norm group of
  $F_v \otimes_F E$, `HN.mem_range_norm_iff`), and $\psi_v$ is multiplicative (`genusSym_mul`; the proved local
  multiplicativity `NFInputs.hilbertSymbol_mul_left_finite_nf`, `NFLocal.hilbertSymbol_mul_left_infinite_nf`).
* **Well defined on lattices** (`genusSym_mul_norm`, `genusSym_lattice_eq`): $\psi_v(c\,N(x)) = \psi_v(c)$ for all $x \in E^\times$,
  so on the space $(E, cN)$ — and on every lattice in it — $\psi_v$ takes the same value $\psi_v(c)$ on **every** nonzero
  represented value, with no "prime to $\mathfrak p$" condition. For the normalized lattice $(\mathfrak A, \tfrac{\eta}{a}N)$
  ($N\mathfrak A = (a)$, $\eta \in \mathcal O_F^\times$), $\psi_v = \psi_v(\eta a)$ (`genusSym_normalized`).
* **The product formula** (`genusSym_reciprocity`): $\psi_v(x) = -1$ at finitely many $v$, an even number of them, i.e.
  $\prod_v\psi_v(x) = 1$ — `hilbert_reciprocity_nf`.
* **Genus = local equivalence of the spaces** (`genusSym_eq_iff_exists_norm`, `isometryEquiv_iff_genusSym`,
  `representsIn_iff_genusSym`): for $c, c' \in F^\times$ the following are equivalent:
  $\psi_v(c) = \psi_v(c')$ at every $v$; $c/c' \in N(E^\times)$; $(E, cN) \cong (E, c'N)$ over $F$; and, place by place,
  $\langle c, -c\delta\rangle$ (which is $(E, cN)$ in the basis $1, \theta$, `normForm_basis`) represents $c'$ over $F_v$ iff
  $\psi_v(c) = \psi_v(c')$. The global step is the **Hasse norm theorem** (`NFInputs.hilbert_eq_one_of_everywhere_nf`, proved
  in the repository); everything else is local.

*Comparison with `RelGenus`* (`RelGenus.quadraticChar_eq`): at an odd ramified $\mathfrak p$ the character is the residue symbol of a
represented value prime to $\mathfrak p$; here the character is defined at every place, by Hilbert symbols, and well-definedness
is the one-line identity $c\,N(x)\cdot c = N(cx)$. The identification of the two at odd ramified $\mathfrak p$ (via
$(\delta, s)_\mathfrak p = (s/\mathfrak p)$ for $v_\mathfrak p(\delta)$ odd, $s$ a unit) is not formalized.

Sources: O'Meara, *Introduction to Quadratic Forms*, §63 (Hilbert symbol, local norm groups) and §65 (Hasse norm theorem)
[unverified locators]; Serre, *A Course in Arithmetic*, Ch. III §1 (Hilbert symbol, $x$ norm iff $(a,x) = 1$); Shimura,
*Arithmetic of Quadratic Forms* (2010), §4 [unverified locator]; Cox, *Primes of the form $x^2+ny^2$*, §3 and Thm. 3.15 (the
case $F = \mathbb Q$).
-/

open NumberField Module IsDedekindDomain
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB

/-! ### Hilbert symbols at a place: multiplicativity and norms -/

namespace NFPlace

variable {F : Type} [Field F] [NumberField F]

/-- **The local Hilbert symbol is multiplicative in its second argument**, at every place $v$ of $F$:
$(a, bc)_v = (a, b)_v\,(a, c)_v$ for $a, b, c \in F^\times$. -/
@[kb "omeara1963" "§63:11 [unverified]; serre1973 Ch. III §1.2"]
theorem hilbert_mul_right (v : NFPlace F) {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    v.hilbert a (b * c) = v.hilbert a b * v.hilbert a c := by
  cases v with
  | infinite w =>
    simp only [hilbert, map_mul]
    rw [hilbertSymbol_comm, NFLocal.hilbertSymbol_mul_left_infinite_nf w _ _ _
      ((map_ne_zero _).mpr hb) ((map_ne_zero _).mpr hc) ((map_ne_zero _).mpr ha),
      hilbertSymbol_comm _ (algebraMap F _ b), hilbertSymbol_comm _ (algebraMap F _ c)]
  | finite v =>
    simp only [hilbert, map_mul]
    rw [hilbertSymbol_comm, NFInputs.hilbertSymbol_mul_left_finite_nf v _ _ _
      ((map_ne_zero _).mpr hb) ((map_ne_zero _).mpr hc) ((map_ne_zero _).mpr ha),
      hilbertSymbol_comm _ (algebraMap F _ b), hilbertSymbol_comm _ (algebraMap F _ c)]

/-- A local Hilbert symbol is $\pm 1$. -/
theorem hilbert_eq_one_or (v : NFPlace F) (a b : F) : v.hilbert a b = 1 ∨ v.hilbert a b = -1 := by
  cases v <;> exact HN.hilbertSymbol_eq_one_or _ _ _

/-- **Global norms are local norms:** $(a, x_0^2 - a x_1^2)_v = 1$ at every place. -/
theorem hilbert_eq_one_of_norm (v : NFPlace F) {a b : F} (x₀ x₁ : F) (h : b = x₀ ^ 2 - a * x₁ ^ 2) :
    v.hilbert a b = 1 := by
  cases v <;>
  · simp only [hilbert]
    exact HN.hilbertSymbol_eq_one_of_norm _ _ _ (algebraMap F _ x₀) (algebraMap F _ x₁)
      (by rw [h, map_sub, map_mul, map_pow, map_pow])

/-- $(a, b)_v = 1 \iff b = x_0^2 - a x_1^2$ in $F_v$: the kernel of $(a, \cdot)_v$ is the local norm group of $F_v(\sqrt a)/F_v$. -/
theorem hilbert_eq_one_iff (v : NFPlace F) {a : F} (ha : a ≠ 0) (b : F) :
    v.hilbert a b = 1 ↔ v.atPlace fun K _ _ =>
      ∃ x₀ x₁ : K, algebraMap F K b = x₀ ^ 2 - algebraMap F K a * x₁ ^ 2 := by
  have h2 : ∀ (K : Type) [Field K] [Algebra F K], (2 : K) ≠ 0 := fun K _ _ => by
    rw [show (2 : K) = algebraMap F K 2 from (map_ofNat _ 2).symm]
    exact (map_ne_zero _).mpr two_ne_zero
  cases v with
  | infinite w =>
    exact HN.hilbertSymbol_eq_one_iff_norm _ (h2 _) ((map_ne_zero _).mpr ha)
  | finite v =>
    exact HN.hilbertSymbol_eq_one_iff_norm _ (h2 _) ((map_ne_zero _).mpr ha)

end NFPlace

namespace Binary.Rel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-! ### $E = F(\sqrt\delta)$ -/

theorem conj_algebraMap (a : F) : conj F E (algebraMap F E a) = algebraMap F E a :=
  (conj F E).commutes a

variable (F E) in
theorem exists_relGen : ∃ θ : 𝓞 E, conj F E (θ : E) = -(θ : E) ∧ (θ : E) ≠ 0 := by
  by_contra h
  push Not at h
  -- every element of 𝓞 E is fixed by σ
  have hfix : ∀ y : 𝓞 E, conj F E (algebraMap (𝓞 E) E y) = algebraMap (𝓞 E) E y := by
    intro y
    have hc : conj F E (algebraMap (𝓞 E) E (y - conjO F E y)) =
        -(algebraMap (𝓞 E) E (y - conjO F E y)) := by
      rw [map_sub, map_sub, algebraMap_conjO, conj_conj]; ring
    have := h _ hc
    change algebraMap (𝓞 E) E (y - conjO F E y) = 0 at this
    rw [map_sub, algebraMap_conjO, sub_eq_zero] at this
    exact this.symm
  apply conj_ne_one (F := F) (E := E)
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  simp only [AlgEquiv.one_apply, map_div₀]
  rw [hfix, hfix]

variable (F E) in
/-- **A generator $\theta$ of $E/F$ with $\sigma(\theta) = -\theta \ne 0$**, $\theta \in \mathcal O_E$ (a fixed choice). -/
@[kb "neukirch1999" "Ch. I §2 (quadratic extensions) [unverified]"]
def relGen : 𝓞 E := (exists_relGen F E).choose

theorem conj_relGen : conj F E (relGen F E : E) = -(relGen F E : E) := (exists_relGen F E).choose_spec.1

theorem relGen_ne_zero : (relGen F E : E) ≠ 0 := (exists_relGen F E).choose_spec.2

theorem exists_relD : ∃ δ : F, algebraMap F E δ = (relGen F E : E) ^ 2 :=
  (conj_eq_self_iff _).mp (by rw [map_pow, conj_relGen]; ring)

variable (F E) in
/-- **$\delta = \theta^2 \in F^\times$**, so that $E = F(\sqrt\delta)$ (`relGen`; $\delta$ is a fixed choice in its class
$\delta F^{\times 2}$). -/
@[kb "neukirch1999" "Ch. I §2 (quadratic extensions) [unverified]"]
def relD : F := (exists_relD (F := F) (E := E)).choose

theorem algebraMap_relD : algebraMap F E (relD F E) = (relGen F E : E) ^ 2 := (exists_relD (F := F) (E := E)).choose_spec

theorem relD_ne_zero : relD F E ≠ 0 := by
  intro h
  have := algebraMap_relD (F := F) (E := E)
  rw [h, map_zero] at this
  exact relGen_ne_zero (pow_eq_zero_iff two_ne_zero |>.mp this.symm)

/-- $N_{E/F}(u + w\theta) = u^2 - \delta w^2$. -/
theorem norm_add_mul_relGen (u w : F) :
    Algebra.norm F (algebraMap F E u + algebraMap F E w * (relGen F E : E)) = u ^ 2 - relD F E * w ^ 2 := by
  apply (algebraMap F E).injective
  rw [algebraMap_norm, map_add, map_mul, conj_algebraMap, conj_algebraMap, conj_relGen, map_sub, map_mul,
    map_pow, map_pow, algebraMap_relD]
  ring

/-- Every $z \in E$ is $u + w\theta$ with $u, w \in F$. -/
theorem exists_eq_add_mul_relGen (z : E) :
    ∃ u w : F, z = algebraMap F E u + algebraMap F E w * (relGen F E : E) := by
  have hθ := relGen_ne_zero (F := F) (E := E)
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨u, hu⟩ := (conj_eq_self_iff ((z + conj F E z) / 2)).mp (by
    rw [map_div₀, map_add, conj_conj, map_ofNat]; ring)
  obtain ⟨w, hw⟩ := (conj_eq_self_iff ((z - conj F E z) / (2 * (relGen F E : E)))).mp (by
    rw [map_div₀, map_sub, conj_conj, map_mul, map_ofNat, conj_relGen]
    field_simp
    ring)
  refine ⟨u, w, ?_⟩
  rw [hu, hw]
  field_simp
  ring

/-- **The norms from $E$:** $N_{E/F}(z) = u^2 - \delta w^2$ for some $u, w \in F$. -/
@[kb "serre1973" "Ch. III §1.1 [unverified]"]
theorem exists_norm_eq_sq_sub (z : E) : ∃ u w : F, Algebra.norm F z = u ^ 2 - relD F E * w ^ 2 := by
  obtain ⟨u, w, rfl⟩ := exists_eq_add_mul_relGen (F := F) z
  exact ⟨u, w, norm_add_mul_relGen u w⟩

/-- **$x \in F^\times$ is a norm from $E$ iff $(\delta, x)_F = 1$.** -/
@[kb "serre1973" "Ch. III §1.1, Prop. 1 [unverified]"]
theorem hilbertSymbol_relD_eq_one_iff (x : F) :
    hilbertSymbol F (relD F E) x = 1 ↔ ∃ z : E, Algebra.norm F z = x := by
  rw [HN.hilbertSymbol_eq_one_iff_norm F two_ne_zero relD_ne_zero]
  constructor
  · rintro ⟨u, w, rfl⟩
    exact ⟨_, norm_add_mul_relGen u w⟩
  · rintro ⟨z, rfl⟩
    exact exists_norm_eq_sq_sub z

/-! ### The genus characters $\psi_v = (\delta, \cdot)_v$ -/

variable (E) in
/-- **The genus character at the place $v$ of $F$:** $\psi_v(x) = (\delta, x)_v$, the Hilbert symbol over the completion $F_v$
($v$ finite — dyadic or not — or infinite), $\delta$ = `relD F E`. -/
@[kb "omeara1963" "§63 [unverified]; Shimura (2010) §4 [unverified]"]
def genusSym (v : NFPlace F) (x : F) : ℤ := v.hilbert (relD F E) x

/-- $\psi_v$ is multiplicative. -/
@[kb "omeara1963" "§63:11 [unverified]"]
theorem genusSym_mul (v : NFPlace F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    genusSym E v (x * y) = genusSym E v x * genusSym E v y :=
  NFPlace.hilbert_mul_right v relD_ne_zero hx hy

theorem genusSym_eq_one_or (v : NFPlace F) (x : F) : genusSym E v x = 1 ∨ genusSym E v x = -1 :=
  NFPlace.hilbert_eq_one_or v _ _

/-- **Global norms are in the kernel of every $\psi_v$.** -/
theorem genusSym_norm (v : NFPlace F) (z : E) : genusSym E v (Algebra.norm F z) = 1 := by
  obtain ⟨u, w, h⟩ := exists_norm_eq_sq_sub (F := F) z
  exact NFPlace.hilbert_eq_one_of_norm v u w h

/-- **The kernel of $\psi_v$ is the local norm group:** $\psi_v(x) = 1$ iff $x = u^2 - \delta w^2$ with $u, w \in F_v$, i.e. iff $x$ is a
norm from $F_v(\sqrt\delta)$ (from $F_v \otimes_F E$; for finite $v$ see `HN.mem_range_norm_iff`). -/
@[kb "serre1973" "Ch. III §1.1, Prop. 1 [unverified]; omeara1963 §63 [unverified]"]
theorem genusSym_eq_one_iff (v : NFPlace F) (x : F) :
    genusSym E v x = 1 ↔ v.atPlace fun K _ _ =>
      ∃ u w : K, algebraMap F K x = u ^ 2 - algebraMap F K (relD F E) * w ^ 2 :=
  NFPlace.hilbert_eq_one_iff v relD_ne_zero x

/-- **$\psi_v$ is constant on the nonzero values of $(E, cN)$:** $\psi_v(c\,N(x)) = \psi_v(c)$ for $c \in F^\times$, $x \in E^\times$, at every
place $v$. Hence the genus character of any lattice $L$ on the space $(E, cN)$ — its value on any nonzero represented
value — is well defined and equals $\psi_v(c)$. -/
@[kb "omeara1963" "§82 [unverified]; Shimura (2010) §4 [unverified]; cf. genusChar_eval_eq_formChar"]
theorem genusSym_mul_norm (v : NFPlace F) {c : F} (hc : c ≠ 0) {x : E} (hx : x ≠ 0) :
    genusSym E v (c * Algebra.norm F x) = genusSym E v c := by
  rw [genusSym_mul v hc (Algebra.norm_ne_zero_iff.mpr hx), genusSym_norm, mul_one]

/-- **Two represented values have the same character:** $\psi_v(c\,N(x)) = \psi_v(c\,N(y))$ for $x, y \in E^\times$ (every place,
including dyadic and infinite ones). -/
@[kb "omeara1963" "§82 [unverified]; Shimura (2010) §4 [unverified]; cf. genusChar_eval_eq_formChar"]
theorem genusSym_lattice_eq (v : NFPlace F) {c : F} (hc : c ≠ 0) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    genusSym E v (c * Algebra.norm F x) = genusSym E v (c * Algebra.norm F y) := by
  rw [genusSym_mul_norm v hc hx, genusSym_mul_norm v hc hy]

/-- **The genus character of a normalized lattice.** Let $\mathfrak A \ne 0$ with $N_{E/F}\mathfrak A = (a)$, $\eta \in F^\times$, and
$x \in \mathfrak A \setminus 0$ with $N(x) = as$ (so $\eta s$ is the value at $x$ of the normalized form $\frac\eta a N$). Then
$\psi_v(\eta s) = \psi_v(\eta a)$ at every place $v$: the character does not depend on $x$, and needs no "prime to $\mathfrak p$". -/
@[kb "omeara1963" "§82 [unverified]; Shimura (2010) §4 [unverified]; cf. genusChar_eval_eq_formChar"]
theorem genusSym_normalized (v : NFPlace F) {a s : 𝓞 F} (ha : a ≠ 0) {η : F} (hη : η ≠ 0) {x : 𝓞 E}
    (hx : x ≠ 0) (hs : Algebra.intNorm (𝓞 F) (𝓞 E) x = a * s) :
    genusSym E v (η * (s : F)) = genusSym E v (η * (a : F)) := by
  have ha' : (a : F) ≠ 0 := by exact_mod_cast ha
  have hxE : (x : E) ≠ 0 := algebraMap_ne_zero hx
  have hN : nrm (F := F) x = (a : F) * s := by
    rw [← algebraMap_intNorm', hs]; push_cast; rfl
  -- η s = (η a) · N(x) · a⁻²  and a⁻² = N(a⁻¹)
  have key : η * (s : F) = η * a * Algebra.norm F ((x : E) * algebraMap F E (a : F)⁻¹) := by
    rw [map_mul, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two F E]
    change _ = η * a * (nrm (F := F) x * _)
    rw [hN]
    field_simp
  rw [key, genusSym_mul_norm v (mul_ne_zero hη ha') (mul_ne_zero hxE (by simpa using ha'))]

/-- **The product formula for the genus characters:** for $x \in F^\times$, $\psi_v(x) = -1$ at only finitely many places $v$
and at an even number of them, i.e. $\prod_v \psi_v(x) = 1$ (Hilbert reciprocity over $F$, `hilbert_reciprocity_nf`). -/
@[kb "omeara1963" "§71:18 [unverified]; cf. prod_formChar_eq_one"]
theorem genusSym_reciprocity {x : F} (hx : x ≠ 0) :
    {v : NFPlace F | genusSym E v x = -1}.Finite ∧ Even {v : NFPlace F | genusSym E v x = -1}.ncard :=
  hilbert_reciprocity_nf _ _ relD_ne_zero hx

/-! ### Genus = local equivalence (of the spaces $(E, cN)$) -/

/-- **Equal genus characters iff the ratio is a norm** (the Hasse norm theorem): for $c, c' \in F^\times$,
$\psi_v(c) = \psi_v(c')$ at every place $v$ iff $c = c'\,N(\lambda)$ for some $\lambda \in E^\times$. -/
@[kb "omeara1963" "§65 (Hasse norm theorem) [unverified]; Shimura (2010) §4 [unverified]"]
theorem genusSym_eq_iff_exists_norm {c c' : F} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    (∀ v : NFPlace F, genusSym E v c = genusSym E v c') ↔
      ∃ l : E, l ≠ 0 ∧ c' * Algebra.norm F l = c := by
  constructor
  · intro h
    have hall : ∀ v : NFPlace F, v.hilbert (relD F E) (c * c') = 1 := by
      intro v
      change genusSym E v (c * c') = 1
      rw [genusSym_mul v hc hc', h v]
      rcases genusSym_eq_one_or (E := E) v c' with h1 | h1 <;> rw [h1] <;> norm_num
    have hF := NFInputs.hilbert_eq_one_of_everywhere_nf _ _ relD_ne_zero (mul_ne_zero hc hc') hall
    obtain ⟨z, hz⟩ := (hilbertSymbol_relD_eq_one_iff (E := E) _).mp hF
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hz
      exact mul_ne_zero hc hc' hz.symm
    refine ⟨z * algebraMap F E c'⁻¹, mul_ne_zero hz0 (by simpa using hc'), ?_⟩
    rw [map_mul, hz, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two F E]
    field_simp
  · rintro ⟨l, hl, rfl⟩ v
    exact genusSym_mul_norm v hc' hl

/-- **Genus characters classify the spaces:** $(E, cN) \cong (E, c'N)$ over $F$ iff $\psi_v(c) = \psi_v(c')$ at every place. -/
@[kb "omeara1963" "§§63, 65 [unverified]; Shimura (2010) §4 [unverified]"]
theorem isometryEquiv_iff_genusSym {c c' : F} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    Nonempty ((c • normForm F E).IsometryEquiv (c' • normForm F E)) ↔
      ∀ v : NFPlace F, genusSym E v c = genusSym E v c' := by
  rw [genusSym_eq_iff_exists_norm hc hc']
  constructor
  · rintro ⟨φ⟩
    refine ⟨φ 1, fun h0 => ?_, ?_⟩
    · have := φ.map_app 1
      rw [h0] at this
      simp only [smul_apply, normForm_apply, smul_eq_mul, map_one, mul_one,
        Algebra.norm_zero, mul_zero] at this
      exact hc this.symm
    · have := φ.map_app 1
      simpa only [smul_apply, normForm_apply, smul_eq_mul, map_one, mul_one] using this
  · rintro ⟨l, hl, h⟩
    exact ⟨simIso l hl h false⟩

/-- **Isometric lattices have equal genus characters** (necessity of the characters). -/
@[kb "omeara1963" "§82 [unverified]"]
theorem genusSym_eq_of_isometricLattices {c c' : F} (hc : c ≠ 0) (hc' : c' ≠ 0) {L L' : Submodule (𝓞 F) E}
    (h : Lattices.IsometricLattices (c • normForm F E) (c' • normForm F E) L L') (v : NFPlace F) :
    genusSym E v c = genusSym E v c' := by
  obtain ⟨l, hl, hcl, -⟩ := (isometricLattices_iff hc hc' L L').mp h
  rw [← hcl]
  exact genusSym_mul_norm v hc' hl

/-! ### Place by place: $(E, cN)_v \cong \langle c, -c\delta\rangle$ represents $c'$ iff $\psi_v(c) = \psi_v(c')$ -/

theorem evalIn_diag_two (K : Type*) [Field K] [Algebra F K] (a b : F) (x : Fin 2 → K) :
    (QuadForm.diag ![a, b]).evalIn K x = algebraMap F K a * x 0 ^ 2 + algebraMap F K b * x 1 ^ 2 := by
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal]
  ring

/-- **$(E, cN)$ in the basis $1, \theta$ is $\langle c, -c\delta\rangle$:** $c\,N(u + w\theta) = cu^2 - c\delta w^2$. -/
@[kb "omeara1963" "§57 [unverified]"]
theorem normForm_basis (c u w : F) :
    c * Algebra.norm F (algebraMap F E u + algebraMap F E w * (relGen F E : E)) =
      (QuadForm.diag ![c, -(c * relD F E)]).eval ![u, w] := by
  rw [QuadForm.eval, evalIn_diag_two, norm_add_mul_relGen]
  simp
  ring

theorem diag_representsIn_iff (K : Type) [Field K] [Algebra F K] {c : F} (hc : c ≠ 0) (c' : F) :
    (QuadForm.diag ![c, -(c * relD F E)]).RepresentsIn K c' ↔
      ∃ u w : K, algebraMap F K (c * c') = u ^ 2 - algebraMap F K (relD F E) * w ^ 2 := by
  have hC : algebraMap F K c ≠ 0 := (map_ne_zero _).mpr hc
  constructor
  · rintro ⟨x, hx⟩
    rw [evalIn_diag_two] at hx
    refine ⟨algebraMap F K c * x 0, algebraMap F K c * x 1, ?_⟩
    rw [map_mul, ← hx, map_neg, map_mul]
    ring
  · rintro ⟨u, w, h⟩
    refine ⟨![u / algebraMap F K c, w / algebraMap F K c], ?_⟩
    rw [evalIn_diag_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_mul]
    rw [map_mul] at h
    field_simp
    linear_combination (-1 : K) * h

/-- **Local equivalence at one place:** $\langle c, -c\delta\rangle$ ($= (E, cN)$ in the basis $1, \theta$, `normForm_basis`) represents
$c'$ over $F_v$ iff $\psi_v(c) = \psi_v(c')$; as both spaces have discriminant $-\delta$, this is "$(E, cN) \cong (E, c'N)$ over $F_v$". -/
@[kb "omeara1963" "§63 [unverified]; serre1973 Ch. IV §2.2 [unverified]"]
theorem representsIn_iff_genusSym (v : NFPlace F) {c c' : F} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    v.atPlace (fun K _ _ => (QuadForm.diag ![c, -(c * relD F E)]).RepresentsIn K c') ↔
      genusSym E v c = genusSym E v c' := by
  have key : v.atPlace (fun K _ _ => (QuadForm.diag ![c, -(c * relD F E)]).RepresentsIn K c') ↔
      genusSym E v (c * c') = 1 := by
    rw [genusSym_eq_one_iff]
    cases v with
    | infinite w => exact diag_representsIn_iff (E := E) _ hc c'
    | finite w => exact diag_representsIn_iff (E := E) _ hc c'
  rw [key, genusSym_mul v hc hc']
  rcases genusSym_eq_one_or (E := E) v c with h | h <;>
    rcases genusSym_eq_one_or (E := E) v c' with h' | h' <;> rw [h, h'] <;> norm_num

/-! ### Gauss's principal genus theorem over $F$ -/

section PrincipalGenus

theorem genusSym_one (v : NFPlace F) : genusSym E v 1 = 1 := by
  cases v <;> simp only [genusSym, NFPlace.hilbert, map_one] <;> exact hilbertSymbol_one_right _ _

theorem relNorm_conjIdeal (𝔄 : Ideal (𝓞 E)) :
    Ideal.relNorm (𝓞 F) (conjIdeal F 𝔄) = Ideal.relNorm (𝓞 F) 𝔄 :=
  Ideal.relNorm_map_algEquiv (RingOfIntegers.mapAlgEquiv (conj F E)) 𝔄

theorem conjO_algebraMap (m : 𝓞 F) : conjO F E (algebraMap (𝓞 F) (𝓞 E) m) = algebraMap (𝓞 F) (𝓞 E) m :=
  (RingOfIntegers.mapAlgEquiv (conj F E)).commutes m

theorem conjIdeal_span (x : 𝓞 E) : conjIdeal F (Ideal.span {x}) = Ideal.span {conjO F E x} := by
  rw [conjIdeal, Ideal.map_span, Set.image_singleton]

/-- **The ideal identity behind the principal genus theorem** (an ideal-theoretic Hilbert 90). Let $N\mathfrak A = (a)$ and
$\mu \in \mathcal O_E$, $m \in \mathcal O_F$, $\eta \in \mathcal O_F^\times$ with $N(\mu) = m^2\eta a$. With $\mathfrak C = m\mathfrak A + \mu\mathcal O_E$:
$$m\,\mathfrak A\,\sigma(\mathfrak C) = \sigma(\mu)\,\mathfrak C .$$
(Both sides are $m^2a\,\mathcal O_E + m\,\sigma(\mu)\,\mathfrak A$, by $\mathfrak A\sigma(\mathfrak A) = a\mathcal O_E$ and $\mu\sigma(\mu) = m^2\eta a$.) -/
@[kb "neukirch1999" "Ch. IV §3 (Hilbert 90) [unverified]; hecke1923 §48 [unverified]"]
theorem principal_identity {𝔄 : Ideal (𝓞 E)} {a m : 𝓞 F} (h𝔄 : Ideal.relNorm (𝓞 F) 𝔄 = Ideal.span {a})
    {μ : 𝓞 E} (η : (𝓞 F)ˣ) (hμ : Algebra.intNorm (𝓞 F) (𝓞 E) μ = m ^ 2 * η * a) :
    Ideal.span {algebraMap (𝓞 F) (𝓞 E) m} * 𝔄 *
        conjIdeal F (Ideal.span {algebraMap (𝓞 F) (𝓞 E) m} * 𝔄 + Ideal.span {μ}) =
      Ideal.span {conjO F E μ} * (Ideal.span {algebraMap (𝓞 F) (𝓞 E) m} * 𝔄 + Ideal.span {μ}) := by
  set M := Ideal.span {algebraMap (𝓞 F) (𝓞 E) m}
  have hσ : conjIdeal F (M * 𝔄 + Ideal.span {μ}) = M * conjIdeal F 𝔄 + Ideal.span {conjO F E μ} := by
    rw [Ideal.add_eq_sup, Ideal.add_eq_sup, conjIdeal, Ideal.map_sup, Ideal.map_mul, ← conjIdeal, ← conjIdeal,
      ← conjIdeal, conjIdeal_span, conjIdeal_span, conjO_algebraMap]
  have hA : 𝔄 * conjIdeal F 𝔄 = Ideal.span {algebraMap (𝓞 F) (𝓞 E) a} := by
    rw [mul_conjIdeal, h𝔄, Ideal.map_span, Set.image_singleton]
  have hN : Ideal.span {conjO F E μ} * Ideal.span {μ} = M * M * Ideal.span {algebraMap (𝓞 F) (𝓞 E) a} := by
    rw [Ideal.span_singleton_mul_span_singleton, mul_comm (conjO F E μ), ← algebraMap_intNorm_eq, hμ,
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton,
      show algebraMap (𝓞 F) (𝓞 E) (m ^ 2 * η * a) =
        algebraMap (𝓞 F) (𝓞 E) m * algebraMap (𝓞 F) (𝓞 E) m * algebraMap (𝓞 F) (𝓞 E) a *
          algebraMap (𝓞 F) (𝓞 E) (η : 𝓞 F) by simp only [map_mul, map_pow]; ring,
      Ideal.span_singleton_mul_right_unit ((η.isUnit).map _)]
  rw [hσ]
  calc M * 𝔄 * (M * conjIdeal F 𝔄 + Ideal.span {conjO F E μ})
      = M * M * (𝔄 * conjIdeal F 𝔄) + Ideal.span {conjO F E μ} * (M * 𝔄) := by ring
    _ = Ideal.span {conjO F E μ} * (M * 𝔄) + Ideal.span {conjO F E μ} * Ideal.span {μ} := by
        rw [hA, hN, add_comm]
    _ = _ := by ring

/-- $c\,\sigma_*(c)^{-1} = c^2\,\iota(d)^{-1}$ for some class $d$ of $F$: the classes $\mathrm{Cl}_E^{1-\sigma}$ lie in $\mathrm{Cl}_E^2\,\iota(\mathrm{Cl}_F)$. -/
theorem mul_inv_conjClass (c : ClassGroup (𝓞 E)) :
    ∃ d : ClassGroup (𝓞 F), c * (conjClass F E c)⁻¹ = c ^ 2 * (ClassGroup.extendedHom (𝓞 F) (𝓞 E) d)⁻¹ := by
  obtain ⟨𝔄, rfl⟩ := ClassGroup.mk0_surjective c
  obtain ⟨𝔞, h⟩ := mul_conjClass (F := F) 𝔄
  refine ⟨ClassGroup.mk0 𝔞, ?_⟩
  rw [← h, mul_inv]
  group

/-- **Gauss's principal genus theorem over $F$.** Let $\mathfrak A \ne 0$ be an ideal of $\mathcal O_E$ with $N_{E/F}\mathfrak A = (a)$ principal
(so that the normalized lattices $(\mathfrak A, \frac\eta aN)$, $\eta \in \mathcal O_F^\times$, of `RelGenus` exist). Then
$$[\mathfrak A] \in \mathrm{Cl}_E^{1-\sigma} = \{c\,\sigma_*(c)^{-1}\} \iff \exists\,\eta \in \mathcal O_F^\times:\ \psi_v(\eta a) = 1 \text{ at every place } v,$$
i.e. iff some normalized lattice on $\mathfrak A$ lies in the principal genus. (By `genusSym_eq_iff_exists_norm`, the right
side says $\eta a \in N_{E/F}(E^\times)$; by `mul_inv_conjClass`, $\mathrm{Cl}_E^{1-\sigma} \subseteq \mathrm{Cl}_E^2\,\iota(\mathrm{Cl}_F)$.) Over $\mathbb Q$
($\mathrm{Cl}_\mathbb Q = 1$, $\sigma_*c = c^{-1}$, $\eta = \pm1$ fixed by positivity) this is `principalGenus_eq_sq`. The proof is
local (Hilbert symbols) plus the Hasse norm theorem and the ideal identity `principal_identity`; no class field theory. -/
@[kb "hecke1923" "§48 [unverified]; neukirch1999 Ch. VI §4 [unverified]; cf. principalGenus_eq_sq"]
theorem principalGenus_iff (𝔄 : (Ideal (𝓞 E))⁰) {a : 𝓞 F}
    (h𝔄 : Ideal.relNorm (𝓞 F) (𝔄 : Ideal (𝓞 E)) = Ideal.span {a}) :
    (∃ c : ClassGroup (𝓞 E), ClassGroup.mk0 𝔄 = c * (conjClass F E c)⁻¹) ↔
      ∃ η : (𝓞 F)ˣ, ∀ v : NFPlace F, genusSym E v ((η : F) * (a : F)) = 1 := by
  have h𝔄0 : (𝔄 : Ideal (𝓞 E)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero 𝔄
  have ha : a ≠ 0 := by
    rintro rfl
    rw [Set.singleton_zero, Ideal.span_zero, Ideal.relNorm_eq_bot_iff] at h𝔄
    exact h𝔄0 h𝔄
  have ha' : (a : F) ≠ 0 := by exact_mod_cast ha
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨𝔆, rfl⟩ := ClassGroup.mk0_surjective c
    have h1 : ClassGroup.mk0 (𝔄 * conjIdeal0 F 𝔆) = ClassGroup.mk0 𝔆 := by
      rw [map_mul, ← conjClass_mk0, hc]
      group
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h1
    have h𝔆 : Ideal.relNorm (𝓞 F) (𝔆 : Ideal (𝓞 E)) ≠ ⊥ :=
      Ideal.relNorm_eq_bot_iff.not.mpr (nonZeroDivisors.coe_ne_zero 𝔆)
    have h2 := congrArg (Ideal.relNorm (𝓞 F)) hxy
    simp only [Submonoid.coe_mul, map_mul, Ideal.relNorm_singleton, conjIdeal0, relNorm_conjIdeal,
      h𝔄] at h2
    rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton] at h2
    have h3 := mul_right_cancel₀ h𝔆 h2
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h3
    refine ⟨u, fun v => ?_⟩
    have hxE : (x : E) ≠ 0 := algebraMap_ne_zero hx
    have key : (u : F) * (a : F) * nrm (F := F) x = nrm (F := F) y := by
      have := congrArg (algebraMap (𝓞 F) F) hu
      simp only [map_mul, algebraMap_intNorm'] at this
      rw [← this]
      ring
    have hu0 : (u : F) ≠ 0 := by
      intro h0
      have : ((u : 𝓞 F) : F) = 0 := h0
      exact u.ne_zero (by exact_mod_cast this)
    rw [← genusSym_mul_norm v (mul_ne_zero hu0 ha') hxE]
    change genusSym E v ((u : F) * (a : F) * nrm (F := F) x) = 1
    rw [key]
    exact genusSym_norm v _
  · rintro ⟨η, hη⟩
    have hη0 : ((η : 𝓞 F) : F) ≠ 0 := by
      intro h0
      exact η.ne_zero (by exact_mod_cast h0)
    obtain ⟨l, hl, hl'⟩ := (genusSym_eq_iff_exists_norm (E := E) (mul_ne_zero hη0 ha') one_ne_zero).mp
      (fun v => by rw [hη v, genusSym_one])
    rw [one_mul] at hl'
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) l
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqE : (q : E) ≠ 0 := algebraMap_ne_zero hq0
    have hp0 : p ≠ 0 := by rintro rfl; simp at hl
    let μ : 𝓞 E := p * conjO F E q
    let m : 𝓞 F := Algebra.intNorm (𝓞 F) (𝓞 E) q
    have hpq : (η : F) * (a : F) * nrm (F := F) q = nrm (F := F) p := by
      rw [← hl']
      change _ = Algebra.norm F (algebraMap (𝓞 E) E p)
      rw [nrm, ← map_mul, div_mul_cancel₀ _ (algebraMap_ne_zero hq0)]
    have hμ : Algebra.intNorm (𝓞 F) (𝓞 E) μ = m ^ 2 * η * a := by
      apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      rw [algebraMap_intNorm', nrm_mul]
      have hc : nrm (F := F) (conjO F E q) = nrm (F := F) q := by
        rw [nrm, nrm, algebraMap_conjO, norm_conj]
      rw [hc, map_mul, map_mul, map_pow, algebraMap_intNorm', ← hpq]
      ring
    have hμ0 : μ ≠ 0 := mul_ne_zero hp0 (fun h0 => hq0 ((conjO F E).injective (by rw [h0, map_zero])))
    have hid := principal_identity h𝔄 η hμ
    set 𝔆 : Ideal (𝓞 E) := Ideal.span {algebraMap (𝓞 F) (𝓞 E) m} * 𝔄 + Ideal.span {μ}
    have h𝔆 : 𝔆 ≠ ⊥ := by
      intro h0
      have : μ ∈ 𝔆 := Ideal.mem_sup_right (Ideal.mem_span_singleton_self μ)
      rw [h0, Ideal.mem_bot] at this
      exact hμ0 this
    let 𝔆0 : (Ideal (𝓞 E))⁰ := ⟨𝔆, mem_nonZeroDivisors_of_ne_zero h𝔆⟩
    refine ⟨ClassGroup.mk0 𝔆0, ?_⟩
    have hm0 : algebraMap (𝓞 F) (𝓞 E) m ≠ 0 := by
      intro h0
      have : m = 0 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by rw [h0, map_zero])
      apply nrm_ne_zero (F := F) hq0
      rw [← algebraMap_intNorm']
      change algebraMap (𝓞 F) F m = 0
      rw [this, map_zero]
    have hσμ : conjO F E μ ≠ 0 := by
      intro h0; exact hμ0 ((conjO F E).injective (by rw [h0, map_zero]))
    have h1 : ClassGroup.mk0 (𝔄 * conjIdeal0 F 𝔆0) = ClassGroup.mk0 𝔆0 :=
      ClassGroup.mk0_eq_mk0_iff.mpr ⟨_, _, hm0, hσμ, by
        simp only [Submonoid.coe_mul, conjIdeal0]
        rw [← mul_assoc]
        exact hid⟩
    rw [map_mul, ← conjClass_mk0] at h1
    exact eq_mul_inv_of_mul_eq h1

end PrincipalGenus

end Binary.Rel

end QuadFormsKB
