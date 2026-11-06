/-
# Cassels, Appendix A, Theorem 3.1 (Watson): the class number of a definite genus tends to infinity

**Layer:** integer-valued forms `Q : QuadForm ℤ n` (Cassels' $\phi$ on $\Lambda = \mathbb Z^n$), positive definite
(`IntQF.PosDef`), genus `Siegel.SameGenus`, classes `Siegel.genusClasses`. Isometry classes of lattices are
$\mathrm{GL}_n(\mathbb Z)$-classes of forms (`Siegel.IntEquiv`); an orthogonal sum of forms is `QuadForm.orthSum`.

**Cassels' statement** (p. 364). Let $c(n)$ be the minimum number of classes in a genus of positive definite
integer-valued forms in $n$ variables. Then $c(n) \to \infty$ as $n \to \infty$. (The same holds for spinor genera;
see below.)

**Formalized.**
* `minGenusClasses n` is $c(n)$, valued in `ℕ∞` (so no finiteness of the class number is needed to state it);
* `WatsonStatement` is Theorem 3.1: $c(n) \to \infty$ (`watsonStatement_iff`: for every $N$, eventually every genus
  has at least $N$ classes);
* **proved** (the counting step (3.1)-(3.2), p. 365): `encard_genus_ge`, a genus containing $r\Gamma_8 \perp \Lambda'$ has
  at least $1 + [r/2]$ classes. Ingredients: the lattices $(r - 2j)\Gamma_8 \perp j\Gamma_{16} \perp \Lambda'$ lie in the
  genus (`sameGenus_rep`, from `Lattices.gamma16_sameGenus`; the variable bookkeeping is `IsoOver`, `repE8`, `repG`),
  and they are pairwise non-isometric by Theorem 2.1 (`Lattices.thm_2_1`) applied to $\mathbb Z^n \subset \mathbb Q^n$
  (`SplitCount`: the number of indecomposable summands, `splitCount_unique`, transported along integral isometries by
  `splitCount_of_isometricGL`, additive in orthogonal sums by `splitCount_orthSum`, equal to $1$ for $E_8$ and
  $\Gamma_{16}$ by `e8_indecomposable`, `gamma16_indecomposable`);
* the remaining two steps of the sketch (pp. 365-366), which are not in the library, are named inputs, each a `Prop`
  structure that is not the conclusion:
  * `WatsonOperationMonotone` : the genus of $(\Lambda_p, p^{-1}\phi)$ has at most as many classes as the genus of
    $(\Lambda, \phi)$ (Cassels: "easy to construct", p. 365);
  * `WatsonLocalStudy` : repeated Watson operations lead from any genus in $n$ variables to a genus containing a
    lattice $r\Gamma_8 \perp \Lambda'$ with $16 r \ge n - 6$ (Cassels: "the local study (Ch. 8, Ex. 8) shows ...", p. 366);
* `watson_of_inputs` : the two inputs imply `WatsonStatement`. Proved here: positive definiteness of the Watson
  derived form (`IsWatsonDerived.posDef`), monotonicity of the class number along a chain of operations
  (`WatsonReach.encard_le`), and the final counting.

**Not formalized** (what a full proof needs): (1) `WatsonOperationMonotone` (a local-to-global construction of a lattice
$\Lambda'$ in the genus of $(\Lambda_p, \psi)$ from each class of the genus of $(\Lambda, \phi)$, Cassels' footnote);
(2) `WatsonLocalStudy` (a local classification at the primes $p \mid 2\det$, Ch. 8 Ex. 8, giving the bound
$r \ge (n-6)/16$, confirmed on the page image of p. 366). The spinor-genus version (p. 366) is stated in
`AppA/Statements.lean` (`WatsonSpinor` and its two points, named statements).

*Deviation.* Cassels' "$c(n) \to \infty$" is stated for $c(n) \in \mathbb N$ implicitly (finiteness of class numbers);
here $c(n) \in \mathbb N\cup\{\infty\}$, so the statement is formally the stronger-or-equal one and does not use the
finiteness theorem. The book's $\Gamma_8$ is the $E_8$ form `Siegel.e8` and $\Gamma_{16}$ the form `Lattices.gamma16`.
-/
import QuadFormsKB.Literature.Cassels.AppA.Gamma16Genus
import QuadFormsKB.Literature.Cassels.AppA.Sec3

open NumberField Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.DefiniteForms

open Siegel Lattices


section IsoOver

variable {S : Type*} [CommRing S]

/-- Helper: $A$ and $A'$ are isometric over $S$ (the forms evaluated over $S$), possibly with different
variable counts. -/
def IsoOver (S : Type*) [CommRing S] {a a' : ℕ} (A : QuadForm ℤ a) (A' : QuadForm ℤ a') : Prop :=
  ∃ f : (Fin a → S) ≃ₗ[S] (Fin a' → S), ∀ x, A'.evalIn S (f x) = A.evalIn S x

/-- Helper: $A$ is isometric over $S$ to itself. -/
theorem IsoOver.refl {a : ℕ} (A : QuadForm ℤ a) : IsoOver S A A :=
  ⟨LinearEquiv.refl _ _, fun _ => rfl⟩

/-- Helper: `IsoOver` is symmetric. -/
theorem IsoOver.symm {a a' : ℕ} {A : QuadForm ℤ a} {A' : QuadForm ℤ a'} (h : IsoOver S A A') :
    IsoOver S A' A := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.symm, fun y => by rw [← hf (f.symm y), LinearEquiv.apply_symm_apply]⟩

/-- Helper: `IsoOver` is transitive. -/
theorem IsoOver.trans {a a' a'' : ℕ} {A : QuadForm ℤ a} {A' : QuadForm ℤ a'} {A'' : QuadForm ℤ a''}
    (h : IsoOver S A A') (h' : IsoOver S A' A'') : IsoOver S A A'' := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  exact ⟨f.trans g, fun x => by simp [hg, hf]⟩

/-- Helper: $(\mathrm{Fin}(a+b) \to S) \simeq (\mathrm{Fin}\,a \to S) \times (\mathrm{Fin}\,b \to S)$. -/
def splitEquiv (S : Type*) [CommRing S] (a b : ℕ) :
    (Fin (a + b) → S) ≃ₗ[S] (Fin a → S) × (Fin b → S) where
  toFun x := (fun i => x (Fin.castAdd b i), fun j => x (Fin.natAdd a j))
  invFun p := Fin.append p.1 p.2
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  right_inv p := by
    ext i <;> simp

/-- Helper: `IsoOver` is compatible with orthogonal sums, in both summands. -/
theorem IsoOver.orthSum {a a' b b' : ℕ} {A : QuadForm ℤ a} {A' : QuadForm ℤ a'} {B : QuadForm ℤ b}
    {B' : QuadForm ℤ b'} (h : IsoOver S A A') (h' : IsoOver S B B') :
    IsoOver S (QuadForm.orthSum A B) (QuadForm.orthSum A' B') := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  refine ⟨(splitEquiv S a b).trans ((f.prodCongr g).trans (splitEquiv S a' b').symm), fun x => ?_⟩
  rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum]
  have e1 : (fun i => ((splitEquiv S a b).trans ((f.prodCongr g).trans (splitEquiv S a' b').symm)) x
      (Fin.castAdd b' i)) = f (fun i => x (Fin.castAdd b i)) := by
    funext i; simp [splitEquiv]
  have e2 : (fun i => ((splitEquiv S a b).trans ((f.prodCongr g).trans (splitEquiv S a' b').symm)) x
      (Fin.natAdd a' i)) = g (fun i => x (Fin.natAdd a i)) := by
    funext i; simp [splitEquiv]
  rw [e1, e2, hf, hg]

/-- Helper: transporting a form along an equality of variable counts `h : a = a'` is an isometry. -/
theorem IsoOver.cast {a a' : ℕ} (h : a = a') (A : QuadForm ℤ a) : IsoOver S A (h ▸ A) := by
  subst h; exact IsoOver.refl A

/-- Helper: orthogonal sums are associative up to relabelling the variables. -/
theorem IsoOver.assoc {a b c : ℕ} (A : QuadForm ℤ a) (B : QuadForm ℤ b) (C : QuadForm ℤ c) :
    IsoOver S (QuadForm.orthSum A (QuadForm.orthSum B C)) (QuadForm.orthSum (QuadForm.orthSum A B) C) := by
  refine ⟨LinearEquiv.funCongrLeft S S (finCongr (add_assoc a b c)), fun x => ?_⟩
  simp only [QuadForm.evalIn_orthSum]
  rw [add_assoc]
  have e1 : (fun i => (LinearEquiv.funCongrLeft S S (finCongr (add_assoc a b c))) x
      (Fin.castAdd c (Fin.castAdd b i))) = fun i => x (Fin.castAdd (b + c) i) := by
    funext i; simp [LinearEquiv.funCongrLeft_apply]; congr 1
  have e2 : (fun i => (LinearEquiv.funCongrLeft S S (finCongr (add_assoc a b c))) x
      (Fin.castAdd c (Fin.natAdd a i))) = fun i => x (Fin.natAdd a (Fin.castAdd c i)) := by
    funext i; simp [LinearEquiv.funCongrLeft_apply]; congr 1
  have e3 : (fun i => (LinearEquiv.funCongrLeft S S (finCongr (add_assoc a b c))) x
      (Fin.natAdd (a + b) i)) = fun i => x (Fin.natAdd a (Fin.natAdd b i)) := by
    funext i; simp [LinearEquiv.funCongrLeft_apply]; congr 1; ext; simp; omega
  rw [e1, e2, e3]

/-- Helper: adding a form in $z = 0$ variables does not change a form up to `IsoOver`. -/
theorem IsoOver.orthSum_zero {a z : ℕ} (A : QuadForm ℤ a) (Z : QuadForm ℤ z) (hz : z = 0) :
    IsoOver S A (QuadForm.orthSum A Z) := by
  subst hz
  refine ⟨(LinearEquiv.prodUnique (R := S) (M := Fin a → S) (M₂ := Fin 0 → S)).symm.trans
    (splitEquiv S a 0).symm, fun x => ?_⟩
  rw [QuadForm.evalIn_orthSum]
  have : Z.evalIn S (fun j => ((LinearEquiv.prodUnique (R := S) (M := Fin a → S) (M₂ := Fin 0 → S)).symm.trans
    (splitEquiv S a 0).symm) x (Fin.natAdd a j)) = 0 := by
    simp [QuadForm.evalIn]
  rw [this, add_zero]
  congr 1
  funext i
  simp [splitEquiv]
  exact Fin.append_left _ _ i

end IsoOver

section Rep

/-- $r$ copies of $E_8$. -/
def repE8 : (r : ℕ) → QuadForm ℤ (8 * r)
  | 0 => QuadForm.ofUpper fun _ _ => 0
  | r + 1 => QuadForm.orthSum (repE8 r) e8

/-- $j$ copies of $\gamma_{16}$. -/
def repG : (j : ℕ) → QuadForm ℤ (16 * j)
  | 0 => QuadForm.ofUpper fun _ _ => 0
  | j + 1 => QuadForm.orthSum (repG j) gamma16

variable {S : Type*} [CommRing S]

/-- Helper: if $E_8 \perp E_8$ is isometric to $\gamma_{16}$ over $S$, then $E_8^{k + 2j}$ is isometric to $E_8^k \perp \gamma_{16}^j$ over $S$. Arguments: `H` the isometry $E_8 \perp E_8 \cong \gamma_{16}$, `k` and `j` the copy counts. -/
theorem isoOver_repE8_repG {S : Type*} [CommRing S] (H : IsoOver S (QuadForm.orthSum e8 e8) gamma16) (k j : ℕ) :
    IsoOver S (repE8 (k + 2 * j)) (QuadForm.orthSum (repE8 k) (repG j)) := by
  induction j with
  | zero => exact IsoOver.orthSum_zero (repE8 k) (repG 0) (by simp)
  | succ j ih =>
    exact ((((ih.orthSum (IsoOver.refl e8)).orthSum (IsoOver.refl e8)).trans
      (IsoOver.assoc _ _ _).symm).trans ((IsoOver.refl _).orthSum H)).trans (IsoOver.assoc _ _ _).symm

end Rep

section Genus

variable {S : Type*} [CommRing S]

private theorem map_eval_eq_evalIn' {n : ℕ} (Q : QuadForm ℤ n) (x : Fin n → S) :
    (Q.map (Int.castRingHom S)).eval x = Q.evalIn S x := by
  simp [QuadForm.map, QuadForm.evalIn]

/-- Helper: an invertible matrix as a linear equivalence. -/
def glEquiv {n : ℕ} (g : GL (Fin n) S) : (Fin n → S) ≃ₗ[S] (Fin n → S) :=
  LinearEquiv.ofLinearMap (Matrix.mulVecLin g.val) (Matrix.mulVecLin (g⁻¹).val)
    (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec])
    (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec])

/-- Helper: `glEquiv g` is multiplication by `g`. -/
theorem glEquiv_apply {n : ℕ} (g : GL (Fin n) S) (x : Fin n → S) : glEquiv g x = g.val *ᵥ x := rfl

/-- Helper: a linear equivalence of $S^n$ as an invertible matrix. -/
def equivGL {n : ℕ} (f : (Fin n → S) ≃ₗ[S] (Fin n → S)) : GL (Fin n) S where
  val := LinearMap.toMatrix' f.toLinearMap
  inv := LinearMap.toMatrix' f.symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    convert LinearMap.toMatrix'_id
    ext x; simp
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    convert LinearMap.toMatrix'_id
    ext x; simp

/-- Helper: `equivGL f` acts as `f`. -/
theorem equivGL_apply {n : ℕ} (f : (Fin n → S) ≃ₗ[S] (Fin n → S)) (x : Fin n → S) :
    (equivGL f).val *ᵥ x = f x := by
  simp [equivGL]

/-- Helper: `IsoOver` in equal dimensions gives `IsometricGL` of the base-changed forms (`A` to `A'`). -/
theorem IsoOver.isometricGL {n : ℕ} {A A' : QuadForm ℤ n} (h : IsoOver S A A') :
    IsometricGL (A.map (Int.castRingHom S)) (A'.map (Int.castRingHom S)) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨equivGL f.symm, fun x => ?_⟩
  rw [equivGL_apply, map_eval_eq_evalIn', map_eval_eq_evalIn', ← hf (f.symm x), LinearEquiv.apply_symm_apply]

/-- Helper: `IsometricGL` of the base-changed forms (`A'` to `A`) gives `IsoOver S A A'` in equal dimensions. -/
theorem IsoOver.of_isometricGL {n : ℕ} {A A' : QuadForm ℤ n}
    (h : IsometricGL (A'.map (Int.castRingHom S)) (A.map (Int.castRingHom S))) : IsoOver S A A' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨glEquiv g, fun x => ?_⟩
  have := hg x
  rw [map_eval_eq_evalIn', map_eval_eq_evalIn'] at this
  exact this

/-- Helper: the explicit element of the genus. -/
theorem sameGenus_rep (hG : SameGenus gamma16 twoE8) {m : ℕ} (Λ' : QuadForm ℤ m) (k j : ℕ)
    (h : 8 * k + (16 * j + m) = 8 * (k + 2 * j) + m) :
    SameGenus (QuadForm.orthSum (repE8 (k + 2 * j)) Λ')
      (h ▸ QuadForm.orthSum (repE8 k) (QuadForm.orthSum (repG j) Λ')) := by
  have key : ∀ (T : Type) [CommRing T], IsometricGL (gamma16.map (Int.castRingHom T)) (twoE8.map (Int.castRingHom T)) →
      IsoOver T (QuadForm.orthSum (repE8 (k + 2 * j)) Λ')
        (h ▸ QuadForm.orthSum (repE8 k) (QuadForm.orthSum (repG j) Λ')) := by
    intro T _ hT
    have H : IsoOver T (QuadForm.orthSum e8 e8) gamma16 := IsoOver.of_isometricGL hT
    exact (((isoOver_repE8_repG H k j).orthSum (IsoOver.refl Λ')).trans
      (IsoOver.assoc _ _ _).symm).trans (IsoOver.cast h _)
  refine ⟨fun p _ => ?_, ?_⟩
  · exact (key ℤ_[p] (hG.1 p)).isometricGL
  · exact (key ℝ hG.2).isometricGL

end Genus




/-- Helper: the rational form of an integral form. -/
abbrev QQ {n : ℕ} (Q : QuadForm ℤ n) : QuadForm ℚ n := Q.map (Int.castRingHom ℚ)

/-- Helper: the value of the rational form `QQ Q` is `Q.evalIn ℚ`. -/
theorem QQ_eval {n : ℕ} (Q : QuadForm ℤ n) (x : Fin n → ℚ) : (QQ Q).eval x = Q.evalIn ℚ x := by
  simp [QuadForm.map, QuadForm.evalIn]

/-- Helper: the polar form of `QQ Q` is $Q(x + y) - Q(x) - Q(y)$. -/
theorem bil_QQ {n : ℕ} (Q : QuadForm ℤ n) (x y : Fin n → ℚ) :
    bil (QQ Q) x y = Q.evalIn ℚ (x + y) - Q.evalIn ℚ x - Q.evalIn ℚ y := by
  rw [QuadForm.polar_eq_hessian ℚ Q x y]
  simp [bil, QuadForm.hessian, QuadForm.map, Matrix.map_add, Matrix.transpose_map]

/-- Helper: a positive definite integral form is positive on non-zero rational vectors. -/
theorem posDef_QQ {n : ℕ} {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (x : Fin n → ℚ) (hx : x ≠ 0) :
    0 < (QQ Q).eval x := by
  rw [QQ_eval]
  have hx' : (fun i => (x i : ℝ)) ≠ 0 := by
    intro h; apply hx; funext i
    have := congrFun h i
    simpa using this
  have h1 := hQ.evalIn_real_pos _ hx'
  have h2 := AWS.evalIn_map Q (Rat.castHom ℝ) x
  have e : (Rat.castHom ℝ) ∘ x = fun i => (x i : ℝ) := rfl
  rw [e] at h2
  rw [← h2] at h1
  simpa using h1

/-- Helper: the lattice $\mathbb Z^n \subset \mathbb Q^n$. -/
def LatZ (n : ℕ) : Submodule (𝓞 ℚ) (Fin n → ℚ) :=
  Submodule.span (𝓞 ℚ) (Set.range fun i : Fin n => (Pi.single i (1 : ℚ) : Fin n → ℚ))

/-- Helper: $x \in \mathbb Z^n$ iff all coordinates are integers. -/
theorem mem_LatZ {n : ℕ} {x : Fin n → ℚ} : x ∈ LatZ n ↔ ∀ i, ∃ z : ℤ, x i = z := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro j
      by_cases h : j = i
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩
    | zero => exact fun i => ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro i
      obtain ⟨a, ha⟩ := hy i
      obtain ⟨b, hb⟩ := hz i
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul a y _ hy =>
      intro i
      obtain ⟨m, hm⟩ := exists_intCast_ringOfIntegers_rat a
      obtain ⟨b, hb⟩ := hy i
      refine ⟨m * b, ?_⟩
      subst hm
      simp [hb, Algebra.smul_def]
  · intro h
    choose z hz using h
    have : x = ∑ i, z i • (Pi.single i (1 : ℚ) : Fin n → ℚ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, hz j]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

/-- Helper: $\mathbb Z^n$ is finitely generated. -/
theorem LatZ_fg (n : ℕ) : (LatZ n).FG :=
  ⟨(Finset.univ : Finset (Fin n)).image fun i => (Pi.single i (1 : ℚ) : Fin n → ℚ), by
    simp [LatZ]⟩

section Transport

variable {n n' : ℕ} {Q : QuadForm ℚ n} {Q' : QuadForm ℚ n'}

/-- Helper: an injective linear map scaling the polar form by $c$ carries an orthogonal splitting of $L$ to one of its image. Arguments: `T` the map, `hT` its injectivity, `hb` the scaling of the polar forms, `h` the splitting. -/
theorem splitting_map (T : (Fin n → ℚ) →ₗ[𝓞 ℚ] (Fin n' → ℚ)) (hT : Function.Injective T) {c : ℚ}
    (hb : ∀ x y, bil Q' (T x) (T y) = c * bil Q x y)
    {L : Submodule (𝓞 ℚ) (Fin n → ℚ)} {S : Finset (Submodule (𝓞 ℚ) (Fin n → ℚ))}
    (h : IsOrthSplitting Q L S) :
    IsOrthSplitting Q' (L.map T) (S.image (Submodule.map T)) where
  ne_bot := by
    intro K' hK'
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hK'
    intro h0
    exact h.ne_bot K hK ((Submodule.map_injective_of_injective hT) (h0.trans (Submodule.map_bot T).symm))
  orth := by
    intro K1' h1 K2' h2 hne
    obtain ⟨K1, hK1, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨K2, hK2, rfl⟩ := Finset.mem_image.mp h2
    have hne' : K1 ≠ K2 := fun e => hne (by rw [e])
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb', rfl⟩
    rw [hb, h.orth K1 hK1 K2 hK2 hne' a ha b hb', mul_zero]
  indep := by
    classical
    have h1 : iSupIndep fun K : S => (K : Submodule (𝓞 ℚ) (Fin n → ℚ)).map T :=
      LinearMap.iSupIndep_map T hT h.indep
    have h2 : S.SupIndep (fun K => K.map T) := iSupIndep.supIndep h1
    exact Finset.SupIndep.independent (f := (id : Submodule (𝓞 ℚ) (Fin n' → ℚ) → _))
      (Finset.SupIndep.image (g := Submodule.map T) h2)
  sup_eq := by
    classical
    rw [Finset.sup_image]
    apply le_antisymm
    · refine Finset.sup_le fun K hK => ?_
      exact Submodule.map_mono (h.sup_eq ▸ Finset.le_sup (f := id) hK)
    · rw [← h.sup_eq, Submodule.map_le_iff_le_comap]
      refine Finset.sup_le fun K hK => ?_
      rw [← Submodule.map_le_iff_le_comap]
      exact Finset.le_sup (f := id ∘ Submodule.map T) hK

/-- Helper: the same map carries an indecomposable lattice to an indecomposable lattice (`c` non-zero). Arguments as in `splitting_map`. -/
theorem indecomposable_map (T : (Fin n → ℚ) →ₗ[𝓞 ℚ] (Fin n' → ℚ)) (hT : Function.Injective T) {c : ℚ}
    (hc : c ≠ 0) (hb : ∀ x y, bil Q' (T x) (T y) = c * bil Q x y)
    {K : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : IsIndecomposable Q K) :
    IsIndecomposable Q' (K.map T) := by
  refine ⟨?_, ?_⟩
  · intro h0
    exact hK.1 ((Submodule.map_injective_of_injective hT) (h0.trans (Submodule.map_bot T).symm))
  · rintro ⟨K1, K2, h1, h2, ho, hd, hs⟩
    apply hK.2
    have hle1 : K1 ≤ K.map T := hs ▸ le_sup_left
    have hle2 : K2 ≤ K.map T := hs ▸ le_sup_right
    have back : ∀ y ∈ K.map T, ∃ x ∈ K, T x = y := fun y hy => hy
    refine ⟨K1.comap T, K2.comap T, ?_, ?_, ?_, ?_, ?_⟩
    · intro h0
      apply h1
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := back y (hle1 hy)
      have : x ∈ K1.comap T := hy
      rw [h0] at this
      simp only [Submodule.mem_bot] at this
      simp [this]
    · intro h0
      apply h2
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := back y (hle2 hy)
      have : x ∈ K2.comap T := hy
      rw [h0] at this
      simp only [Submodule.mem_bot] at this
      simp [this]
    · intro x hx y hy
      have := ho _ hx _ hy
      rw [hb] at this
      exact (mul_eq_zero.mp this).resolve_left hc
    · rw [Submodule.disjoint_def]
      intro x hx1 hx2
      have := Submodule.disjoint_def.mp hd (T x) hx1 hx2
      exact hT (by rw [this, map_zero])
    · apply le_antisymm
      · refine sup_le ?_ ?_
        · intro x hx
          obtain ⟨x', hx', e⟩ := back _ (hle1 hx)
          rwa [← hT e]
        · intro x hx
          obtain ⟨x', hx', e⟩ := back _ (hle2 hx)
          rwa [← hT e]
      · intro x hx
        have hTx : T x ∈ K1 ⊔ K2 := by rw [hs]; exact ⟨x, hx, rfl⟩
        obtain ⟨a, ha, b, hb', hab⟩ := Submodule.mem_sup.mp hTx
        obtain ⟨a0, -, rfl⟩ := back a (hle1 ha)
        obtain ⟨b0, -, rfl⟩ := back b (hle2 hb')
        have : x = a0 + b0 := hT (by rw [map_add]; exact hab.symm)
        rw [this]
        exact Submodule.add_mem_sup ha hb'

end Transport

section Count

variable {n : ℕ}

/-- Helper: an indecomposable splitting of $\mathbb Z^n$ (for the rational form of $Q$) with $k$ summands. -/
def SplitCount (Q : QuadForm ℤ n) (k : ℕ) : Prop :=
  ∃ S : Finset (Submodule (𝓞 ℚ) (Fin n → ℚ)), IsOrthSplitting (QQ Q) (LatZ n) S ∧
    (∀ K ∈ S, IsIndecomposable (QQ Q) K) ∧ S.card = k

/-- Helper (Theorem 2.1 for forms): the number of indecomposable summands of $\mathbb Z^n$ is well defined for a positive definite form. -/
theorem splitCount_unique {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {k k' : ℕ} (h : SplitCount Q k)
    (h' : SplitCount Q k') : k = k' := by
  obtain ⟨S, h1, h2, rfl⟩ := h
  obtain ⟨S', h1', h2', rfl⟩ := h'
  rw [thm_2_1 (QQ Q) (posDef_QQ hQ) (LatZ n) (LatZ_fg n) h1 h2 h1' h2']

/-- Helper: every form has an indecomposable splitting of $\mathbb Z^n$, with some number $k$ of summands. -/
theorem exists_splitCount (Q : QuadForm ℤ n) : ∃ k, SplitCount Q k := by
  obtain ⟨S, h1, h2, -⟩ := exists_indecomposable_splitting (QQ Q) (LatZ n)
  exact ⟨S.card, S, h1, h2, rfl⟩

/-- Helper: an indecomposable $\mathbb Z^n$ has the splitting with one summand. -/
theorem splitCount_one {Q : QuadForm ℤ n} (h : IsIndecomposable (QQ Q) (LatZ n)) : SplitCount Q 1 :=
  ⟨{LatZ n}, splitting_single h.1, by simpa using h, by simp⟩

/-- Helper: `SplitCount` is invariant under transport along `h : a = a'`. -/
theorem splitCount_cast {a a' : ℕ} (h : a = a') (Q : QuadForm ℤ a) (c : ℕ) :
    SplitCount (h ▸ Q) c ↔ SplitCount Q c := by
  subst h; exact Iff.rfl

/-- Helper: a rational matrix as a linear map over $\mathcal O_{\mathbb Q}$. -/
def lmQ {n n' : ℕ} (M : Matrix (Fin n') (Fin n) ℚ) : (Fin n → ℚ) →ₗ[𝓞 ℚ] (Fin n' → ℚ) :=
  (Matrix.mulVecLin M).restrictScalars (𝓞 ℚ)

/-- Helper: `lmQ M` is multiplication by `M`. -/
theorem lmQ_apply {n n' : ℕ} (M : Matrix (Fin n') (Fin n) ℚ) (x : Fin n → ℚ) : lmQ M x = M *ᵥ x := rfl

/-- Helper: the polar form of `QQ Q` is given by the Hessian of `Q`. -/
theorem bil_QQ_hess {n : ℕ} (Q : QuadForm ℤ n) (x y : Fin n → ℚ) :
    bil (QQ Q) x y = x ⬝ᵥ (Q.hessian.map (Int.castRingHom ℚ) *ᵥ y) := by
  simp [bil, QuadForm.hessian, QuadForm.map, Matrix.map_add, Matrix.transpose_map]

/-- Helper: an integral matrix maps $\mathbb Z^n$ into $\mathbb Z^n$. -/
theorem mulVec_mem_LatZ {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ) {x : Fin n → ℚ} (hx : x ∈ LatZ n) :
    U.map (Int.castRingHom ℚ) *ᵥ x ∈ LatZ n := by
  rw [mem_LatZ] at hx ⊢
  intro i
  choose z hz using hx
  refine ⟨∑ j, U i j * z j, ?_⟩
  simp [Matrix.mulVec, dotProduct, hz]

/-- Helper: an integral isometry transports splittings. -/
theorem splitCount_of_isometricGL {Q Q' : QuadForm ℤ n} (h : IsometricGL Q Q') {k : ℕ}
    (hk : SplitCount Q' k) : SplitCount Q k := by
  obtain ⟨g, hg⟩ := h
  set G : Matrix (Fin n) (Fin n) ℚ := g.val.map (Int.castRingHom ℚ) with hG
  set Gi : Matrix (Fin n) (Fin n) ℚ := (g⁻¹ : GL (Fin n) ℤ).val.map (Int.castRingHom ℚ) with hGidef
  have hGi : Gi * G = 1 := by
    rw [hG, hGidef, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel]; simp
  have hGi' : G * Gi = 1 := by
    rw [hG, hGidef, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel]; simp
  have hinj : Function.Injective (lmQ G) := by
    intro x y hxy
    have := congrArg (fun z => Gi *ᵥ z) hxy
    simp only [lmQ_apply, Matrix.mulVec_mulVec, hGi, Matrix.one_mulVec] at this
    exact this
  have hev : ∀ x : Fin n → ℚ, Q.evalIn ℚ (G *ᵥ x) = Q'.evalIn ℚ x := by
    intro x
    have := Siegel.eval_mulVec_map (Int.castRingHom ℚ) hg x
    simpa [QuadForm.map, QuadForm.evalIn, hG] using this
  have hb : ∀ x y, bil (QQ Q) (lmQ G x) (lmQ G y) = 1 * bil (QQ Q') x y := by
    intro x y
    rw [one_mul, bil_QQ, bil_QQ]
    simp only [lmQ_apply]
    rw [← Matrix.mulVec_add, hev, hev, hev]
  have hL : (LatZ n).map (lmQ G) = LatZ n := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact mulVec_mem_LatZ g.val hx
    · intro y hy
      have hy' : y ∈ LatZ n := hy
      refine ⟨Gi *ᵥ y, mulVec_mem_LatZ _ hy', ?_⟩
      rw [lmQ_apply, Matrix.mulVec_mulVec, hGi', Matrix.one_mulVec]
  obtain ⟨S, h1, h2, rfl⟩ := hk
  refine ⟨S.image (Submodule.map (lmQ G)), ?_, ?_, ?_⟩
  · have := splitting_map (lmQ G) hinj hb h1
    rwa [hL] at this
  · intro K' hK'
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hK'
    exact indecomposable_map (lmQ G) hinj one_ne_zero hb (h2 K hK)
  · exact Finset.card_image_of_injective _ (Submodule.map_injective_of_injective hinj)


section Add

/-- Helper: $\mathbb Q^a \to \mathbb Q^{a+b}$, $x \mapsto (x, 0)$. -/
def emb1 (a b : ℕ) : (Fin a → ℚ) →ₗ[𝓞 ℚ] (Fin (a + b) → ℚ) where
  toFun x := Fin.append x 0
  map_add' x y := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  map_smul' c x := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

/-- Helper: $\mathbb Q^b \to \mathbb Q^{a+b}$, $y \mapsto (0, y)$. -/
def emb2 (a b : ℕ) : (Fin b → ℚ) →ₗ[𝓞 ℚ] (Fin (a + b) → ℚ) where
  toFun y := Fin.append 0 y
  map_add' x y := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  map_smul' c x := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

/-- Helper: first block of `emb1`. -/
theorem emb1_castAdd (a b : ℕ) (x : Fin a → ℚ) (i : Fin a) : emb1 a b x (Fin.castAdd b i) = x i := by
  simp [emb1]

/-- Helper: second block of `emb1` is zero. -/
theorem emb1_natAdd (a b : ℕ) (x : Fin a → ℚ) (j : Fin b) : emb1 a b x (Fin.natAdd a j) = 0 := by
  simp [emb1]

/-- Helper: first block of `emb2` is zero. -/
theorem emb2_castAdd (a b : ℕ) (y : Fin b → ℚ) (i : Fin a) : emb2 a b y (Fin.castAdd b i) = 0 := by
  simp [emb2]

/-- Helper: second block of `emb2`. -/
theorem emb2_natAdd (a b : ℕ) (y : Fin b → ℚ) (j : Fin b) : emb2 a b y (Fin.natAdd a j) = y j := by
  simp [emb2]

/-- Helper: `emb1` is injective. -/
theorem emb1_injective (a b : ℕ) : Function.Injective (emb1 a b) := by
  intro x y h
  funext i
  have := congrFun h (Fin.castAdd b i)
  rwa [emb1_castAdd, emb1_castAdd] at this

/-- Helper: `emb2` is injective. -/
theorem emb2_injective (a b : ℕ) : Function.Injective (emb2 a b) := by
  intro x y h
  funext i
  have := congrFun h (Fin.natAdd a i)
  rwa [emb2_natAdd, emb2_natAdd] at this

/-- Helper: a form vanishes at $0$. -/
theorem evalIn_zero_rat {n : ℕ} (Q : QuadForm ℤ n) : Q.evalIn ℚ 0 = 0 := by
  simp [QuadForm.evalIn]

/-- Helper: `emb1` is an isometry for the polar form of an orthogonal sum. -/
theorem bil_emb11 {a b : ℕ} (A : QuadForm ℤ a) (B : QuadForm ℤ b) (x y : Fin a → ℚ) :
    bil (QQ (QuadForm.orthSum A B)) (emb1 a b x) (emb1 a b y) = 1 * bil (QQ A) x y := by
  rw [one_mul, bil_QQ, bil_QQ, ← map_add]
  simp only [QuadForm.evalIn_orthSum]
  have e : ∀ z : Fin a → ℚ, (fun i => emb1 a b z (Fin.castAdd b i)) = z := fun z => funext (emb1_castAdd a b z)
  have e' : ∀ z : Fin a → ℚ, (fun j => emb1 a b z (Fin.natAdd a j)) = 0 :=
    fun z => funext (emb1_natAdd a b z)
  rw [e, e, e, e', e', e', evalIn_zero_rat]
  ring

/-- Helper: `emb2` is an isometry for the polar form of an orthogonal sum. -/
theorem bil_emb22 {a b : ℕ} (A : QuadForm ℤ a) (B : QuadForm ℤ b) (x y : Fin b → ℚ) :
    bil (QQ (QuadForm.orthSum A B)) (emb2 a b x) (emb2 a b y) = 1 * bil (QQ B) x y := by
  rw [one_mul, bil_QQ, bil_QQ, ← map_add]
  simp only [QuadForm.evalIn_orthSum]
  have e : ∀ z : Fin b → ℚ, (fun i => emb2 a b z (Fin.natAdd a i)) = z := fun z => funext (emb2_natAdd a b z)
  have e' : ∀ z : Fin b → ℚ, (fun j => emb2 a b z (Fin.castAdd b j)) = 0 :=
    fun z => funext (emb2_castAdd a b z)
  rw [e, e, e, e', e', e', evalIn_zero_rat]
  ring

/-- Helper: the images of `emb1` and `emb2` are orthogonal. -/
theorem bil_emb12 {a b : ℕ} (A : QuadForm ℤ a) (B : QuadForm ℤ b) (x : Fin a → ℚ) (y : Fin b → ℚ) :
    bil (QQ (QuadForm.orthSum A B)) (emb1 a b x) (emb2 a b y) = 0 := by
  rw [bil_QQ]
  simp only [QuadForm.evalIn_orthSum]
  have e1 : (fun i => emb1 a b x (Fin.castAdd b i)) = x := funext (emb1_castAdd a b x)
  have e2 : (fun j => emb1 a b x (Fin.natAdd a j)) = 0 := funext (emb1_natAdd a b x)
  have e3 : (fun i => emb2 a b y (Fin.castAdd b i)) = 0 := funext (emb2_castAdd a b y)
  have e4 : (fun j => emb2 a b y (Fin.natAdd a j)) = y := funext (emb2_natAdd a b y)
  have e5 : (fun i => (emb1 a b x + emb2 a b y) (Fin.castAdd b i)) = x := by
    funext i; simp [emb1_castAdd, emb2_castAdd]
  have e6 : (fun j => (emb1 a b x + emb2 a b y) (Fin.natAdd a j)) = y := by
    funext j; simp [emb1_natAdd, emb2_natAdd]
  rw [e5, e6, e1, e2, e3, e4]
  simp only [evalIn_zero_rat]
  ring

end Add


/-- Helper: the number of indecomposable summands is additive in orthogonal sums. -/
theorem splitCount_orthSum {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b} {k l : ℕ}
    (hA : SplitCount A k) (hB : SplitCount B l) : SplitCount (QuadForm.orthSum A B) (k + l) := by
  classical
  obtain ⟨S1, h1, i1, rfl⟩ := hA
  obtain ⟨S2, h2, i2, rfl⟩ := hB
  set K1 : Submodule (𝓞 ℚ) (Fin (a + b) → ℚ) := (LatZ a).map (emb1 a b) with hK1
  set K2 : Submodule (𝓞 ℚ) (Fin (a + b) → ℚ) := (LatZ b).map (emb2 a b) with hK2
  have h1' := splitting_map (emb1 a b) (emb1_injective a b) (bil_emb11 A B) h1
  have h2' := splitting_map (emb2 a b) (emb2_injective a b) (bil_emb22 A B) h2
  have ho : LatOrth (QQ (QuadForm.orthSum A B)) K1 K2 := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    exact bil_emb12 A B x y
  have hd : Disjoint K1 K2 := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨x, -, rfl⟩ ⟨y, -, hxy⟩
    have : x = 0 := by
      funext i
      have := congrFun hxy (Fin.castAdd b i)
      rw [emb2_castAdd, emb1_castAdd] at this
      simpa using this.symm
    simp [this]
  have hsup : K1 ⊔ K2 = LatZ (a + b) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        rw [mem_LatZ]
        intro i
        refine Fin.addCases (fun i => ?_) (fun j => ?_) i
        · obtain ⟨z, hz⟩ := mem_LatZ.1 hx i
          exact ⟨z, by rw [emb1_castAdd, hz]⟩
        · exact ⟨0, by rw [emb1_natAdd]; simp⟩
      · rintro _ ⟨x, hx, rfl⟩
        rw [mem_LatZ]
        intro i
        refine Fin.addCases (fun i => ?_) (fun j => ?_) i
        · exact ⟨0, by rw [emb2_castAdd]; simp⟩
        · obtain ⟨z, hz⟩ := mem_LatZ.1 hx j
          exact ⟨z, by rw [emb2_natAdd, hz]⟩
    · intro x hx
      have hx' : x ∈ LatZ (a + b) := hx
      have e : x = emb1 a b (fun i => x (Fin.castAdd b i)) + emb2 a b (fun j => x (Fin.natAdd a j)) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun j => ?_) i
        · simp [emb1_castAdd, emb2_castAdd]
        · simp [emb1_natAdd, emb2_natAdd]
      rw [e]
      refine Submodule.add_mem_sup ⟨_, ?_, rfl⟩ ⟨_, ?_, rfl⟩
      · exact mem_LatZ.2 fun i => mem_LatZ.1 hx' (Fin.castAdd b i)
      · exact mem_LatZ.2 fun j => mem_LatZ.1 hx' (Fin.natAdd a j)
  have hU := splitting_union ho hd h1' h2'
  rw [hsup] at hU
  refine ⟨_, hU, ?_, ?_⟩
  · intro K hK
    rcases Finset.mem_union.mp hK with h | h
    · obtain ⟨K0, hK0, rfl⟩ := Finset.mem_image.mp h
      exact indecomposable_map (emb1 a b) (emb1_injective a b) one_ne_zero (bil_emb11 A B) (i1 K0 hK0)
    · obtain ⟨K0, hK0, rfl⟩ := Finset.mem_image.mp h
      exact indecomposable_map (emb2 a b) (emb2_injective a b) one_ne_zero (bil_emb22 A B) (i2 K0 hK0)
  · rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (Submodule.map_injective_of_injective
      (emb1_injective a b)), Finset.card_image_of_injective _ (Submodule.map_injective_of_injective
      (emb2_injective a b))]
    rw [Finset.disjoint_left]
    intro K hK hK2
    have le1 : K ≤ K1 := (Finset.le_sup (f := id) hK).trans h1'.sup_eq.le
    have le2 : K ≤ K2 := (Finset.le_sup (f := id) hK2).trans h2'.sup_eq.le
    exact h1'.ne_bot K hK (eq_bot_iff.mpr (hd.mono le1 le2 |> fun h => by simpa using h))

end Count

section Indec

/-- Helper: unit vectors lie in $\mathbb Z^n$. -/
theorem single_mem_LatZ {n : ℕ} (i : Fin n) : (Pi.single i (1 : ℚ) : Fin n → ℚ) ∈ LatZ n :=
  Submodule.subset_span (Set.mem_range_self i)

/-- Helper: the polar form on unit vectors is the Hessian. -/
theorem bil_single {n : ℕ} (Q : QuadForm ℤ n) (a b : Fin n) :
    bil (QQ Q) (Pi.single a 1) (Pi.single b 1) = (Q.hessian a b : ℚ) := by
  rw [bil_QQ_hess]
  simp

/-- Helper: the rational value at a unit vector is the integral value. -/
theorem evalIn_single {n : ℕ} (Q : QuadForm ℤ n) (i : Fin n) :
    Q.evalIn ℚ (Pi.single i 1) = (Q.eval (Pi.single i 1) : ℚ) := by
  have := Siegel.evalIn_intCast (K := ℚ) Q (Pi.single i 1)
  rw [← this]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

/-- Helper: a lattice $\mathbb Z^n$ with $Q(e_i) = 1$ and connected "Gram graph" is indecomposable. -/
theorem indecomposable_of_graph {n : ℕ} (hn : 0 < n) {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q)
    (hone : ∀ i, Q.eval (Pi.single i 1) = 1)
    (hconn : ∀ j, Relation.ReflTransGen (fun a b : Fin n => Q.hessian a b ≠ 0) ⟨0, hn⟩ j) :
    IsIndecomposable (QQ Q) (LatZ n) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := single_mem_LatZ (⟨0, hn⟩ : Fin n)
    rw [h] at this
    have h2 := congrFun (Submodule.mem_bot _ |>.mp this) ⟨0, hn⟩
    simp at h2
  · rintro ⟨K1, K2, h1, h2, ho, hd, hs⟩
    have hKle1 : K1 ≤ LatZ n := hs ▸ le_sup_left
    have hKle2 : K2 ≤ LatZ n := hs ▸ le_sup_right
    -- each unit vector lies in K1 or K2
    have key : ∀ i : Fin n, (Pi.single i (1 : ℚ) : Fin n → ℚ) ∈ K1 ∨ (Pi.single i (1 : ℚ) : Fin n → ℚ) ∈ K2 := by
      intro i
      have hi : (Pi.single i (1 : ℚ) : Fin n → ℚ) ∈ K1 ⊔ K2 := hs ▸ single_mem_LatZ i
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hi
      obtain ⟨zu, hzu⟩ : ∃ z : Fin n → ℤ, u = fun j => (z j : ℚ) := by
        have := mem_LatZ.1 (hKle1 hu)
        choose z hz using this
        exact ⟨z, funext hz⟩
      obtain ⟨zv, hzv⟩ : ∃ z : Fin n → ℤ, v = fun j => (z j : ℚ) := by
        have := mem_LatZ.1 (hKle2 hv)
        choose z hz using this
        exact ⟨z, funext hz⟩
      have hbil := ho u hu v hv
      rw [bil_QQ, huv, evalIn_single, hzu, hzv, Siegel.evalIn_intCast, Siegel.evalIn_intCast,
        hone] at hbil
      have hsum : Q.eval zu + Q.eval zv = 1 := by
        have : ((Q.eval zu + Q.eval zv : ℤ) : ℚ) = 1 := by push_cast at hbil ⊢; linarith
        exact_mod_cast this
      have hnn := fun z => IntQF.PosDef.eval_nonneg hQ z
      by_cases hzu0 : zu = 0
      · right
        have : u = 0 := by rw [hzu, hzu0]; funext j; simp
        rw [this, zero_add] at huv
        rwa [← huv]
      · left
        have hp := hQ zu hzu0
        have : Q.eval zv = 0 := by linarith [hnn zv]
        have hzv0 : zv = 0 := by
          by_contra hne
          have := hQ zv hne
          linarith
        have : v = 0 := by rw [hzv, hzv0]; funext j; simp
        rw [this, add_zero] at huv
        rwa [← huv]
    have excl : ∀ i : Fin n, ¬ ((Pi.single i (1 : ℚ) : Fin n → ℚ) ∈ K1 ∧ (Pi.single i (1 : ℚ) : Fin n → ℚ) ∈ K2) := by
      rintro i ⟨a, b⟩
      have := Submodule.disjoint_def.mp hd _ a b
      have h2 := congrFun this i
      simp at h2
    have edge : ∀ a b : Fin n, Q.hessian a b ≠ 0 →
        ((Pi.single a (1 : ℚ) : Fin n → ℚ) ∈ K1 ↔ (Pi.single b (1 : ℚ) : Fin n → ℚ) ∈ K1) := by
      intro a b hab
      have hne : bil (QQ Q) (Pi.single a 1) (Pi.single b 1) ≠ 0 := by
        rw [bil_single]; exact_mod_cast hab
      have hne' : bil (QQ Q) (Pi.single b 1) (Pi.single a 1) ≠ 0 := by
        rw [bil_comm]; exact hne
      constructor
      · intro ha
        rcases key b with hb | hb
        · exact hb
        · exact absurd (ho _ ha _ hb) hne
      · intro hb
        rcases key a with ha | ha
        · exact ha
        · exact absurd (ho _ hb _ ha) hne'
    have prop : ∀ j : Fin n, ((Pi.single (⟨0, hn⟩ : Fin n) (1 : ℚ) : Fin n → ℚ) ∈ K1 ↔
        (Pi.single j (1 : ℚ) : Fin n → ℚ) ∈ K1) := by
      intro j
      induction hconn j with
      | refl => exact Iff.rfl
      | tail _ hbc ih => exact ih.trans (edge _ _ hbc)
    by_cases h0 : (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℚ) : Fin n → ℚ) ∈ K1
    · have hall : LatZ n ≤ K1 := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨j, rfl⟩
        exact (prop j).mp h0
      exact h2 (eq_bot_iff.mpr (hd.symm.eq_bot_of_le (hKle2.trans hall) |>.le))
    · have hall : LatZ n ≤ K2 := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨j, rfl⟩
        rcases key j with hj | hj
        · exact absurd ((prop j).mpr hj) h0
        · exact hj
      exact h1 (eq_bot_iff.mpr (hd.eq_bot_of_le (hKle1.trans hall) |>.le))

end Indec

section Concrete

/-- Helper: the lattice of $E_8$ (`Siegel.e8`) is indecomposable (Cassels' $\Gamma_8$). Proof: every unit vector has value $1$, hence is irreducible, and the Gram graph (the $E_8$ Dynkin diagram) is connected. -/
theorem e8_indecomposable : IsIndecomposable (QQ e8) (LatZ 8) := by
  refine indecomposable_of_graph (by norm_num) e8_posDef ?_ ?_
  · intro i
    rw [e8_eval]
    fin_cases i <;> simp
  · set R : Fin 8 → Fin 8 → Prop := fun a b => e8.hessian a b ≠ 0 with hR
    have R02 : R 0 2 := by simp only [hR]; rw [e8_hessian]; decide
    have R23 : R 2 3 := by simp only [hR]; rw [e8_hessian]; decide
    have R31 : R 3 1 := by simp only [hR]; rw [e8_hessian]; decide
    have R34 : R 3 4 := by simp only [hR]; rw [e8_hessian]; decide
    have R45 : R 4 5 := by simp only [hR]; rw [e8_hessian]; decide
    have R56 : R 5 6 := by simp only [hR]; rw [e8_hessian]; decide
    have R67 : R 6 7 := by simp only [hR]; rw [e8_hessian]; decide
    have r2 : Relation.ReflTransGen R 0 2 := Relation.ReflTransGen.single R02
    have r3 := r2.tail R23
    have r1 := r3.tail R31
    have r4 := r3.tail R34
    have r5 := r4.tail R45
    have r6 := r5.tail R56
    have r7 := r6.tail R67
    intro j
    fin_cases j
    · exact Relation.ReflTransGen.refl
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
    · exact r7

/-- Helper: $E_8$ has one indecomposable summand. -/
theorem splitCount_e8 : SplitCount e8 1 := splitCount_one e8_indecomposable


/-- Helper: the polar form of $\sum x_i^2$ is $2\,x \cdot y$. -/
theorem bil_sumSq (n : ℕ) (x y : Fin n → ℚ) : bil (sumSqForm n) x y = 2 * (x ⬝ᵥ y) := by
  have h := QuadForm.polar_eq_hessian ℚ (sumSqForm n) x y
  have h2 : bil (sumSqForm n) x y =
      (sumSqForm n).evalIn ℚ (x + y) - (sumSqForm n).evalIn ℚ x - (sumSqForm n).evalIn ℚ y := by
    simpa [bil] using h.symm
  have hev : ∀ z : Fin n → ℚ, (sumSqForm n).evalIn ℚ z = ∑ i, z i ^ 2 := by
    intro z
    rw [sumSqForm, QuadForm.evalIn_diag]; simp
  rw [h2, hev, hev, hev]
  simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, dotProduct, Finset.mul_sum]
  ring_nf

/-- Helper: the basis $B$ of $\Gamma_{16}$ carries the polar form of `gamma16` to $\tfrac12$ of that of $\sum x_i^2$ (precisely $B$ scales by $2$). -/
theorem bil_gamma16_fwd (x y : Fin 16 → ℚ) :
    bil (sumSqForm 16) (gamma16Basis *ᵥ x) (gamma16Basis *ᵥ y) = 2 * bil (QQ gamma16) x y := by
  have h : (gamma16Basis *ᵥ x) ⬝ᵥ (gamma16Basis *ᵥ y) = x ⬝ᵥ ((gamma16Basisᵀ * gamma16Basis) *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x gamma16Basisᵀ (gamma16Basis *ᵥ y),
      Matrix.vecMul_transpose]
  rw [bil_sumSq, bil_QQ_hess, gamma16_hessian_map, h]

/-- Helper: the lattice of `gamma16` is indecomposable (from `Lattices.casselsGamma_indecomposable`, Ex. 1 (iii), transported along the basis). -/
theorem gamma16_indecomposable : IsIndecomposable (QQ gamma16) (LatZ 16) := by
  set B := gamma16Basis with hB
  have hdet : IsUnit B.det := by rw [hB, det_gamma16Basis]; exact isUnit_one
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  have hinj : Function.Injective (lmQ B⁻¹) := by
    intro x y hxy
    have := congrArg (fun z => B *ᵥ z) hxy
    simp only [lmQ_apply, Matrix.mulVec_mulVec, hBi', Matrix.one_mulVec] at this
    exact this
  have hb : ∀ x y, bil (QQ gamma16) (lmQ B⁻¹ x) (lmQ B⁻¹ y) = (1 / 2 : ℚ) * bil (sumSqForm 16) x y := by
    intro x y
    have := bil_gamma16_fwd (B⁻¹ *ᵥ x) (B⁻¹ *ᵥ y)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBi', Matrix.one_mulVec, Matrix.one_mulVec] at this
    rw [lmQ_apply, lmQ_apply, this]; ring
  have hmap : (casselsGamma 16).map (lmQ B⁻¹) = LatZ 16 := by
    rw [← span_gamma16Vec]
    unfold LatZ
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      refine ⟨j, ?_⟩
      have : gamma16Vec j = B *ᵥ Pi.single j 1 := by
        funext i; simp [gamma16Vec, hB]
      rw [lmQ_apply, this, Matrix.mulVec_mulVec, hBi, Matrix.one_mulVec]
    · rintro ⟨j, rfl⟩
      refine ⟨gamma16Vec j, ⟨j, rfl⟩, ?_⟩
      have : gamma16Vec j = B *ᵥ Pi.single j 1 := by
        funext i; simp [gamma16Vec, hB]
      rw [lmQ_apply, this, Matrix.mulVec_mulVec, hBi, Matrix.one_mulVec]
  have := indecomposable_map (Q := sumSqForm 16) (Q' := QQ gamma16) (lmQ B⁻¹) hinj (by norm_num) hb
    (casselsGamma_indecomposable (n := 16) (by norm_num) (by norm_num))
  rwa [hmap] at this

/-- Helper: $\Gamma_{16}$ has one indecomposable summand. -/
theorem splitCount_gamma16 : SplitCount gamma16 1 := splitCount_one gamma16_indecomposable

/-- Helper: `gamma16` is positive definite. -/
theorem gamma16_posDef : IntQF.PosDef gamma16 := by
  intro c hc
  have h := two_mul_gamma16_eval c
  have hne : gamma16Basis *ᵥ (fun i => (c i : ℚ)) ≠ 0 := by
    intro h0
    have hdet : gamma16Basis.det ≠ 0 := by rw [det_gamma16Basis]; exact one_ne_zero
    apply hc
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet h0
    funext i
    have := congrFun this i
    simpa using this
  have hpos : 0 < (sumSqForm 16).eval (gamma16Basis *ᵥ fun i => (c i : ℚ)) := by
    have hev : (sumSqForm 16).eval (gamma16Basis *ᵥ fun i => (c i : ℚ)) =
        ∑ i, (gamma16Basis *ᵥ fun i => (c i : ℚ)) i ^ 2 := by
      rw [sumSqForm, QuadForm.eval, QuadForm.evalIn_diag]; simp
    rw [hev]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact lt_of_lt_of_le (by simpa using pow_pos (abs_pos.mpr hi) 2 |>.trans_eq (sq_abs _))
      (Finset.single_le_sum (f := fun i => (gamma16Basis *ᵥ fun i => (c i : ℚ)) i ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  rw [← h] at hpos
  have : (0 : ℚ) < (gamma16.eval c : ℚ) := by linarith
  exact_mod_cast this

end Concrete



/-! ### Positive definiteness and splitting counts of the building blocks -/

section Blocks

/-- Helper: a form in $0$ variables is positive definite (vacuously). -/
theorem posDef_of_dim_zero {z : ℕ} (Z : QuadForm ℤ z) (hz : z = 0) : IntQF.PosDef Z := by
  subst hz
  intro x hx
  exact absurd (funext fun i => (IsEmpty.false i).elim) hx

/-- Helper: the orthogonal sum of positive definite forms is positive definite. -/
theorem posDef_orthSum {a b : ℕ} {A : QuadForm ℤ a} {B : QuadForm ℤ b} (hA : IntQF.PosDef A)
    (hB : IntQF.PosDef B) : IntQF.PosDef (QuadForm.orthSum A B) := by
  intro x hx
  have e : (QuadForm.orthSum A B).eval x =
      A.eval (fun i => x (Fin.castAdd b i)) + B.eval (fun j => x (Fin.natAdd a j)) := by
    simpa [QuadForm.eval] using QuadForm.evalIn_orthSum ℤ A B x
  rw [e]
  by_cases h1 : (fun i => x (Fin.castAdd b i)) = 0
  · have h2 : (fun j => x (Fin.natAdd a j)) ≠ 0 := by
      intro h2
      apply hx
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · exact congrFun h1 i
      · exact congrFun h2 j
    have := hB _ h2
    have := hA.eval_nonneg (fun i => x (Fin.castAdd b i))
    linarith
  · have := hA _ h1
    have := hB.eval_nonneg (fun j => x (Fin.natAdd a j))
    linarith

/-- Helper: transport along `h : a = a'` preserves positive definiteness. -/
theorem posDef_cast {a a' : ℕ} (h : a = a') (Q : QuadForm ℤ a) : IntQF.PosDef (h ▸ Q) ↔ IntQF.PosDef Q := by
  subst h; exact Iff.rfl

/-- Helper: $E_8^r$ is positive definite. -/
theorem posDef_repE8 : ∀ r, IntQF.PosDef (repE8 r)
  | 0 => posDef_of_dim_zero _ (by simp)
  | r + 1 => posDef_orthSum (posDef_repE8 r) e8_posDef

/-- Helper: $\gamma_{16}^j$ is positive definite. -/
theorem posDef_repG : ∀ j, IntQF.PosDef (repG j)
  | 0 => posDef_of_dim_zero _ (by simp)
  | j + 1 => posDef_orthSum (posDef_repG j) gamma16_posDef

/-- Helper: a form in $0$ variables has the empty splitting. -/
theorem splitCount_of_dim_zero {z : ℕ} (Z : QuadForm ℤ z) (hz : z = 0) : SplitCount Z 0 := by
  subst hz
  have hbot : LatZ 0 = ⊥ := by
    apply Submodule.eq_bot_of_subsingleton
  refine ⟨∅, ⟨by simp, by simp, (Finset.supIndep_empty (id : Submodule (𝓞 ℚ) (Fin 0 → ℚ) → _)).independent,
    by simp [hbot]⟩, by simp, by simp⟩

/-- Helper: $E_8^r$ has $r$ indecomposable summands. -/
theorem splitCount_repE8 : ∀ r, SplitCount (repE8 r) r
  | 0 => splitCount_of_dim_zero _ (by simp)
  | r + 1 => splitCount_orthSum (splitCount_repE8 r) splitCount_e8

/-- Helper: $\gamma_{16}^j$ has $j$ indecomposable summands. -/
theorem splitCount_repG : ∀ j, SplitCount (repG j) j
  | 0 => splitCount_of_dim_zero _ (by simp)
  | j + 1 => splitCount_orthSum (splitCount_repG j) splitCount_gamma16

end Blocks

/-! ### The classes $(r - 2j)\Gamma_8 \perp j\Gamma_{16} \perp \Lambda'$ -/

/-- **Cassels, App. A, §3, (3.1)-(3.2), p. 365:** a genus containing $r\Gamma_8 \perp \Lambda'$, $\Lambda'$ positive
definite, has at least $1 + [r/2]$ classes: the lattices $(r - 2j)\Gamma_8 \perp j\Gamma_{16} \perp \Lambda'$,
$0 \le j \le r/2$, lie in the genus of $r\Gamma_8 \perp \Lambda'$ (because $\Gamma_{16}$ and $2\Gamma_8$ are in one genus,
`Lattices.gamma16_sameGenus`) and are pairwise non-isometric: an isometry carries the unique splitting into
indecomposable sublattices (Theorem 2.1, `Lattices.thm_2_1`) to the unique splitting, and the numbers of summands
$r - j + \kappa$ differ ($\kappa$ the number of indecomposable summands of $\Lambda'$; $E_8$ and $\Gamma_{16}$ are
indecomposable). Arguments: `r` the number of copies of $E_8$, `Λ'` the complementary form in `m` variables. -/
@[kb "cassels1978" "App. A, §3, (3.1)-(3.2), p. 365"]
theorem encard_genus_ge {m : ℕ} (r : ℕ) (Λ' : QuadForm ℤ m) (hΛ : IntQF.PosDef Λ') :
    ((1 + r / 2 : ℕ) : ℕ∞) ≤ (genusClasses (QuadForm.orthSum (repE8 r) Λ')).encard := by
  classical
  obtain ⟨κ, hκ⟩ := exists_splitCount Λ'
  have data : ∀ j : ℕ, 2 * j ≤ r → ∃ Qj : QuadForm ℤ (8 * r + m), IntQF.PosDef Qj ∧
      SameGenus (QuadForm.orthSum (repE8 r) Λ') Qj ∧ SplitCount Qj (r - j + κ) := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 * j := ⟨r - 2 * j, by omega⟩
    have h : 8 * k + (16 * j + m) = 8 * (k + 2 * j) + m := by ring
    refine ⟨h ▸ QuadForm.orthSum (repE8 k) (QuadForm.orthSum (repG j) Λ'), ?_,
      sameGenus_rep gamma16_sameGenus Λ' k j h, ?_⟩
    · rw [posDef_cast]
      exact posDef_orthSum (posDef_repE8 k) (posDef_orthSum (posDef_repG j) hΛ)
    · rw [splitCount_cast]
      have := splitCount_orthSum (splitCount_repE8 k) (splitCount_orthSum (splitCount_repG j) hκ)
      have e : k + 2 * j - j + κ = k + (j + κ) := by omega
      rw [e]
      exact this
  have : Nonempty (QuadForm ℤ (8 * r + m)) := ⟨QuadForm.ofUpper fun _ _ => 0⟩
  choose! Q hQ using data
  set s : Finset ℕ := Finset.range (r / 2 + 1) with hs
  have hle : ∀ j ∈ s, 2 * j ≤ r := fun j hj => by
    have := Finset.mem_range.mp hj
    omega
  have hinj : Set.InjOn (fun j => classOf (Q j)) (s : Set ℕ) := by
    intro i hi j hj hij
    have hi' := hle i hi
    have hj' := hle j hj
    have hint : IntEquiv (Q i) (Q j) := classOf_eq_classOf_iff.mp hij
    have h1 := splitCount_of_isometricGL hint (hQ j hj').2.2
    have := splitCount_unique (hQ i hi').1 h1 (hQ i hi').2.2
    omega
  have hsub : (fun j => classOf (Q j)) '' (s : Set ℕ) ⊆
      genusClasses (QuadForm.orthSum (repE8 r) Λ') := by
    rintro _ ⟨j, hj, rfl⟩
    exact classOf_mem_genusClasses_iff.mpr (hQ j (hle j hj)).2.1
  calc ((1 + r / 2 : ℕ) : ℕ∞) = (s : Set ℕ).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, hs, Finset.card_range]; congr 1; omega
    _ = ((fun j => classOf (Q j)) '' (s : Set ℕ)).encard := hinj.encard_image.symm
    _ ≤ _ := Set.encard_le_encard hsub

/-! ### The statement -/

section Statement

variable {n : ℕ}

/-- **$c(n)$** (Cassels, App. A, Thm. 3.1, p. 364): the minimum, over positive definite integer-valued forms $Q$ in
$n$ variables, of the number of classes (`genusClasses Q`, a set of $\mathrm{GL}_n(\mathbb Z)$-classes) in the genus
of $Q$; an element of $\mathbb N \cup \{\infty\}$ (`ℕ∞`). Argument: the number of variables `n`. -/
noncomputable def minGenusClasses (n : ℕ) : ℕ∞ :=
  ⨅ Q : {Q : QuadForm ℤ n // IntQF.PosDef Q}, (genusClasses Q.1).encard

/-- **Cassels, Appendix A, Theorem 3.1 (Watson):** the minimum number $c(n)$ of classes in a genus of positive definite
integer-valued forms in $n$ variables tends to infinity with $n$. -/
@[kb "cassels1978" "App. A, §3, Thm. 3.1, p. 364"]
def WatsonStatement : Prop :=
  Filter.Tendsto minGenusClasses Filter.atTop (nhds ⊤)

/-- **Unfolding:** `WatsonStatement` says that for every $N$, for all large $n$, every genus of positive definite
integer-valued forms in $n$ variables has at least $N$ classes. -/
theorem watsonStatement_iff : WatsonStatement ↔
    ∀ N : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ Q : QuadForm ℤ n, IntQF.PosDef Q → (N : ℕ∞) ≤ (genusClasses Q).encard := by
  unfold WatsonStatement
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  constructor
  · intro h N
    obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (h N)
    refine ⟨n₀, fun n hn Q hQ => ?_⟩
    exact (hn₀ n hn).le.trans (iInf_le _ (⟨Q, hQ⟩ : {Q : QuadForm ℤ n // IntQF.PosDef Q}))
  · intro h N
    obtain ⟨n₀, hn₀⟩ := h (N + 1)
    refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn => ?_⟩
    have : ((N + 1 : ℕ) : ℕ∞) ≤ minGenusClasses n :=
      le_iInf fun Q => hn₀ n hn Q.1 Q.2
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N) this

/-! ### Watson's operation as a map of forms -/

/-- **The derived form of Watson's operation** (Cassels, App. A, §3, p. 365): $Q'$ in $n$ variables is *derived from*
$Q$ at the prime $p$ if there is an integer matrix `g` with non-zero determinant whose columns span (over $\mathbb Z$)
the lattice $\Lambda_p$ = `watsonSub Q p`, and $Q(g\vec x) = p\,Q'(\vec x)$ for all $\vec x \in \mathbb Z^n$, i.e. $Q'$
is $\psi = p^{-1}\phi$ on $\Lambda_p$ written in a basis. Arguments: `Q` the form, `p` the prime, `Q'` the derived
form. -/
def IsWatsonDerived (Q : QuadForm ℤ n) (p : ℕ) (Q' : QuadForm ℤ n) : Prop :=
  p.Prime ∧ ∃ g : Matrix (Fin n) (Fin n) ℤ, g.det ≠ 0 ∧
    Set.range g.mulVec = (watsonSub Q (p : ℤ) : Set (Fin n → ℤ)) ∧
    ∀ x, Q.eval (g *ᵥ x) = (p : ℤ) * Q'.eval x

/-- **Chains of Watson operations** (possibly with different primes, p. 365): the reflexive-transitive closure of
"derived from at some prime". -/
def WatsonReach (Q Q' : QuadForm ℤ n) : Prop :=
  Relation.ReflTransGen (fun A B : QuadForm ℤ n => ∃ p : ℕ, IsWatsonDerived A p B) Q Q'

/-- **Helper:** a derived form of a positive definite form is positive definite. -/
theorem IsWatsonDerived.posDef {Q Q' : QuadForm ℤ n} {p : ℕ} (h : IsWatsonDerived Q p Q')
    (hQ : IntQF.PosDef Q) : IntQF.PosDef Q' := by
  obtain ⟨hp, g, hg, -, hQg⟩ := h
  intro x hx
  have hgx : g *ᵥ x ≠ 0 := fun h0 => hx (Matrix.eq_zero_of_mulVec_eq_zero hg h0)
  have h1 := hQ _ hgx
  rw [hQg] at h1
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  exact (pos_iff_pos_of_mul_pos h1).mp hp0

/-! ### The two cited steps of the proof, as named inputs -/

/-- **Input (Cassels p. 365, "Hence the genus $\mathcal G_p$ of $\Lambda_p, \psi$ contains at most as many classes as
the genus $\mathcal G$ of $\Lambda, \phi$").** For every positive definite $Q$ in $n$ variables and every form $Q'$
derived from $Q$ at a prime $p$, the genus of $Q'$ has at most as many classes as the genus of $Q$. Cited, not proved
here (Cassels sketches the construction of the lattice $\Lambda' \supseteq \Lambda'_p$ in the footnote).
**Proved** in `AppA/WatsonMonotone.lean` (`watsonOperationMonotone_holds`). -/
structure WatsonOperationMonotone : Prop where
  /-- For all `n`, positive definite `Q` in `n` variables, primes `p` and forms `Q'` derived from `Q` at `p`:
  the genus of `Q'` has at most as many classes as the genus of `Q`. -/
  monotone : ∀ (n : ℕ) (Q Q' : QuadForm ℤ n) (p : ℕ), IntQF.PosDef Q → IsWatsonDerived Q p Q' →
    (genusClasses Q').encard ≤ (genusClasses Q).encard

/-- **Input (Cassels p. 366, the local study).** Every positive definite form $Q$ in $n$ variables can be taken by a
chain of Watson operations to a form $Q^*$ whose genus contains $r\Gamma_8 \perp \Lambda'$, with $\Lambda'$ a positive
definite form in $m = n - 8r$ variables and $16 r \ge n - 6$ (Cassels, p. 366: "$r \ge (n-6)/16$", page image; only
$r \to \infty$ as $n \to \infty$ is used below). The orthogonal sum has $8r + m$ variables, `h : 8 * r + m = n`
transports it to $n$ variables. Cited, not proved here (Ch. 8, Ex. 8). -/
structure WatsonLocalStudy : Prop where
  /-- For all `n` and positive definite `Q` in `n` variables there are `Qs` reachable from `Q` by Watson operations,
  `r` copies of $E_8$ and a positive definite `Λ'` in `m = n - 8r` variables with `n ≤ 16 r + 6` and `Qs` in the
  genus of $r E_8 \perp \Lambda'$. -/
  reach : ∀ (n : ℕ) (Q : QuadForm ℤ n), IntQF.PosDef Q →
    ∃ (Qs : QuadForm ℤ n) (r m : ℕ) (Λ' : QuadForm ℤ m) (h : 8 * r + m = n),
      WatsonReach Q Qs ∧ IntQF.PosDef Λ' ∧ n ≤ 16 * r + 6 ∧
        SameGenus Qs (h ▸ QuadForm.orthSum (repE8 r) Λ')

/-! ### Assembly -/

/-- **Helper:** along a chain of Watson operations from a positive definite form, the end form is positive definite
and its genus has at most as many classes. -/
theorem WatsonReach.encard_le (hA : WatsonOperationMonotone) {Q Qs : QuadForm ℤ n} (hQ : IntQF.PosDef Q)
    (h : WatsonReach Q Qs) : IntQF.PosDef Qs ∧ (genusClasses Qs).encard ≤ (genusClasses Q).encard := by
  induction h with
  | refl => exact ⟨hQ, le_rfl⟩
  | tail _ hstep ih =>
    obtain ⟨p, hp⟩ := hstep
    exact ⟨hp.posDef ih.1, (hA.monotone _ _ _ p ih.1 hp).trans ih.2⟩

/-- **Cassels, App. A, Theorem 3.1, from the two remaining cited steps of the sketch:** if Watson's operation does not
increase the class number (`WatsonOperationMonotone`) and the local study reaches a genus containing $r\Gamma_8 \perp
\Lambda'$ with $16 r \ge n - 6$ (`WatsonLocalStudy`), then $c(n) \to \infty$; the count $1 + [r/2]$ of classes is
proved (`encard_genus_ge`). *Proof:* given $N$, take $n_0 = 32 N + 6$; then $r \ge 2N$ and $1 + [r/2] \ge N$. -/
@[kb "cassels1978" "App. A, §3, Thm. 3.1, pp. 364-366 (proof sketch, conditional on two named steps)"]
theorem watson_of_inputs (hA : WatsonOperationMonotone) (hB : WatsonLocalStudy) :
    WatsonStatement := by
  rw [watsonStatement_iff]
  intro N
  refine ⟨32 * N + 6, fun n hn Q hQ => ?_⟩
  obtain ⟨Qs, r, m, Λ', h, hreach, hΛ, hr, hgen⟩ := hB.reach n Q hQ
  subst h
  obtain ⟨hQs, hle⟩ := hreach.encard_le hA hQ
  rw [genusClasses_eq_of_sameGenus hgen] at hle
  have hc := encard_genus_ge r Λ' hΛ
  have hNr : N ≤ 1 + r / 2 := by omega
  exact (Nat.cast_le.mpr hNr).trans (hc.trans hle)

end Statement

end QuadFormsKB.DefiniteForms
