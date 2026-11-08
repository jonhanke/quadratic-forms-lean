/-
# Conway–Sloane 1988, §10: the vine graph on genera

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §10 "Verification of the results of part I", p. 274:

> We form a graph, in which each node represents a genus, and nodes for genera containing lattices $L$ and
> $L \oplus I_1$ are joined by an edge. In view of lemma 3 [of §11], this graph has the following structure. Each
> connected component of the graph is a tree consisting of a single path (the 'stem'), the nodes of which represent odd
> genera, together with other nodes representing even genera that are joined to the stem by single edges (the
> 'twigs'). There is at most one twig at any stem node.

(*Erratum:* the paper says "lemma 3 of §13"; the lemma is Lemma 3 of §11.)

**Conventions.** A lattice is a positive definite integral Gram matrix `A : Matrix (Fin n) (Fin n) ℤ`
(`PosDefGram A`); its genus is its class under `Siegel.SameGenus` of the forms `ofMatrixZ A`. $L \oplus I_1$ is
`sumOne A` (dimension $n + 1$, the new coordinate last). The type is `gramType A` ($1$ odd, $2$ even). The edge
relation of the graph, oriented from dimension $n$ to dimension $n + 1$, is `VineEdge A B`: $B$ lies in the genus of
$A \oplus I_1$. It depends only on the genera of $A$ and $B$ (`vineEdge_congr`). Every edge joins dimensions $n$ and
$n + 1$, so the graph is the graph of the map "genus of $L$ $\mapsto$ genus of $L \oplus I_1$".

**Proves** (all unconditional; §10, remark 1)
* `sameGenus_sumOne`: the genus of $L \oplus I_1$ depends only on the genus of $L$.
* `vine_structure`: the local structure that makes each component a stem with twigs:
  (1) every genus has exactly one neighbour one dimension up (the genus of $L \oplus I_1$), and it is odd;
  (2) an even genus has no neighbour one dimension down (twigs are leaves);
  (3) a genus has at most one neighbour one dimension down of each type: at most one odd one (the stem continues
      downwards in at most one way) and at most one even one (at most one twig per stem node) — this is Lemma 3;
  (4) joined genera have the same determinant.
  Since each node has exactly one upward neighbour and the dimension increases by one along it, every component is a
  tree; by (1)–(3) its odd nodes form a single path and its even nodes are leaves attached to it, at most one at each
  node.
* `Genus`, `Genus.up`, `vineGraph`: the graph itself, on genera (a dimension and a same-genus class);
  `vineGraph_isAcyclic` (every component is a tree) and `vineGraph_structure` (the same statement as
  `vine_structure`, on the graph).
* `vine_lattices` (§10, remark 2): the $n$-dimensional lattices of a vine are exactly the $L_r \oplus I_{n-r}$ with
  $L_r$ marked on the vine (no vectors of norm $1$); from `exists_sumI_no_norm_one` (`VineLattices.lean`). This does
  not use Part I's enumeration.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemmasHold
import QuadFormsKB.Literature.ConwaySloane.Mass.VineLattices

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa.Frames QuadFormsKB.Cassels

namespace QuadFormsKB.ConwaySloane.Mass

variable {n : ℕ}

/-- **The genus of $L \oplus I_1$ depends only on the genus of $L$**: if $L$, $M$ are in the same genus then so are
$L \oplus I_1$ and $M \oplus I_1$. -/
@[kb "conwaysloane1988" "§10, remark 1, p. 274 (vines)"]
theorem sameGenus_sumOne {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B)
    (h : SameGenus (ofMatrixZ A) (ofMatrixZ B)) : SameGenus (ofMatrixZ (sumOne A)) (ofMatrixZ (sumOne B)) := by
  have hA' := hA.sumOne
  have hB' := hB.sumOne
  refine ⟨fun p _ => ?_, ?_⟩
  · have hp := (isometricGL_padic_iff hA.1 hB.1).1 (h.1 p)
    refine (isometricGL_padic_iff hA'.1 hB'.1).2 ?_
    have e : ∀ C : Matrix (Fin n) (Fin n) ℤ, (sumOne C).map (Int.castRingHom ℚ_[p]) =
        orthSumMat (C.map (Int.castRingHom ℚ_[p])) !![(1 : ℚ_[p])] := fun C => by
      rw [← oneGram_map]; exact Ex5.map_orthSum _ C oneGram
    rw [e, e]
    exact zpEquiv_orthSumMat hp _
  · refine Siegel.isometricGL_real_of_posDef ⟨sumOne A, hA'.1, fun x => LocalDensity.eval_ofMatrixZ _ x⟩
      ⟨sumOne B, hB'.1, fun x => LocalDensity.eval_ofMatrixZ _ x⟩ (fun x hx => ?_) (fun x hx => ?_)
    · rw [LocalDensity.eval_ofMatrixZ]; exact hA'.pos_int hx
    · rw [LocalDensity.eval_ofMatrixZ]; exact hB'.pos_int hx

/-- **The edges of the vine graph** (§10, p. 274), oriented upwards: the genus of $L$ (Gram matrix $A$, dimension $n$)
is joined to the genus of $M$ (Gram matrix $B$, dimension $n + 1$) iff $M$ is in the genus of $L \oplus I_1$. -/
@[kb "conwaysloane1988" "§10, remark 1, p. 274 (vines)"]
def VineEdge (A : Matrix (Fin n) (Fin n) ℤ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : Prop :=
  SameGenus (ofMatrixZ (sumOne A)) (ofMatrixZ B)

/-- `VineEdge` is a relation between genera: it depends only on the genera of its two ends. -/
theorem vineEdge_congr {A A' : Matrix (Fin n) (Fin n) ℤ} {B B' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ}
    (hA : PosDefGram A) (hA' : PosDefGram A') (h1 : SameGenus (ofMatrixZ A) (ofMatrixZ A'))
    (h2 : SameGenus (ofMatrixZ B) (ofMatrixZ B')) (h : VineEdge A B) : VineEdge A' B' :=
  ((sameGenus_sumOne hA hA' h1).symm.trans h).trans h2

/-- Same genus gives the same determinant (positive definite lattices): $|L^*/L| = \det$. -/
theorem det_eq_of_sameGenus {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B)
    (h : SameGenus (ofMatrixZ A) (ofMatrixZ B)) : A.det.natAbs = B.det.natAbs := by
  obtain ⟨φ, _⟩ := (lemma2_only_if hA hB h).2
  rw [← card_discGroup hA.det_ne, ← card_discGroup hB.det_ne]
  exact Nat.card_congr φ.toEquiv

theorem det_sumOne (A : Matrix (Fin n) (Fin n) ℤ) : (sumOne A).det = A.det := by
  have : sumOne A = orthSumMat A (1 : Matrix (Fin 1) (Fin 1) ℤ) := rfl
  rw [this, det_orthSumMat, det_one, mul_one]

/-- **§10, remark 1 (p. 274): the structure of the vine graph** (unconditional). For positive definite integral
lattices:
1. *exactly one upward neighbour, odd*: the genus of $L$ is joined to that of $L \oplus I_1$, any two upward
   neighbours are the same genus, and every upward neighbour is odd (type $1$);
2. *twigs are leaves*: an even genus (type $2$) has no downward neighbour;
3. *at most one downward neighbour of each type* (Lemma 3 of §11): if $L$ and $L'$ of the same type are both joined
   to $M$, they are in the same genus. So a stem node has at most one odd downward neighbour (the stem) and at most
   one even one (its twig);
4. *one determinant per vine*: joined genera have the same determinant. -/
@[kb "conwaysloane1988" "§10, remark 1, p. 274 (vines)"]
theorem vine_structure :
    (∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ), VineEdge A (sumOne A)) ∧
    (∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} {B B' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ},
      VineEdge A B → VineEdge A B' → SameGenus (ofMatrixZ B) (ofMatrixZ B')) ∧
    (∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ},
      PosDefGram A → PosDefGram B → VineEdge A B → gramType B = 1) ∧
    (∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ},
      PosDefGram A → PosDefGram B → gramType B = 2 → ¬ VineEdge A B) ∧
    (∀ {n : ℕ} {A A' : Matrix (Fin n) (Fin n) ℤ} {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ},
      PosDefGram A → PosDefGram A' → gramType A = gramType A' → VineEdge A B → VineEdge A' B →
      SameGenus (ofMatrixZ A) (ofMatrixZ A')) ∧
    (∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ},
      PosDefGram A → PosDefGram B → VineEdge A B → B.det.natAbs = A.det.natAbs) := by
  refine ⟨fun A => SameGenus.refl _, fun h h' => h.symm.trans h', fun hA hB h => ?_, fun hA hB h2 h => ?_,
    fun hA hA' ht h h' => lemma3 hA hA' (h.trans h'.symm) ht, fun hA hB h => ?_⟩
  · rw [← gramType_eq_of_sameGenus hA.sumOne.1 hB.1 h, gramType_sumOne]
  · have := gramType_eq_of_sameGenus hA.sumOne.1 hB.1 h
    rw [gramType_sumOne, h2] at this
    exact absurd this (by norm_num)
  · rw [← det_eq_of_sameGenus hA.sumOne hB h, det_sumOne]

/-! ### The vine graph as a graph on genera -/

/-- Same genus as a setoid on the positive definite integral Gram matrices of dimension $n$. -/
def genusSetoid (n : ℕ) : Setoid {A : Matrix (Fin n) (Fin n) ℤ // PosDefGram A} where
  r A B := SameGenus (ofMatrixZ A.1) (ofMatrixZ B.1)
  iseqv := ⟨fun _ => SameGenus.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- **A genus** of positive definite integral lattices: a dimension $n$ and a same-genus class of $n \times n$
positive definite integral Gram matrices. -/
def Genus : Type := Σ n : ℕ, Quotient (genusSetoid n)

/-- The genus of a positive definite integral Gram matrix. -/
def Genus.of (A : Matrix (Fin n) (Fin n) ℤ) (hA : PosDefGram A) : Genus := ⟨n, ⟦⟨A, hA⟩⟧⟩

/-- The dimension of a genus. -/
def Genus.dim (X : Genus) : ℕ := X.1

/-- The genus of $L \oplus I_1$, for $L$ in the genus $X$ (well defined by `sameGenus_sumOne`). -/
noncomputable def Genus.up (X : Genus) : Genus :=
  ⟨X.1 + 1, Quotient.map (fun A => ⟨sumOne A.1, A.2.sumOne⟩) (fun A B h => sameGenus_sumOne A.2 B.2 h) X.2⟩

/-- The type of a genus ($1$ odd, $2$ even; well defined by `gramType_eq_of_sameGenus`). -/
noncomputable def Genus.type (X : Genus) : ℕ :=
  Quotient.lift (fun A => gramType A.1) (fun A B h => gramType_eq_of_sameGenus A.2.1 B.2.1 h) X.2

/-- The determinant of a genus (well defined by `det_eq_of_sameGenus`). -/
def Genus.det (X : Genus) : ℕ :=
  Quotient.lift (fun A => A.1.det.natAbs) (fun A B h => det_eq_of_sameGenus A.2 B.2 h) X.2

@[simp] theorem Genus.dim_up (X : Genus) : X.up.dim = X.dim + 1 := rfl

theorem Genus.up_of (A : Matrix (Fin n) (Fin n) ℤ) (hA : PosDefGram A) :
    (Genus.of A hA).up = Genus.of (sumOne A) hA.sumOne := rfl

theorem Genus.type_up (X : Genus) : X.up.type = 1 := by
  obtain ⟨n, q⟩ := X
  induction q using Quotient.inductionOn with
  | h A => exact gramType_sumOne A.1

theorem Genus.det_up (X : Genus) : X.up.det = X.det := by
  obtain ⟨n, q⟩ := X
  induction q using Quotient.inductionOn with
  | h A => show (sumOne A.1).det.natAbs = A.1.det.natAbs; rw [det_sumOne]

/-- **Lemma 3 on genera**: two genera of the same type with the same `up` are equal. -/
theorem Genus.up_injective_of_type {X Y : Genus} (ht : X.type = Y.type) (h : X.up = Y.up) : X = Y := by
  obtain ⟨n, q⟩ := X
  obtain ⟨m, q'⟩ := Y
  have hnm : n = m := by have := congrArg Sigma.fst h; simp only [Genus.up] at this; omega
  subst hnm
  induction q using Quotient.inductionOn with
  | h A =>
  induction q' using Quotient.inductionOn with
  | h B =>
  have h2 := eq_of_heq (Sigma.mk.inj h).2
  have hg : SameGenus (ofMatrixZ (sumOne A.1)) (ofMatrixZ (sumOne B.1)) := Quotient.exact h2
  exact congrArg (Sigma.mk n) (Quotient.sound (lemma3 A.2 B.2 hg ht))

/-- **The vine graph** (§10, p. 274): genera, with the genus of $L$ joined to the genus of $L \oplus I_1$. -/
@[kb "conwaysloane1988" "§10, remark 1, p. 274 (vines)"]
def vineGraph : SimpleGraph Genus where
  Adj X Y := Y = X.up ∨ X = Y.up
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun X h => by
    rcases h with h | h <;> · have := congrArg Genus.dim h; simp at this⟩

theorem vineGraph_adj_of {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A)
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hB : PosDefGram B) :
    vineGraph.Adj (Genus.of A hA) (Genus.of B hB) ↔ VineEdge A B := by
  constructor
  · rintro (h | h)
    · have h2 := eq_of_heq (Sigma.mk.inj h).2
      exact (Quotient.exact h2 : SameGenus (ofMatrixZ B) (ofMatrixZ (sumOne A))).symm
    · have := congrArg Genus.dim h; rw [Genus.dim_up] at this; simp [Genus.of, Genus.dim] at this; omega
  · intro h
    exact Or.inl (congrArg (Sigma.mk (n + 1)) (Quotient.sound h.symm))

theorem vineGraph_adj_dim {X Y : Genus} (h : vineGraph.Adj X Y) (hle : X.dim ≤ Y.dim) : Y = X.up := by
  rcases h with h | h
  · exact h
  · have := congrArg Genus.dim h; simp at this; omega

/-- **The vine graph is acyclic**: every connected component is a tree. (Take a vertex of least dimension on a
cycle; both its neighbours on the cycle have larger dimension, so both are its `up`, but they are distinct.) -/
theorem vineGraph_isAcyclic : vineGraph.IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨u, hu, hmin⟩ : ∃ u ∈ c.support, ∀ w ∈ c.support, u.dim ≤ w.dim := by
    obtain ⟨u, hu, hmin⟩ := c.support.toFinset.exists_min_image Genus.dim ⟨v, by simp⟩
    exact ⟨u, by simpa using hu, fun w hw => hmin w (by simpa using hw)⟩
  set c' := c.rotate u hu
  have hc' : c'.IsCycle := hc.rotate hu
  have hnil := hc'.not_nil
  have hmem : ∀ w ∈ c'.support, u.dim ≤ w.dim := fun w hw =>
    hmin w ((SimpleGraph.Walk.mem_support_rotate_iff c u hu).1 hw)
  have h1 : c'.snd = u.up :=
    vineGraph_adj_dim (SimpleGraph.Walk.adj_snd hnil) (hmem _ (c'.getVert_mem_support 1))
  have h2 : c'.penultimate = u.up :=
    vineGraph_adj_dim (SimpleGraph.Walk.adj_penultimate hnil).symm
      (hmem _ (c'.getVert_mem_support _))
  exact hc'.snd_ne_penultimate (h1.trans h2.symm)

/-- **§10, remark 1 (p. 274), as a statement about the graph on genera** (unconditional): the vine graph is a
forest (each connected component is a tree); every genus has exactly one neighbour of larger dimension, namely
`up` ($L \mapsto L \oplus I_1$), which is odd; an even genus is a leaf (its only neighbour is its `up`, a stem
node: the twigs); a genus has at most one neighbour of smaller dimension of each type — at most one odd (so the odd
genera of a component, each with at most two odd neighbours, form a single path: the stem) and at most one even
(at most one twig at any stem node); and the determinant is constant along edges. -/
@[kb "conwaysloane1988" "§10, remark 1, p. 274 (vines)"]
theorem vineGraph_structure :
    vineGraph.IsAcyclic ∧
    (∀ X Y : Genus, vineGraph.Adj X Y → X.dim ≤ Y.dim → Y = X.up) ∧
    (∀ X : Genus, vineGraph.Adj X X.up ∧ X.up.type = 1 ∧ X.up.dim = X.dim + 1) ∧
    (∀ X : Genus, X.type = 2 → ∀ Y, vineGraph.Adj X Y ↔ Y = X.up) ∧
    (∀ X Y Y' : Genus, Y.up = X → Y'.up = X → Y.type = Y'.type → Y = Y') ∧
    (∀ X Y : Genus, vineGraph.Adj X Y → X.det = Y.det) := by
  refine ⟨vineGraph_isAcyclic, fun X Y h hle => vineGraph_adj_dim h hle,
    fun X => ⟨Or.inl rfl, X.type_up, rfl⟩, fun X hX Y => ⟨fun h => ?_, fun h => Or.inl h⟩,
    fun X Y Y' h h' ht => Genus.up_injective_of_type ht (h.trans h'.symm), fun X Y h => ?_⟩
  · rcases h with h | h
    · exact h
    · have := Genus.type_up Y; rw [← h, hX] at this; exact absurd this (by norm_num)
  · rcases h with h | h
    · rw [h, Genus.det_up]
    · rw [h, Genus.det_up]

/-! ### The lattices of a vine (§10, p. 274) -/

theorem Genus.of_congr {A B : Matrix (Fin n) (Fin n) ℤ} (h : A = B) (hA : PosDefGram A) (hB : PosDefGram B) :
    Genus.of A hA = Genus.of B hB := by subst h; rfl

/-- The genus of $L \oplus I_k$ is reached from the genus of $L$ by $k$ upward edges of the vine. -/
theorem Genus.of_sumI {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (hL : PosDefGram L) (k : ℕ) :
    Genus.of (sumI L k) (hL.sumI k) = Genus.up^[k] (Genus.of L hL) := by
  induction k with
  | zero => exact Genus.of_congr (sumI_zero L) _ _
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, Genus.up_of]
    exact (Genus.of_congr (sumOne_sumI L k) _ _).symm

/-- **§10, remark 2 (p. 274): the lattices of a vine.** "The complete set of $n$-dimensional lattices in a given
vine then consists of all direct sums $L_r \oplus I_{n-r}$, where $L_r$ is any $r$-dimensional lattice ($r \le n$)
that is marked on the vine" (the marked lattices are those with no vectors of norm $1$). Unconditional, and
independent of Part I's enumeration:
1. every positive definite integral lattice $M$ of dimension $n$ is integrally equivalent to $L_r \oplus I_{n-r}$ for
   some lattice $L_r$ with no vectors of norm $1$, and the genus of $M$ is reached from the genus of $L_r$ by $n - r$
   upward edges, so $L_r$ is marked on the vine of $M$;
2. conversely, for every lattice $L_r$ and every $k$, $L_r \oplus I_k$ lies in the vine of $L_r$, $k$ edges above
   $L_r$. -/
@[kb "conwaysloane1988" "§10, remark 2, p. 274 (vines)"]
theorem vine_lattices :
    (∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : PosDefGram A),
      ∃ (r k : ℕ) (h : r + k = n) (L : Matrix (Fin r) (Fin r) ℤ) (hL : PosDefGram L),
        (∀ x, x ⬝ᵥ (L *ᵥ x) ≠ 1) ∧
        IntEquiv (ofMatrixZ A) (ofMatrixZ ((sumI L k).reindex (finCongr h) (finCongr h))) ∧
        Genus.of A hA = Genus.up^[k] (Genus.of L hL)) ∧
    (∀ {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (hL : PosDefGram L) (k : ℕ),
      Genus.of (sumI L k) (hL.sumI k) = Genus.up^[k] (Genus.of L hL)) := by
  refine ⟨fun A hA => ?_, Genus.of_sumI⟩
  obtain ⟨r, k, h, L, hL, h1, he⟩ := exists_sumI_no_norm_one hA
  refine ⟨r, k, h, L, hL, h1, he, ?_⟩
  subst h
  rw [reindex_finCongr_rfl] at he
  rw [← Genus.of_sumI L hL k]
  exact congrArg (Sigma.mk (r + k)) (Quotient.sound he.sameGenus)

end QuadFormsKB.ConwaySloane.Mass
