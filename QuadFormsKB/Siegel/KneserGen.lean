/-
# Kneser neighbours, part 7: a computable $p$-neighbour generator and equivalence search

**Layer:** integral forms (`QuadForm ℤ n`) as data; everything here is computable and meant to be run with `#eval`.
**Nothing in this file is trusted:** its outputs are certificates (`NbCert`, `IsoCert`, `Siegel/KneserCert.lean`) that
Lean re-checks with `decide`. A bug here can only make a certificate fail to check, never prove a false statement.

**Defines**
- `allVecs p n`: all $\vec{u} \in \{0, \dots, p-1\}^n$ (proved complete: `mem_allVecs`);
- `isoLines Q p`: one representative (first nonzero coordinate $1$) of each isotropic line of $\mathbb{F}_p^n$;
- `liftIso Q p u`: a lift $\vec{v} \equiv \vec{u}$ with $p^2 \mid Q(\vec{v})$ (one Hensel step, $\vec{v} = \vec{u} + pt\,\vec{e}_j$ with
  $B(\vec{u}, \vec{e}_j) \not\equiv 0$);
- `latBasis`: a triangular basis of the lattice spanned by finitely many integer vectors (gcd elimination);
- `nbData H n p u`: the full neighbour certificate of the line $\mathbb{F}_p\vec{u}$ (basis $G$ of $pL(\vec{v})$ and all
  coordinates), and `gramHess`: the Hessian $H'$ with $G^{\mathsf T}HG = p^2H'$;
- `findIso n H H' B`: a backtracking search for $M \in \mathrm{GL}_n(\mathbb{Z})$ with $M^{\mathsf T}H_QM = H_{Q'}$ whose columns
  lie in the box $[-B, B]^n$ (columns $\vec{m}_j$ with $Q(\vec{m}_j) = Q'(\vec{e}_j)$, pruned by $B(\vec{m}_i, \vec{m}_j)$);
  together with `AM.intInverse` (adjugate) it yields an `IsoCert`.

This is the method of Kneser 1957 and its implementations (Schulze-Pillot 1991; Scharlau–Hemkemeier 1998): enumerate
isotropic lines mod $p$, build the neighbours, reduce them to known classes by an equivalence test.
-/
import QuadFormsKB.Siegel.KneserCert

open Matrix

namespace QuadFormsKB.Siegel.Kneser.Gen

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### Enumerating vectors mod $p$ -/

/-- All vectors in $\{0, \dots, p-1\}^n$ (as integer vectors). -/
def allVecs (p : ℕ) : (n : ℕ) → List (Fin n → ℤ)
  | 0 => [Fin.elim0]
  | n + 1 => (allVecs p n).flatMap fun v => (List.range p).map fun a : ℕ => Fin.cons (Int.ofNat a) v

/-- **Completeness of `allVecs`:** every $\vec{u}$ with $0 \le u_i < p$ is listed. -/
theorem mem_allVecs {p : ℕ} : ∀ {n : ℕ} (u : Fin n → ℤ), (∀ i, 0 ≤ u i ∧ u i < p) → u ∈ allVecs p n
  | 0, u, _ => by simp [allVecs]; exact funext fun i => i.elim0
  | n + 1, u, h => by
    simp only [allVecs, List.mem_flatMap, List.mem_map]
    refine ⟨Fin.tail u, mem_allVecs _ fun i => h i.succ, (u 0).toNat, ?_, ?_⟩
    · rw [List.mem_range]; have := h 0; omega
    · rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (h 0).1]; exact Fin.cons_self_tail u

/-- The modular inverse of $a$ modulo $p$ (for $\gcd(a, p) = 1$), in $[0, p)$. -/
def invMod (a : ℤ) (p : ℕ) : ℤ := (Int.gcdA a p) % p

/-! ### Array arithmetic

The search works on arrays (`Array ℤ` vectors, `Array (Array ℤ)` matrices by rows) so that intermediate results are
stored, not recomputed through nested closures. -/

/-- A vector, as an array of length $n$. -/
abbrev AV := Array ℤ
/-- A matrix, as an array of rows. -/
abbrev AM := Array (Array ℤ)

/-- Entry $i$ of a vector (default $0$). -/
def vget (x : AV) (i : ℕ) : ℤ := x.getD i 0
/-- Entry $(i, j)$ of a matrix (default $0$). -/
def mget (M : AM) (i j : ℕ) : ℤ := (M.getD i #[]).getD j 0
/-- $\vec{x} \cdot \vec{y}$. -/
def vdot (x y : AV) : ℤ := (List.range x.size).foldl (fun s i => s + vget x i * vget y i) 0
/-- $M\vec{x}$. -/
def mmulVec (M : AM) (x : AV) : AV := M.map fun r => vdot r x
/-- Column $j$ of $M$. -/
def mcol (M : AM) (j : ℕ) : AV := M.map fun r => r.getD j 0
/-- The matrix with the given columns. -/
def mofCols (n : ℕ) (cs : List AV) : AM :=
  Array.ofFn fun (i : Fin n) => Array.ofFn fun (j : Fin n) => vget (cs.getD j #[]) i
/-- $M^{\mathsf T}AM$ for a symmetric $A$, entrywise $\vec{m}_i^{\mathsf T}A\vec{m}_j$. -/
def mconj (n : ℕ) (A M : AM) : AM :=
  Array.ofFn fun (i : Fin n) => Array.ofFn fun (j : Fin n) => vdot (mcol M i) (mmulVec A (mcol M j))
/-- The Hessian of $Q$ as an array matrix. -/
def hessA (Q : QuadForm ℤ n) : AM := Array.ofFn fun i => Array.ofFn fun j => Q.hessian i j
/-- $Q(\vec{x}) = \frac12\vec{x}^{\mathsf T}H\vec{x}$. -/
def evalA (H : AM) (x : AV) : ℤ := vdot x (mmulVec H x) / 2
/-- $a\vec{x}$. -/
def vsmul (a : ℤ) (x : AV) : AV := x.map (a * ·)
/-- $\vec{x} - \vec{y}$. -/
def vsub (x y : AV) : AV := Array.ofFn fun (i : Fin x.size) => vget x i - vget y i
/-- The unit vector $\vec{e}_i$. -/
def vunit (n i : ℕ) : AV := Array.ofFn fun (j : Fin n) => if (j : ℕ) = i then 1 else 0
/-- The first index $< n$ satisfying a Boolean predicate. -/
def firstIdxA (n : ℕ) (P : ℕ → Bool) : Option ℕ := (List.range n).find? P

/-! ### Isotropic lines and lifts -/

/-- All vectors in $\{0, \dots, p-1\}^n$ as arrays. -/
def allVecsA (p : ℕ) : ℕ → List AV
  | 0 => [#[]]
  | n + 1 => (allVecsA p n).flatMap fun v => (List.range p).map fun a : ℕ => #[(a : ℤ)] ++ v

/-- Is $\vec{u}$ the normalized representative of its line (first nonzero coordinate $= 1$)? -/
def isLineRep (u : AV) : Bool :=
  match firstIdxA u.size (fun i => vget u i != 0) with
  | none => false
  | some i => vget u i == 1

/-- **Representatives of the isotropic lines** of $\mathbb{F}_p^n$ for $Q$ (first nonzero coordinate $1$). -/
def isoLines (Q : QuadForm ℤ n) (p : ℕ) : List AV :=
  let H := hessA Q
  (allVecsA p n).filter fun u => isLineRep u && (evalA H u % (p : ℤ) == 0)

/-- **Hensel lift** of an isotropic $\vec{u}$ to $\vec{v} \equiv \vec{u} \pmod p$ with $p^2 \mid Q(\vec{v})$, and the index $j$ used
($B(\vec{u}, \vec{e}_j) \not\equiv 0 \bmod p$). -/
def liftIso (H : AM) (n p : ℕ) (u : AV) : AV × ℕ :=
  let w := mmulVec H u
  match firstIdxA n (fun j => vget w j % (p : ℤ) != 0) with
  | none => (u, 0)
  | some j =>
    let s := evalA H u / p
    let t := (-s * invMod (vget w j) p) % p
    (u.set! j (vget u j + p * t), j)

/-! ### Lattice bases by gcd elimination -/

/-- One elimination round at coordinate `i`: a pivot (smallest nonzero $|x_i|$ after repeated reduction) and the
remaining vectors, whose coordinate `i` is $0$. Fuel bounds the Euclidean steps. -/
def elimAt (i : ℕ) : ℕ → List AV → Option AV × List AV
  | 0, vs => (none, vs)
  | fuel + 1, vs =>
    let nz := vs.filter fun x => vget x i != 0
    let z := vs.filter fun x => vget x i == 0
    match nz with
    | [] => (none, z)
    | m₀ :: rest =>
      let m := rest.foldl (fun m x => if (vget x i).natAbs < (vget m i).natAbs then x else m) m₀
      let others := (nz.filter fun x => x != m) ++ ((nz.filter fun x => x == m).drop 1)
      let red := others.map fun x => vsub x (vsmul (vget x i / vget m i) m)
      if red.all (fun x => vget x i == 0) then (some m, z ++ red)
      else
        match elimAt i fuel (m :: red) with
        | (piv, rest') => (piv, z ++ rest')

/-- **A basis of the lattice spanned by `vs`** (assumed of full rank $n$): pivots at coordinates $0, \dots, n-1$; the
$j$-th basis vector vanishes at the coordinates $< j$ (as columns: a lower-triangular matrix). -/
def latBasis (n : ℕ) (vs : List AV) : List AV :=
  ((List.range n).foldl (fun (acc : List AV × List AV) i =>
    match elimAt i 200 acc.2 with
    | (some piv, rest) => (acc.1 ++ [if vget piv i < 0 then vsmul (-1) piv else piv], rest)
    | (none, rest) => (acc.1, rest)) ([], vs)).1

/-- **Solve $G\vec{c} = \vec{t}$** for a lower-triangular $G$ (forward substitution with exact division; only meaningful
when the solution is integral, which the certificate check verifies). -/
def solveLower (n : ℕ) (G : AM) (t : AV) : AV :=
  (List.range n).foldl (fun (acc : AV) r =>
    let s := (List.range r).foldl (fun s j => s + mget G r j * vget acc j) 0
    acc.push ((vget t r - s) / mget G r r)) #[]

/-! ### The neighbour certificate -/

/-- The data of a neighbour certificate, as arrays: $(\vec{v}, G, \vec{k}, \vec{w}, A, \vec{c}_w, \vec{c}_v, K)$. -/
structure NbData where
  /-- $\vec{v}$. -/
  v : AV
  /-- $G$. -/
  G : AM
  /-- $\vec{k}$. -/
  k : AV
  /-- $\vec{w}$. -/
  w : AV
  /-- $A$. -/
  A : AM
  /-- $\vec{c}_w$. -/
  cW : AV
  /-- $\vec{c}_v$. -/
  cV : AV
  /-- $K$. -/
  K : AM

/-- **The neighbour certificate of the line $\mathbb{F}_p\vec{u}$** ($\vec{u}$ isotropic mod $p$, $p \nmid \det H$): lift $\vec{u}$ to
$\vec{v}$, take $\vec{w} = B(\vec{v}, \vec{e}_j)^{-1}\vec{e}_j$, a basis $G$ of $pL(\vec{v})$ spanned by $p(\vec{e}_i - u_i\vec{w})$, $p^2\vec{w}$,
$\vec{v}$, and solve for all coordinates. -/
def nbData (H : AM) (n p : ℕ) (u : AV) : NbData :=
  let (v, j) := liftIso H n p u
  let hv := mmulVec H v
  let P : ℤ := p
  let w := vsmul (invMod (vget hv j) p) (vunit n j)
  let gens : List AV :=
    (List.range n).map (fun i => vsmul P (vsub (vunit n i) (vsmul (vget hv i) w))) ++ [vsmul (P * P) w, v]
  let G := mofCols n (latBasis n gens)
  let r := (firstIdxA n fun i => vget v i % P != 0).getD j
  let k : AV := Array.ofFn fun (c : Fin n) => (mget G r c * invMod (vget v r) p) % P
  let Acols := (List.range n).map fun c =>
    solveLower n G (vsmul P (vsub (vunit n c) (vsmul (vget hv c) w)))
  let Kcols := (List.range n).map fun c => solveLower n G (vsmul (P * P) (vunit n c))
  { v := v, G := G, k := k, w := w, A := mofCols n Acols, cW := solveLower n G (vsmul (P * P) w),
    cV := solveLower n G v, K := mofCols n Kcols }

/-- The Hessian $G^{\mathsf T}HG/p^2$ of the Gram form of a certified neighbour. -/
def gramHess (H : AM) (n p : ℕ) (d : NbData) : AM :=
  (mconj n H d.G).map fun r => r.map fun x => x / ((p : ℤ) * p)

/-! ### Equivalence search -/

/-- All vectors in the box $[-B, B]^n$. -/
def boxVecs (B : ℕ) : ℕ → List AV
  | 0 => [#[]]
  | n + 1 => (boxVecs B n).flatMap fun v => (List.range (2 * B + 1)).map fun a : ℕ => #[(a : ℤ) - B] ++ v

/-- Backtracking: extend the chosen columns `cols` by a column $\vec{m}$ with $\vec{m}^{\mathsf T}H\vec{m} = H'_{kk}$ and
$\vec{m}_i^{\mathsf T}H\vec{m} = H'_{ik}$. -/
def searchCols (n : ℕ) (H H' : AM) (cands : List AV) : ℕ → List AV → Option (List AV)
  | 0, cols => some cols
  | fuel + 1, cols =>
    let k := cols.length
    if k < n then
      (cands.filter fun m => vdot m (mmulVec H m) == mget H' k k &&
          (List.range k).all fun i => vdot (cols.getD i #[]) (mmulVec H m) == mget H' i k)
        |>.firstM fun m => searchCols n H H' cands fuel (cols ++ [m])
    else some cols

/-- Rounding of $a/b$ to a nearest integer ($b > 0$). -/
def roundDiv (a b : ℤ) : ℤ := (2 * a + b) / (2 * b)

/-- One pass of **pairwise (Lagrange) reduction** of the basis `us` (columns) for the Gram matrix $H$:
$\vec{u}_j \leftarrow \vec{u}_j - \mathrm{round}(B(\vec{u}_i, \vec{u}_j)/B(\vec{u}_i, \vec{u}_i))\,\vec{u}_i$ for all $i \ne j$, then sort by norm. -/
def reducePass (n : ℕ) (H : AM) (us : List AV) : List AV :=
  let us := (List.range n).foldl (fun us i => (List.range n).foldl (fun us j =>
      if i = j then us else
        let ui := us.getD i #[]
        let uj := us.getD j #[]
        let q := roundDiv (vdot ui (mmulVec H uj)) (vdot ui (mmulVec H ui))
        if q = 0 then us else us.set j (vsub uj (vsmul q ui))) us) us
  us.mergeSort fun a b => vdot a (mmulVec H a) ≤ vdot b (mmulVec H b)

/-- **A reducing change of basis** $U$ (columns) for the Gram matrix $H$: iterated `reducePass` from the identity. -/
def reduceGram (n : ℕ) (H : AM) : AM :=
  mofCols n ((List.range 30).foldl (fun us _ => reducePass n H us) ((List.range n).map (vunit n)))

/-- $M N$ for array matrices. -/
def mmul (n : ℕ) (M N : AM) : AM :=
  Array.ofFn fun (i : Fin n) => Array.ofFn fun (j : Fin n) => vdot (M.getD i #[]) (mcol N j)

/-- **Search for $M$ with $M^{\mathsf T}HM = H'$**: reduce $H$ to $H_r = U^{\mathsf T}HU$, search $M'$ with columns in $[-B, B]^n$ and $M'^{\mathsf T}H_rM' = H'$, return $M = UM'$. -/
def findIso (n : ℕ) (H H' : AM) (B : ℕ) : Option AM :=
  let U := reduceGram n H
  let Hr := mconj n H U
  let cands := (boxVecs B n).filter fun m => (List.range n).any fun k => vdot m (mmulVec Hr m) == mget H' k k
  (searchCols n Hr H' cands n []).map fun cols => mmul n U (mofCols n cols)

/-- The minor of $M$ without row $i$ and column $j$. -/
def mminor (M : AM) (i j : ℕ) : AM :=
  ((M.toList.eraseIdx i).map fun r => (r.toList.eraseIdx j).toArray).toArray

/-- Determinant by Laplace expansion along the first row (for small matrices). -/
def mdet : ℕ → AM → ℤ
  | 0, _ => 1
  | k + 1, M => (List.range (k + 1)).foldl (fun s j =>
      s + (if j % 2 = 0 then 1 else -1) * mget M 0 j * mdet k (mminor M 0 j)) 0

/-- The integer inverse $\det(M)\operatorname{adj}(M)$ of $M$ with $\det M = \pm 1$. -/
def mintInverse (n : ℕ) (M : AM) : AM :=
  let d := mdet n M
  Array.ofFn fun (i : Fin n) => Array.ofFn fun (j : Fin n) =>
    d * (if ((i : ℕ) + j) % 2 = 0 then 1 else -1) * mdet (n - 1) (mminor M j i)

/-- **Change of basis in a neighbour certificate:** replace the basis $G$ by $GM$ ($M \in \mathrm{GL}_n(\mathbb{Z})$ with inverse
$N$); the coordinates become $N A$, $N\vec{c}_w$, $N\vec{c}_v$, $NK$ and $\vec{k} \mapsto M^{\mathsf T}\vec{k} \bmod p$. If
$M^{\mathsf T}H'M = H''$ the new Gram form has Hessian $H''$. -/
def NbData.transform (n p : ℕ) (d : NbData) (M N : AM) : NbData :=
  let k : AV := Array.ofFn fun (j : Fin n) => (vdot (mcol M j) d.k) % (p : ℤ)
  ⟨d.v, mmul n d.G M, k, d.w, mmul n N d.A, mmulVec N d.cW, mmulVec N d.cV, mmul n N d.K⟩

/-- **A neighbour certificate whose Gram form is a given target** $T$ (Hessian `HT`), if the equivalence search succeeds:
the certificate of the line of $\vec{u}$, with the basis changed by the equivalence found. -/
def nbDataTo (H HT : AM) (n p B : ℕ) (u : AV) : Option NbData :=
  let d := nbData H n p u
  (findIso n (gramHess H n p d) HT B).map fun M => d.transform n p M (mintInverse n M)

/-! ### Conversion and printing -/

/-- An array vector as a function. -/
def vfun (x : AV) : Fin n → ℤ := fun i => vget x i
/-- An array matrix as a matrix. -/
def mmat (M : AM) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => mget M i j

/-- The certificate as a `NbCert`. -/
def NbData.toCert (d : NbData) : NbCert n :=
  ⟨vfun d.v, mmat d.G, vfun d.k, vfun d.w, mmat d.A, vfun d.cW, vfun d.cV, mmat d.K⟩

/-- The form with Hessian $H'$ (assumed even on the diagonal). -/
def formOfHess (H' : AM) : QuadForm ℤ n :=
  QuadForm.ofUpper fun i j => if i = j then mget H' i i / 2 else mget H' i j

/-- A vector as `![a, b, …]`. -/
def showAV (x : AV) : String := "![" ++ ", ".intercalate (x.toList.map toString) ++ "]"

/-- A matrix as `!![a, b; c, d]`. -/
def showAM (M : AM) : String :=
  "!![" ++ "; ".intercalate (M.toList.map fun r => ", ".intercalate (r.toList.map toString)) ++ "]"

/-- A neighbour certificate as a structure literal. -/
def showNb (d : NbData) : String :=
  "⟨" ++ ", ".intercalate [showAV d.v, showAM d.G, showAV d.k, showAV d.w, showAM d.A, showAV d.cW, showAV d.cV,
    showAM d.K] ++ "⟩"

/-- The upper-triangular coefficient matrix of the form with Hessian $H'$, as `!![…]` (for `QuadForm.ofUpper`). -/
def showFormOfHess (n : ℕ) (H' : AM) : String :=
  showAM (Array.ofFn fun (i : Fin n) => Array.ofFn fun (j : Fin n) =>
    if (i : ℕ) = j then mget H' i i / 2 else if (i : ℕ) < j then mget H' i j else 0)

end QuadFormsKB.Siegel.Kneser.Gen
