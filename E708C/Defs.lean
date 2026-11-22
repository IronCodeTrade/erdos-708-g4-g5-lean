/-! Computational part (no Mathlib): checkers, cost tables, search, enumeration. -/

namespace E708F

abbrev Opt := List (Nat × Nat) × List Nat

def isPrimeB (p : Nat) : Bool := 2 ≤ p && (List.range' 2 (p - 2)).all (fun k => p % k != 0)

def primeTab : Array Bool := (List.range 1001).map isPrimeB |>.toArray

def pT (p : Nat) : Bool := decide (p < 1001) && primeTab.getD p false

def validOpt (a : Nat) (o : Opt) : Bool :=
  o.1.all (fun pe => pT pe.1 && a % pe.1 ^ pe.2 == 0) &&
  decide ((o.1.map Prod.fst).Nodup) &&
  o.2.all (fun d => decide (0 < d)) &&
  ((o.1.map (fun pe => pe.1 ^ pe.2)).prod * o.2.prod) % a == 0

def stripAux : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, t, _, e => (e, t)
  | fuel+1, t, p, e => if t % p == 0 then stripAux fuel (t / p) p (e+1) else (e, t)

def atomsAux : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | fuel+1, t, p =>
    if t ≤ 1 then [] else if t < p * p then [(t, 1)]
    else if t % p == 0 then
      let r := stripAux t t p 0
      (p, r.1) :: atomsAux fuel r.2 (p+1)
    else atomsAux fuel t (p+1)

def atoms (a : Nat) : List (Nat × Nat) := atomsAux (a+1) a 2

/-- (chosen, rest) subsets -/

def subsetsL {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => (subsetsL xs).flatMap fun (s, r) => [(s, x :: r), (x :: s, r)]

/-- set partitions, as lists of block products -/

def partsL : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (partsL xs).flatMap fun P =>
      ((List.range P.length).map fun i => P.modify i (· * x)) ++ [P ++ [x]]

def optsOf (a : Nat) : List Opt :=
  (subsetsL (atoms a)).flatMap fun (s, r) =>
    (partsL (r.map fun pe => pe.1 ^ pe.2)).map fun P => (s, P)

def optLen (o : Opt) : Nat := o.1.length + o.2.length

def bestStep (a H m : Nat) (best : Option Opt) (o : Opt) : Option Opt :=
  if validOpt a o && o.2.all (fun d => decide (H * d ≤ m)) then
    match best with
    | none => some o
    | some b => if optLen o < optLen b then some o else best
  else best

def bestOpt (H m a : Nat) : Option Opt := (optsOf a).foldl (bestStep a H m) none

def bestLen (H m a : Nat) : Nat :=
  match bestOpt H m a with
  | some o => optLen o
  | none => 100

def optOf (l : List Nat) (cert : List Opt) (a : Nat) : Opt := ((l.zip cert).lookup a).getD ([], [])

def shL (l : List Nat) (cert : List Opt) : Nat := (l.map fun a => (optOf l cert a).1.length).sum

def cntL (m : Nat) (l : List Nat) (cert : List Opt) (d : Nat) : Nat :=
  (l.map fun a' => ((optOf l cert a').2.map fun d' => if m / d' ≤ m / d then 1 else 0).sum).sum

def checkTup (H m : Nat) (l : List Nat) (cert : List Opt) : Bool :=
  decide l.Nodup &&
  l.all (fun a => validOpt a (optOf l cert a) &&
    (optOf l cert a).2.all (fun d => decide (shL l cert + cntL m l cert d ≤ m / d))) &&
  decide (shL l cert + (l.map fun a => (optOf l cert a).2.length).sum ≤ H)

def okD (m L : Nat) (S : List Nat) : Bool :=
  S.all fun d => decide (0 < d) &&
    decide (L + (S.map fun d' => if m / d' ≤ m / d then 1 else 0).sum ≤ m / d)

def optsTab : Array (List Opt) := (List.range 1001).map optsOf |>.toArray

def search (H m : Nat) : List Nat → List Nat → Nat → Option (List Opt)
  | [], _, _ => some []
  | a :: rest, S, L =>
    (optsTab.getD a []).findSome? fun o =>
      let S' := S ++ o.2
      let L' := L + o.1.length
      if S'.length + L' + rest.length ≤ H && okD m L' S' then
        (search H m rest S' L').map (o :: ·)
      else none

def fullOK (H m : Nat) (l : List Nat) : Bool :=
  match search H m l [] 0 with
  | some cert => checkTup H m l cert
  | none => false

def mkC (H m : Nat) : Array Nat := (List.range (m+1)).map (bestLen H m) |>.toArray

def mkPM (cA : Array Nat) (m : Nat) : Array Nat :=
  (List.range m).foldl (fun acc d => acc.push (if d < 2 then 0 else max (acc.getD d 0) (cA.getD d 100))) #[0]

def enum4 (H m : Nat) (c pm : Nat → Nat) (full : List Nat → Bool) : Bool :=
  (List.range' 4 (m-4)).all fun d3 => decide (c m + c d3 + 2 * pm d3 ≤ H) ||
   (List.range' 3 (d3-3)).all fun d2 => decide (c m + c d3 + c d2 + pm d2 ≤ H) ||
    (List.range' 2 (d2-2)).all fun d1 => decide (c m + c d3 + c d2 + c d1 ≤ H) ||
      full [d1, d2, d3, m]

def enum5 (H m : Nat) (c pm : Nat → Nat) (full : List Nat → Bool) : Bool :=
  (List.range' 5 (m-5)).all fun d4 => decide (c m + c d4 + 3 * pm d4 ≤ H) ||
  (List.range' 4 (d4-4)).all fun d3 => decide (c m + c d4 + c d3 + 2 * pm d3 ≤ H) ||
   (List.range' 3 (d3-3)).all fun d2 => decide (c m + c d4 + c d3 + c d2 + pm d2 ≤ H) ||
    (List.range' 2 (d2-2)).all fun d1 => decide (c m + c d4 + c d3 + c d2 + c d1 ≤ H) ||
      full [d1, d2, d3, d4, m]

/-- tables are correct and the pruned enumeration passes, for one `m`. -/

def tabOK (H m : Nat) (c pm : Nat → Nat) : Bool :=
  ((List.range (m+1)).all fun a => c a == bestLen H m a) &&
  ((List.range' 2 (m-2)).all fun d => decide (c d ≤ pm (d+1)) && decide (pm d ≤ pm (d+1)))

def mOK4 (m : Nat) : Bool :=
  let cA := mkC 8 m
  let pA := mkPM cA m
  tabOK 8 m (fun a => cA.getD a 100) (fun d => pA.getD d 100) &&
  enum4 8 m (fun a => cA.getD a 100) (fun d => pA.getD d 100) (fullOK 8 m)

def mOK5 (m : Nat) : Bool :=
  let cA := mkC 10 m
  let pA := mkPM cA m
  tabOK 10 m (fun a => cA.getD a 100) (fun d => pA.getD d 100) &&
  enum5 10 m (fun a => cA.getD a 100) (fun d => pA.getD d 100) (fullOK 10 m)

def enum5r (H m : Nat) (c pm : Nat → Nat) (full : List Nat → Bool) (lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all fun d4 => decide (c m + c d4 + 3 * pm d4 ≤ H) ||
  (List.range' 4 (d4-4)).all fun d3 => decide (c m + c d4 + c d3 + 2 * pm d3 ≤ H) ||
   (List.range' 3 (d3-3)).all fun d2 => decide (c m + c d4 + c d3 + c d2 + pm d2 ≤ H) ||
    (List.range' 2 (d2-2)).all fun d1 => decide (c m + c d4 + c d3 + c d2 + c d1 ≤ H) ||
      full [d1, d2, d3, d4, m]

def mOK5r (m lo hi : Nat) : Bool :=
  let cA := mkC 10 m
  let pA := mkPM cA m
  tabOK 10 m (fun a => cA.getD a 100) (fun d => pA.getD d 100) &&
  enum5r 10 m (fun a => cA.getD a 100) (fun d => pA.getD d 100) (fullOK 10 m) lo hi

def parseUnits (s : String) : Array (Nat × Nat × Nat) :=
  ((s.splitOn "\n").filterMap fun ln =>
    match (ln.splitOn " ").filterMap String.toNat? with
    | [a, b, c] => some (a, b, c)
    | _ => none).toArray

def units5 : Array (Nat × Nat × Nat) := parseUnits (include_str "../units5.txt")

def unitOK (i : Nat) : Bool :=
  let u := units5.getD i (11, 5, 11)
  mOK5r u.1 u.2.1 u.2.2

def chunkS : Nat := 48

def chunkOK (k : Nat) : Bool := (List.range' (k * chunkS) chunkS).all unitOK

def covOK (K : Nat) : Bool :=
  (List.range' 11 989).all fun m =>
    let us := (List.range (K * chunkS)).filterMap fun i =>
      let u := units5.getD i (11, 5, 11)
      if u.1 == m then some (u.2.1, u.2.2) else none
    (List.range' 5 (m-5)).all fun d4 => us.any fun u => u.1 ≤ d4 && d4 < u.2

end E708F
