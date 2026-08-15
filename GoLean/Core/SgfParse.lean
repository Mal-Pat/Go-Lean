/-
Authors: Malhar A. Patel
-/

import GoLean.Core.Sgf

/-!
# SGF import

`Sgf.load : String → Except String SgfImport` parses an SGF (FF[4]) string
into a `GameConfig` plus a move list, validated by replay. The moves
are folded through `Game.step`, so every successfully loaded game is
legal-by-construction and a corrupt file fails with a precise message
("SGF: illegal move 37: …").

Two stages:

1. **Syntax:** a small lexer (`(` `)` `;` identifiers, `[…]` values with
   `\` escapes) and a recursive-descent parser that follows only the
   main line (the first variation at every branch).
2. **Interpretation:** root properties (`SZ`, `KM`, `RU`, `HA`, `AB`,
   `AW`, `PL`, `PB`, `PW`) become the `GameConfig`; `B`/`W` nodes become
   `Action.play`/`Action.pass` (both `[]` and, on boards ≤ 19, `[tt]`
   mean pass).

Forgiving-import policies (each recorded in `warnings`):
- `HA[n]` with no `AB`: the first `n` leading Black moves are treated as
  handicap placement stones.
- A position repeat that the ruleset's ko rule would reject (a real game
  played under laxer rules): ko checking is disabled for that game.

Not supported (clear errors): variations as branches (main line only —
others are ignored), mid-game `AB`/`AW` setup nodes, non-alternating move
colors.
-/

namespace GoLean

/-! ## Stage 1: syntax -/

inductive SgfToken where
  | lparen
  | rparen
  | semi
  | ident (s : String)
  | value (s : String)
  deriving DecidableEq, Repr, Inhabited

structure SgfProp where
  ident : String
  values : List String
  deriving Repr, Inhabited

abbrev SgfNode := List SgfProp

/-- Tokenize an SGF string. Property values keep their content with `\`
escapes resolved; identifiers keep only uppercase letters (FF[3] compat). -/
def lexSgf (input : String) : Except String (List SgfToken) := do
  let mut toks : Array SgfToken := #[]
  let mut identAcc : List Char := []
  let mut inValue := false
  let mut escaped := false
  let mut valAcc : List Char := []
  for c in input.toList do
    if inValue then
      if escaped then
        valAcc := c :: valAcc
        escaped := false
      else if c == '\\' then
        escaped := true
      else if c == ']' then
        toks := toks.push (.value (String.ofList valAcc.reverse))
        valAcc := []
        inValue := false
      else
        valAcc := c :: valAcc
    else if c.isAlpha then
      identAcc := c :: identAcc
    else
      if !identAcc.isEmpty then
        toks := toks.push (.ident (String.ofList (identAcc.reverse.filter Char.isUpper)))
        identAcc := []
      if c == '[' then
        inValue := true
      else if c == '(' then
        toks := toks.push .lparen
      else if c == ')' then
        toks := toks.push .rparen
      else if c == ';' then
        toks := toks.push .semi
      else if c.isWhitespace || c.toNat == 0xFEFF then
        pure ()
      else
        throw s!"SGF: unexpected character '{c}'"
  if inValue then
    throw "SGF: unterminated property value (missing ']')"
  return toks.toList

private def takeValues : List SgfToken → List String × List SgfToken
  | .value v :: rest =>
    let (vs, r) := takeValues rest
    (v :: vs, r)
  | ts => ([], ts)

private def parsePropsAux : Nat → List SgfToken → SgfNode × List SgfToken
  | 0, ts => ([], ts)
  | fuel + 1, .ident i :: rest =>
    let (vs, rest') := takeValues rest
    let (props, rest'') := parsePropsAux fuel rest'
    (⟨i, vs⟩ :: props, rest'')
  | _ + 1, ts => ([], ts)

/-- Skip a balanced subtree (the opening `(` already consumed). -/
private def skipTreeAux : Nat → Nat → List SgfToken → Except String (List SgfToken)
  | _, 0, ts => return ts
  | 0, _, _ => throw "SGF: parser overflow"
  | fuel + 1, depth, t :: ts =>
    match t with
    | .lparen => skipTreeAux fuel (depth + 1) ts
    | .rparen => skipTreeAux fuel (depth - 1) ts
    | _ => skipTreeAux fuel depth ts
  | _ + 1, _, [] => throw "SGF: unbalanced parentheses"

/-- Skip the remaining sibling variations up to (and including) the `)`
closing the current tree. -/
private def skipSiblings : Nat → List SgfToken → Except String (List SgfToken)
  | 0, _ => throw "SGF: parser overflow"
  | fuel + 1, .lparen :: rest => do
    skipSiblings fuel (← skipTreeAux (rest.length + 1) 1 rest)
  | _ + 1, .rparen :: rest => return rest
  | _ + 1, _ => throw "SGF: expected a variation '(' or ')'"

/-- Parse the nodes of one tree, following only the first variation at
every branch (the main line). Assumes the opening `(` is consumed;
consumes through the matching `)`. -/
private def parseMainAux : Nat → List SgfToken → Array SgfNode →
    Except String (Array SgfNode × List SgfToken)
  | 0, _, _ => throw "SGF: parser overflow"
  | fuel + 1, ts, acc =>
    match ts with
    | .semi :: rest =>
      let (props, rest') := parsePropsAux rest.length rest
      parseMainAux fuel rest' (acc.push props)
    | .lparen :: rest => do
      -- The first variation continues the main line; siblings are ignored.
      let (sub, rest') ← parseMainAux fuel rest acc
      let rest'' ← skipSiblings (rest'.length + 1) rest'
      return (sub, rest'')
    | .rparen :: rest => return (acc, rest)
    | .ident i :: _ => throw s!"SGF: property {i} outside a node (missing ';')"
    | .value _ :: _ => throw "SGF: stray property value"
    | [] => throw "SGF: unbalanced parentheses"

/-- Parse the main line of the first game tree in an SGF string. -/
def parseSgfMainLine (input : String) : Except String (List SgfNode) := do
  let toks ← lexSgf input
  match toks with
  | .lparen :: rest =>
    let (nodes, _) ← parseMainAux (toks.length + 1) rest #[]
    if nodes.isEmpty then throw "SGF: empty game tree"
    return nodes.toList
  | _ => throw "SGF: expected '(' at the start"

/-! ## Stage 2: interpretation -/

private def propVal? (n : SgfNode) (id : String) : Option String :=
  (n.find? (·.ident == id)).map fun p => p.values.headD ""

private def propVals (n : SgfNode) (id : String) : List String :=
  ((n.find? (·.ident == id)).map (·.values)).getD []

/-- Inverse of `sgfLetter`. -/
def sgfLetterIdx? (c : Char) : Option Nat :=
  if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'Z' then some (26 + (c.toNat - 'A'.toNat))
  else none

/-- Decode an SGF point value into `(row, col)` (column letter first). -/
def sgfCoord? (v : String) : Option (Nat × Nat) :=
  match v.toList with
  | [cc, rc] => do return ((← sgfLetterIdx? rc), (← sgfLetterIdx? cc))
  | _ => none

/-- Parse a komi value (`"6.5"`, `"-2"`, `"0,5"`, …) into a doubled integer. -/
def parseKomi2? (v : String) : Option Int := do
  let v := v.trimAscii.toString
  let (neg, v) := if v.startsWith "-" then (true, v.drop 1) else (false, v)
  let mkRes (n2 : Nat) : Option Int :=
    some (if neg then -(n2 : Int) else (n2 : Int))
  match (v.replace "," ".").splitOn "." with
  | [whole] => mkRes (2 * (← whole.toNat?))
  | [whole, frac] => do
    let n ← if whole.isEmpty then some 0 else whole.toNat?
    let half ←
      match frac.toList.head? with
      | none => some 0
      | some '5' => some 1
      | some '0' => some 0
      | _ => none
    mkRes (2 * n + half)
  | _ => none

/-- Closest `Ruleset` for an SGF `RU` value (never fails; unknown values
default to Japanese). Understands the standard names plus the parseable
`Custom ko=… scoring=… selfcapture=… passes=…` form our export writes. -/
def rulesetOfRu (v : String) : Ruleset :=
  let l := v.trimAscii.toString.toLower
  if l.startsWith "custom" then
    (l.splitOn " ").foldl (init := ({} : Ruleset)) fun rs part =>
      match part.splitOn "=" with
      | ["ko", k] => { rs with ko := (KoRule.ofWireName? k).getD rs.ko }
      | ["scoring", sc] => { rs with scoring := (ScoringMethod.ofWireName? sc).getD rs.scoring }
      | ["selfcapture", b] => { rs with selfCaptureAllowed := b == "yes" }
      | ["passes", n] => { rs with passesToScore := n.toNat?.getD rs.passesToScore }
      | _ => rs
  else if l == "chinese" then .chinese
  else if l == "aga" then .aga
  else if l.startsWith "tromp" then .trompTaylor
  else if l == "nz" || l == "new zealand" || l == "goe" then .trompTaylor
  else .japanese

/-- The result of loading an SGF game. -/
structure SgfImport where
  config : GameConfig
  moves : Array Action
  warnings : List String := []

/-- Replay outcome: the game, or the 1-based move index that failed and why.
Config errors and non-alternating colors are fatal (`Except.error`). -/
private def replayMoves (cfg : GameConfig) (colMoves : Array (Color × Action)) :
    Except String (Sum Game (Nat × IllegalAction)) := do
  let g0 ←
    match Game.new cfg with
    | .ok g0 => pure g0
    | .error e => throw s!"SGF: {e.describe}"
  let mut g := g0
  let mut i := 0
  let mut failed : Option (Nat × IllegalAction) := none
  for (col, a) in colMoves do
    i := i + 1
    if g.curPlayState.toMove != col then
      throw s!"SGF: non-alternating move colors at move {i} are not supported"
    match g.step a with
    | .ok g' => g := g'
    | .error e =>
      failed := some (i, e)
      break
  match failed with
  | none => return .inl g
  | some f => return .inr f

/-- Parse and validate an SGF string into a game record. -/
def Sgf.load (input : String) : Except String SgfImport := do
  let nodes ← parseSgfMainLine input
  let root := nodes.headD []
  -- Board size: SZ[n] or SZ[cols:rows]; default 19.
  let (cols, rows) ←
    match propVal? root "SZ" with
    | none => pure (19, 19)
    | some v =>
      match v.splitOn ":" with
      | [n] =>
        match n.trimAscii.toString.toNat? with
        | some k => pure (k, k)
        | none => throw s!"SGF: bad SZ value '{v}'"
      | [w, h] =>
        match w.trimAscii.toString.toNat?, h.trimAscii.toString.toNat? with
        | some cw, some rh => pure (cw, rh)
        | _, _ => throw s!"SGF: bad SZ value '{v}'"
      | _ => throw s!"SGF: bad SZ value '{v}'"
  if rows > 52 || cols > 52 then
    throw "SGF: boards larger than 52×52 are not supported"
  let some size := Size.ofNats? rows cols
    | throw "SGF: board size must be at least 2×2"
  -- Rules and komi.
  let ruleset := ((propVal? root "RU").map rulesetOfRu).getD .japanese
  let komi2 ←
    match propVal? root "KM" with
    | none => pure ruleset.defaultKomi2
    | some v =>
      match parseKomi2? v with
      | some k => pure k
      | none => throw s!"SGF: bad KM value '{v}'"
  let handicap := ((propVal? root "HA").bind (·.trimAscii.toString.toNat?)).getD 0
  -- Setup stones.
  let decodeSetup (id : String) : Except String (List (Nat × Nat)) :=
    (propVals root id).mapM fun v =>
      match sgfCoord? v with
      | some rc => .ok rc
      | none => .error s!"SGF: bad {id} coordinate '{v}'"
  let setupBlack0 ← decodeSetup "AB"
  let setupWhite ← decodeSetup "AW"
  -- Moves (every node; a value of `[]`, or `[tt]` on boards ≤ 19, is a pass).
  let mut colMoves : Array (Color × Action) := #[]
  let mut nodeIdx := 0
  for n in nodes do
    nodeIdx := nodeIdx + 1
    for (id, col) in [("B", Color.black), ("W", Color.white)] do
      if (n.find? (·.ident == id)).isSome then
        let v := (propVal? n id).getD ""
        if v.isEmpty || (v == "tt" && rows ≤ 19 && cols ≤ 19) then
          colMoves := colMoves.push (col, .pass)
        else
          match sgfCoord? v with
          | some (r, c) => colMoves := colMoves.push (col, .play r c)
          | none => throw s!"SGF: bad move coordinate '{v}'"
    if nodeIdx > 1 && (!(propVals n "AB").isEmpty || !(propVals n "AW").isEmpty) then
      throw "SGF: mid-game AB/AW setup stones are not supported"
  let mut warnings : List String := []
  -- Forgiving import: HA with no AB means the leading Black moves are the
  -- handicap placement.
  let mut setupBlack := setupBlack0
  if handicap ≥ 2 && setupBlack.isEmpty then
    let leadingB := colMoves.toList.takeWhile fun (col, a) =>
      col == Color.black && (match a with | .play .. => true | _ => false)
    let take := min handicap leadingB.length
    if take ≥ 1 then
      setupBlack := (leadingB.take take).filterMap fun (_, a) =>
        match a with
        | .play r c => some (r, c)
        | _ => none
      colMoves := colMoves.extract take colMoves.size
      warnings := warnings ++
        [s!"HA[{handicap}] with no AB: treated the first {take} Black move(s) as handicap stones"]
  -- First mover: derived from the first move, or PL; normalized to `none`
  -- when it matches the engine's own convention (for clean round trips).
  let plColor? : Option Color :=
    match (propVal? root "PL").map (·.trimAscii.toString.toLower) with
    | some "b" => some .black
    | some "w" => some .white
    | _ => none
  let derived? := (colMoves[0]?.map (·.1)) <|> plColor?
  let cfg0 : GameConfig :=
    { size, ruleset, komi2, handicap, setupBlack, setupWhite
      blackName := ((propVal? root "PB").getD "Black")
      whiteName := ((propVal? root "PW").getD "White") }
  let cfg :=
    match derived?, cfg0.initialPlayState with
    | some col, .ok ps0 =>
      if ps0.toMove == col then cfg0 else { cfg0 with firstToMove := some col }
    | _, _ => cfg0
  -- Validate by replay; degrade the ko rule once if a repeat is the only
  -- obstacle (the game may have been played under a laxer ko rule).
  match ← replayMoves cfg colMoves with
  | .inl _ =>
    return { config := cfg, moves := colMoves.map (·.2), warnings }
  | .inr (i, .koViolation kr) =>
    let cfg' := { cfg with ruleset := { cfg.ruleset with ko := .none } }
    match ← replayMoves cfg' colMoves with
    | .inl _ =>
      return { config := cfg', moves := colMoves.map (·.2)
               warnings := warnings ++
                 [s!"move {i} repeats a position under {kr.describe}; ko checking disabled for this game"] }
    | .inr (j, e) => throw s!"SGF: illegal move {j}: {e.describe}"
  | .inr (i, e) => throw s!"SGF: illegal move {i}: {e.describe}"

end GoLean
