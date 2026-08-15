/-
Authors: Malhar A. Patel
-/

import GoLean.Core.Types

/-!
# Rules of Go

A `Ruleset` is a record of independent toggles.
The named presets (Japanese / Chinese / Tromp-Taylor / AGA) set specific toggles.
You can set your own rules by modifying the toggles.

Komi is stored as double the value (`komi2 = 13` means 6.5),
so all scoring is exact integer arithmetic.
-/

namespace GoLean

/-- `KoRule` sets which repetitions of position are forbidden. -/
inductive KoRule where
  /-- Forbid recreating the previous position (immediate ko recapture). -/
  | simple
  /-- Forbid recreating *any* previous position. -/
  | positionalSuperko
  /-- Forbid recreating any previous (position, player-to-move) pair. -/
  | situationalSuperko
  /-- No repetition check. -/
  | none
  deriving DecidableEq, Repr, Inhabited

def KoRule.describe : KoRule → String
  | .simple => "simple ko"
  | .positionalSuperko => "positional superko"
  | .situationalSuperko => "situational superko"
  | .none => "no ko rule"

/-- Canonical short name, used on the wire and in SGF `RU` values. -/
def KoRule.wireName : KoRule → String
  | .simple => "simple"
  | .positionalSuperko => "positional"
  | .situationalSuperko => "situational"
  | .none => "none"

def KoRule.ofWireName? : String → Option KoRule
  | "simple" => some .simple
  | "positional" => some .positionalSuperko
  | "situational" => some .situationalSuperko
  | "none" => some .none
  | _ => Option.none

/-- `ScoringMethod` sets how the final position is scored. -/
inductive ScoringMethod where
  /-- Japanese-style: territory + prisoners. -/
  | territory
  /-- Chinese/Tromp-Taylor-style: territory + living stones. -/
  | area
  deriving DecidableEq, Repr, Inhabited

def ScoringMethod.describe : ScoringMethod → String
  | .territory => "territory"
  | .area => "area"

/-- Canonical short name, used on the wire and in SGF `RU` values. -/
abbrev ScoringMethod.wireName : ScoringMethod → String := ScoringMethod.describe

def ScoringMethod.ofWireName? : String → Option ScoringMethod
  | "territory" => some .territory
  | "area" => some .area
  | _ => none

/-- The full rule configuration of a game. -/
structure Ruleset where
  ko : KoRule := .simple
  scoring : ScoringMethod := .territory
  selfCaptureAllowed : Bool := false
  /-- Twice the default komi (`13` = 6.5). -/
  defaultKomi2 : Int := 13
  /-- Consecutive passes that end the play phase. -/
  passesToScore : Nat := 2
  deriving DecidableEq, Repr, Inhabited

namespace Ruleset

def japanese : Ruleset := {}

def chinese : Ruleset :=
  { ko := .positionalSuperko, scoring := .area, defaultKomi2 := 15 }

def trompTaylor : Ruleset :=
  { ko := .positionalSuperko, scoring := .area,
    selfCaptureAllowed := true, defaultKomi2 := 15 }

def aga : Ruleset :=
  { ko := .situationalSuperko, scoring := .area, defaultKomi2 := 15 }

/-- Named presets, for the setup UI. -/
def presets : List (String × Ruleset) :=
  [("japanese", japanese), ("chinese", chinese),
   ("tromp-taylor", trompTaylor), ("aga", aga)]

/-- One-line human-readable summary. -/
def summary (rs : Ruleset) (komi2 : Int) : String :=
  s!"{rs.scoring.describe} scoring · {rs.ko.describe} · komi {formatHalfInt komi2}"
    ++ (if rs.selfCaptureAllowed then " · self-capture allowed" else "")

end Ruleset

end GoLean
