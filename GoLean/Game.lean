import GoLean.Score

section GameFinish

structure GameFinish extends ScoreState where
  winner : Color

end GameFinish

section Game

inductive Stage where
  | setUp  (su : SetUp)
  | play   (gs : GameState)
  | score  (ss : ScoreState)
  | finish (gf : GameFinish)

inductive InvalidStageTransition where
  | alreadyStarted
  | gameOver
  | notScored
  | notEvenStarted

inductive StageTransitionResult where
  | valid
  | invalid (reason : InvalidStageTransition)

structure Game where
  stage      : Stage
  transition : StageTransitionResult

def Game.startGame (game : Game) (startCol : Color)
    : Game :=
  match game.stage with
  | .setUp su => {
    transition := .valid
    stage := .play {
      su with
      turn := startCol
    }
  }
  | .finish _ => {
    transition := .invalid .gameOver
    stage := game.stage
  }
  | _ => {
    game with
    transition := .invalid .alreadyStarted
  }



def Game.finish (game : Game) : Game :=
  match game.stage with
  | .score ss => {
    transition := .valid
    stage := .finish {
      ss with
      winner :=
        if ss.score.black > ss.score.white then .B
        else .W
    }
  }
  | .setUp _ => {
    game with
    transition := .invalid .notEvenStarted
  }
  | .play _ => {
    game with
    transition := .invalid .notScored
  }
  | .finish _ => {
    game with
    transition := .invalid .gameOver
  }

end Game
