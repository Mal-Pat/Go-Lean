import GoLean.Play

section ScoreState

structure Score where
  white : Float
  black : Float

structure ScoreState extends GameState where
  sboard : ScoreBoard size
  score  : Score

end ScoreState
