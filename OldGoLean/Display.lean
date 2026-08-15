import GoLean.Basic

instance : ToString InvalidMoveReason where
  toString
    | .outOfBoard      => "Out of Board!"
    | .occupied        => "Occupied!"
    | .selfCapture     => "Self-Capture!"
    | .ko              => "Ko!"
    | .invalidNotation => "Invalid Notation!"
