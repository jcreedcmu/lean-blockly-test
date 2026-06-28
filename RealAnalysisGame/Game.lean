import Game.Levels.L1RealAnalysisStory
import Game.Levels.L1PsetIntro
import Game.Levels.L2NewtonsCalculationOfPi
import Game.Levels.Conversion

Title "Real Analysis, The Game"

Introduction "
# Welcome to Real Analysis, The Game!

This is a test build with one level.
"

Dependency RealAnalysisStory → NewtonsCalculationOfPi
Dependency RealAnalysisStory → L1Pset
Dependency RealAnalysisStory → Conversion

MakeGame
