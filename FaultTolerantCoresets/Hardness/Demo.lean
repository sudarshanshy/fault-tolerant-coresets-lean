import FaultTolerantCoresets.Hardness.Examples

open FTC.Hardness FTC.Hardness.Encoding FTC.Hardness.Examples

def main : IO Unit := do
  let yesOutput := (fullReductionCode parameters.copies).eval yesSource
  let noOutput := (fullReductionCode parameters.copies).eval noSource
  let yesValue := exactFullSensitivity yesFull yesFull_valid
  let noValue := exactFullSensitivity noFull noFull_valid
  IO.println "Gap k-means to weighted sensitivity: rho=3, alpha=2, threshold=1/11"
  IO.println s!"YES instance weights: {(fullWeights yesOutput).map rational}"
  IO.println s!"NO instance weights: {(fullWeights noOutput).map rational}"
  IO.println s!"YES exact sensitivity: {yesValue}"
  IO.println s!"NO exact sensitivity: {noValue}"
  IO.println s!"YES accepted: {(thresholdCode (encodeRational parameters.threshold)).eval (encodeRational yesValue)}"
  IO.println s!"NO rejected: {!((thresholdCode (encodeRational parameters.threshold)).eval (encodeRational noValue))}"
  IO.println s!"YES construction bit-cost: {(fullReductionCode parameters.copies).cost yesSource}"
  IO.println s!"NO construction bit-cost: {(fullReductionCode parameters.copies).cost noSource}"
