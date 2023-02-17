module PTSV.Translation.KPTSA2PAHORS

open PTSV.Core

module KPTSA2PAHORS =
    let translate (kptsa : KPTSA) : PAHORS =
        let gammaAmount = kptsa.maxGamma + 1
        failwith "todo"
        