val iota_def = 
  Rfunction `measure \(b,t). SUC t - b`
    `iota(bot, top) = 
      (bot > top => [] 
      | bot :: iota(bot+1,top))`;


