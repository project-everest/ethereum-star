let contract() =
  mstore [0x40uy] [0x60uy];
  let x_1 = pow [0x02uy] [0xE0uy] in
  let x_2 = get_calldataload [0x00uy] in
  let x_3 = div x_2 x_1 in
  let x_4 = eqw x_3 [0x57uy; 0xEAuy; 0x89uy; 0xB6uy] in
  if nonZero x_4 then
    begin (* offset: 46 *)
    let x_5 = pow [0x02uy] [0xA0uy] in
    let x_6 = x_5 - [0x01uy] in
    let x_7 = get_caller () in
    let x_8 = land x_7 x_6 in
    mstore [0x00uy] x_8;
    mstore [0x20uy] [0x00uy];
    let x_9 = sha3 [0x00uy] [0x40uy] in
    let x_10 = sload x_9 in
    let inputs = loadLocal [0x60uy] [0x00uy] in
    let (result,gasLeft) = call x_8 [0x00uy] x_10 inputs in
    let x_11 =
      match result with
      | Some outputs -> localStore [0x60uy] [0x00uy] outputs; one
      | None         -> zero in
    let x_12 = get_caller () in
    let x_13 = pow [0x02uy] [0xA0uy] in
    let x_14 = x_13 - [0x01uy] in
    let x_15 = land x_14 x_12 in
    mstore [0x00uy] x_15;
    let x_16 = [0x20uy] + [0x00uy] in
    mstore x_16 [0x00uy];
    let x_17 = [0x20uy] + x_16 in
    let x_18 = sha3 [0x00uy] x_17 in
    sstore x_18 [0x00uy];
     [] (* no returned outputs *)
    end
  else
    begin (* offset: 24 *)
    let x_19 = eqw [0xEDuy; 0x21uy; 0x24uy; 0x8Cuy] x_3 in
    if nonZero x_19 then
      begin (* offset: 131 *)
      let x_20 = pow [0x02uy] [0xA0uy] in
      let x_21 = x_20 - [0x01uy] in
      let x_22 = get_caller () in
      let x_23 = land x_22 x_21 in
      mstore [0x00uy] x_23;
      mstore [0x20uy] [0x00uy];
      let x_24 = sha3 [0x00uy] [0x40uy] in
      let x_25 = sload x_24 in
      let x_26 = get_callvalue () in
      let x_27 = x_26 + x_25 in
      sstore x_24 x_27;
       [] (* no returned outputs *)
      end
    else
      begin (* offset: 34 *)
      let x_28 = eqw [0xF8uy; 0xF8uy; 0xA9uy; 0x12uy] x_3 in
      if nonZero x_28 then
        begin (* offset: 165 *)
        let x_29 = pow [0x02uy] [0xA0uy] in
        let x_30 = x_29 - [0x01uy] in
        let x_31 = get_caller () in
        let x_32 = land x_31 x_30 in
        mstore [0x00uy] x_32;
        mstore [0x20uy] [0x00uy];
        let x_33 = sha3 [0x00uy] [0x40uy] in
        let x_34 = sload x_33 in
        mstore [0x60uy] x_34;
        loadLocal [0x60uy] [0x20uy] (* returned outputs *)
        end
      else
        begin (* offset: 44 *)
         [] (* no returned outputs *)
        end
      end
    end
