(*
   Copyright 2016 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
open Batteries
open BatOptParse

let _ =
  let infile_opt  = StdOpt.str_option ~metavar:"filename" () in
  let outfile_opt = StdOpt.str_option ~metavar:"filename" () in
  let pp_opt = StdOpt.store_true () in
  let gas_opt = StdOpt.store_true () in
  let print_const_opt = StdOpt.store_true () in
  let opt_parser  = OptParser.make () in
  OptParser.add opt_parser ~short_name:'i' ~long_name:"input" infile_opt;
  OptParser.add opt_parser ~short_name:'o' ~long_name:"output" outfile_opt;
  OptParser.add opt_parser ~short_name:'p' ~long_name:"print" pp_opt;
  OptParser.add opt_parser ~short_name:'g' ~long_name:"print_gas" ~help:"Outputs 'burn' commands corresponding to gas consumption" gas_opt ;
  OptParser.add opt_parser ~short_name:'c' ~long_name:"print_const" ~help:"Outputs commented int constants next to the corresponding byte arrays" print_const_opt ;
  let _ = OptParser.parse_argv opt_parser in
  try
    let infile =
      try Opt.get infile_opt
      with Opt.No_value -> ""
    in
    let outfile =
      try Opt.get outfile_opt
      with Opt.No_value -> ""                                      in
    let inbuf =
      if infile = "" then stdin else open_in infile in
    let outbuf =
      if outfile = "" then stdout else open_out outfile in
    let opcodes = Parse.parse inbuf in
    if Opt.get gas_opt then Disasm.gas_flag := true;
    if Opt.get pp_opt then
      Parse.pretty_print outbuf opcodes
    else
      let opcodes = Parse.pad_with_nop opcodes in
      Disasm.scan opcodes
  with
  | Sys_error err -> Printf.printf "%s\n" err
