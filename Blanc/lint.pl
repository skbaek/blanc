#!/usr/bin/env swipl

:- initialization(main, main).
:- ['$PRELUDE'].

read_file_to_lines(NAME, LINES) :-
  read_file_to_string(NAME, STR, []),
  split_string(STR, "\n", "", LINES).

uppercase('A').
uppercase('B').
uppercase('C').
uppercase('D').
uppercase('E').
uppercase('F').
uppercase('G').
uppercase('H').
uppercase('I').
uppercase('J').
uppercase('K').
uppercase('L').
uppercase('M').
uppercase('N').
uppercase('O').
uppercase('P').
uppercase('Q').
uppercase('R').
uppercase('S').
uppercase('T').
uppercase('U').
uppercase('V').
uppercase('W').
uppercase('X').
uppercase('Y').
uppercase('Z').

lowercase('a').
lowercase('b').
lowercase('c').
lowercase('d').
lowercase('e').
lowercase('f').
lowercase('g').
lowercase('h').
lowercase('i').
lowercase('j').
lowercase('k').
lowercase('l').
lowercase('m').
lowercase('n').
lowercase('o').
lowercase('p').
lowercase('q').
lowercase('r').
lowercase('s').
lowercase('t').
lowercase('u').
lowercase('v').
lowercase('w').
lowercase('x').
lowercase('y').
lowercase('z').

letter(CHAR) :- uppercase(CHAR).
letter(CHAR) :- lowercase(CHAR).

digit('0').
digit('1').
digit('2').
digit('3').
digit('4').
digit('5').
digit('6').
digit('7').
digit('8').
digit('9').

valid_char(CHAR) :- letter(CHAR).
valid_char(CHAR) :- digit(CHAR).
valid_char('\'').
valid_char('.').
valid_char('ℕ').
valid_char('₀').
valid_char('₁').
valid_char('₂').
valid_char('₃').
valid_char('₄').
valid_char('₅').
valid_char('₆').
valid_char('₇').
valid_char('₈').
valid_char('₉').
valid_char('!').
valid_char('?').
valid_char('φ').
valid_char('ξ').
valid_char('σ').
valid_char('ρ').
valid_char('υ').
valid_char('_').
valid_char('Θ').
valid_char('Λ').
valid_char('α').
valid_char('Ξ').
valid_char('ₙ').

valid_string(ATOM) :- string_chars(ATOM, CHARS), maplist(valid_char, CHARS).
  
check_tokens(TOKENS) :- maplist(valid_string, TOKENS).
check_tokens(TOKENS) :- 
  format("Invalid tokens : ~w", [TOKENS]),
  throw(validity_fail).

break(LINE, WORDS) :- 
  split_string(LINE, " ,;^\"~⊚¬·{}⟨⟩±∅()[]⟪⟫*+-⊻↟≥\\⊢:×&=←$#π∘λ⦃⦄∃/∨∈∀@<≤`|>∧≠→⟦↦↔⟧%", "", TEMP),
  delete(TEMP, "", WORDS).

is_comment(STR) :- string_concat("--", _, STR), !.
is_comment(STR) :- string_concat(" ", SFX, STR), is_comment(SFX), !.

inert(STR) :- is_comment(STR), !.
% inert(STR) :- string_concat("#", _, STR).
% inert(STR) :- string_concat("%", _, STR).
inert(STR) :- string_concat("namespace", _, STR), !.
inert(STR) :- string_concat("open", _, STR), !.
inert(STR) :- string_concat("import", _, STR), !.
inert("end").
inert("").

primitive("_").
primitive("rcases").
primitive("apply").
primitive("by").
primitive("with").
primitive("if").
primitive("then").
primitive("else").
primitive("refine").
primitive("intros").
primitive("cases").
primitive("simp").
primitive("intros").
primitive("exact").
primitive("intro").
primitive("only").
primitive("rw").
primitive("unfold").
primitive("constructor").
primitive("first").
primitive("rw").
primitive("tactic").
primitive("have").
primitive("match").
primitive("macro_rules").

line_decl(["macro", NAME | _], NAME).
line_decl(["def", NAME | _], NAME).
line_decl(["definition", NAME | _], NAME).
line_decl(["partial", "def", NAME | _], NAME).
line_decl(["partial", "definition", NAME | _], NAME).
line_decl(["lemma", NAME | _], NAME).
line_decl(["theorem", NAME | _], NAME).
line_decl(["inductive", NAME | _], NAME).
line_decl(["structure", NAME | _], NAME).
line_decl(["abbrev", NAME | _], NAME).
line_decl(["syntax", NAME | _], NAME).
line_decl(["elab", NAME | _], NAME).
line_decl(["class", NAME | _], NAME).

line_name_rest(["macro", NAME | REST], NAME, REST).
line_name_rest(["def", NAME | REST], NAME, REST).
line_name_rest(["definition", NAME | REST], NAME, REST).
line_name_rest(["partial", "def", NAME | REST], NAME, REST).
line_name_rest(["partial", "definition", NAME | REST], NAME, REST).
line_name_rest(["lemma", NAME | REST], NAME, REST).
line_name_rest(["theorem", NAME | REST], NAME, REST).
line_name_rest(["inductive", NAME | REST], NAME, REST).
line_name_rest(["structure", NAME | REST], NAME, REST).
line_name_rest(["abbrev", NAME | REST], NAME, REST).
line_name_rest(["syntax", NAME | REST], NAME, REST).
line_name_rest(["elab", NAME | REST], NAME, REST).
line_name_rest(["class", NAME | REST], NAME, REST).

add_all([], TREE, TREE).
add_all([TOKEN | TOKENS], TREE, NEW_TREE) :- 
  rb_insert(TREE, TOKEN, c, TEMP), !,
  add_all(TOKENS, TEMP, NEW_TREE).

decl_used(DECL, TREE) :- rb_in(DECL, c, TREE), !.
decl_used(DECL, TREE) :-  
  split_string(DECL, ".", "", [_, TAIL]), !, 
  rb_in(TAIL, c, TREE).

loop(_, []).
loop(TREE, [LINE | LINES]) :- 
  line_decl(LINE, DECL), !, 
  (
    decl_used(DECL, TREE) -> 
    loop(TREE, LINES)
  ;
    format("Unused : ~w", [DECL]),
    throw(unused_def)
  ).
loop(TREE, [LINE | LINES]) :-
  add_all(LINE, TREE, NEW_TREE), !,
    loop(NEW_TREE, LINES).

rep(_, []).
rep(TREE, [decl(NAME, TOKENS) | DECLS]) :- 
    decl_used(NAME, TREE) -> 
    add_all(TOKENS, TREE, NEW_TREE), !,
    rep(NEW_TREE, DECLS)
  ;
    format("Unused : ~w", [NAME]),
    throw(unused_def).

header(LINE) :- line_decl(LINE, _).
header(["instance" | _]).
header(["notation" | _]).
header(["infix" | _]).
header(["infixr" | _]).

carve([], [], []).
carve([LINE | LINES], [], [[LINE | BODY] | DECLS]) :- 
  header(LINE), !, 
  carve(LINES, BODY, DECLS).
carve([LINE | LINES], [LINE | BODY], DECLS) :- 
  carve(LINES, BODY, DECLS).

gather([LINE | LINES], decl(NAME, TOKENS)) :- 
  line_name_rest(LINE, NAME, REST), !, 
  append([REST | LINES], TOKENS).

gather([[_ | REST] | LINES], decl("null", TOKENS)) :- 
  append([REST | LINES], TOKENS).

gather(LINES, _) :- 
  write_ln("FAILED!:"), 
  write_list(LINES),
  throw(gather_fail).

main :- 
  read_file_to_lines('BasicE.lean', BASIC),
  read_file_to_lines('TypesE.lean', TYPES),
  read_file_to_lines('Hash.lean', HASH),
  read_file_to_lines('EC.lean', EC),
  read_file_to_lines('Execution.lean', EXEC),
  read_file_to_lines('../Blanc.lean', BLANC),
  append([BASIC, TYPES, HASH, EC, EXEC, BLANC], L0),
  exclude(inert, L0, L1),
  maplist(break, L1, L2),
  maplist(exclude(primitive), L2, LINES),
  carve(LINES, [], LINESS),
  maplist(gather, LINESS, REV),
  reverse(REV, DECLS),
  rb_new(EMPTY),
  add_all(
    [
      "null",
      "main",
      "exec",
      "BLSP12",
      "run",

      "recover",
      "pseudoBinaryEncoding",
      "List.toStrings",
      "mkProlog",

      "Option.toIO",

      "Linst.run",
      "Jinst.run",
      "Rinst.run",
      "Evm.extCost",
      "Evm.rollback",
      "Mem.read",
      "Mem.write",
      "Mem.extend",
      "Mem.extends",
      "Evm.popN",
      "Evm.stackTop",
      "Evm.pop'",
      "Evm.pop",
      "Evm.getInst",
      "Evm.popToNat",

      "State.setCode",
      "Acct.Erasable",

      "State.set",
      "State.get",
      "Tra.set",
      "Stor.set",
      "State.setStorVal",
      "Benv.setStorVal",
      "Msg.setStorVal",
      "Evm.setStorVal",

      "Evm.getAcct",
      "Evm.getOrigAcct",
      "Evm.getStorVal",
      "Evm.getBal",
      "Evm.getCode",

      "Tra.setStorVal",
      "Tenv.setTransVal",
      "Msg.setTransVal",
      "Evm.setTransVal",
      "Evm.getTransVal",
      "Evm.getOrigStorVal",
      "Evm.memRead",
      "Evm.memWrite",
      "Evm.memExtends",
      "Evm.assertDynamic",
      "Evm.addLog",
      "Evm.addBal",
      "Evm.setBal",
      "Msg.setBal",
      "Evm.subBal",
      "Msg.subBal",
      "Msg.addBal",
      "Evm.setCode",
      "Msg.setCode",
      "Benv.setStor",
      "Benv.addBal",
      "Benv.subBal",
      "Benv.setBal",
      "State.setBal",
      "State.addBal",
      "State.subBal",
      "Benv.incrNonce",
      "State.incrNonce",
      "Msg.incrNonce",
      "Evm.incrNonce",
      "State.setStor",
      "Inst.toOpString",
      "Ninst.toOpString",
      "Jinst.toOpString",
      "Linst.toOpString",
      "Nat.toHex",
      "Nat.toHexit",
      "Adr.toB256",
      "maxInitCodeSize",
      "B256.bytecount",
      "B256.zerocount",
      "Stor.toNTB",
      "BLT.toAccessList",
      "Block.toBLT",
      "Tx.toBLT",
      "AccessList.toBLT",
      "AccessList.toStrings",
      "TxType.receiver?",

      "NTB.maxKeyLength",
      "NTB.factor",
      "NTBs.update",
      "NTB.toStrings",
      "B128.toNat",

      "Evm.toStrings",
      "List.slice!",
      "List.sliceD",
      "List.slice?",
      "Benv.toStrings",
      "Msg.toStrings",
      "Tra.toStrings",
      "Nat.toBool",
      "BNP.toBNP12",
      "EllipticCurve.isOnCurve",
      "GaloisField.ofNat",
      "FinField.ofInt",
      "B256.keccak",
      "Nat.toB256",
      "Nat.toB128",

      "B8.toHexit",
      "B8.lows",
      "B8.highs",
      "B16.lows",
      "B16.highs",
      "B32.lows",
      "B32.highs",
      "B64.lows",
      "B64.highs",
      "B64.lows'",
      "B64.highs'",
      "B64.teg",
      "B128.teg",
      "B64.toB8V",
      "B128.toB8V",
      "B128.toB8L",
      "B256.teg",
      "B256.toB8V",
      "String.keccak",
      "String.dropZeroes",
      "B8.lowBit",
      "B8.highBit",
      "B16.lowBit",
      "B16.highBit",
      "B32.lowBit",
      "B32.highBit",
      "B64.lowBit",
      "B64.highBit",
      "B128.lowBit",
      "B128.highBit",
      "B256.lowBit",
      "B256.highBit",
      "ByteArray.run",
      "B8L.run",
      "B8L.toB8V",
      "B8L.pack",
      "B8L.toB128Diff",
      "B8L.ripemd160",
      "Bytes.run",
      "Lean.Json.toString",
      "Lean.Json.toStrings",
      "Lean.Jsons.toStrings",
      "StringJsons.toStrings",
      "BLTs.toStringss",
      "BLTs.toB8L",
      "B8L.toBLTs?",

      "Option.toExcept",
      "Nat.toB8L",
      "Nat.toB8LPack",

      "B8.toBools",
      "B8.toLinst",
      "B8.toXinst",
      "B8.toJinst",
      "B8.toRinst",
      "B256.lt_check",
      "B256.gt_check",
      "B256.slt_check",
      "B256.sgt_check",
      "B256.eq_check",
      "B256.toB4s",
      "B128.toB4s",
      "B64.toB4s",
      "B32.toB4s",
      "B16.toB4s",
      "B8.toB4s",
      "B32.toB8L",
      "B16.toB8L",
      "Array.sliceD",
      "ByteArray.sliceD",


      "List.maxD",
      "Ninst.run",
      "Except.print",
      
      "Nat.toAdr",
      "Adr.toNat",
      "showLim",
      "showStep",
      "State.getCode",
      "State.getStor",
      "State.getNonce",
      "Except.toIO",
      "List.putIndex",
      "Lean.Json.find",
      "Lean.Json.find?",
      "Lean.Json.toHeader",
      "Lean.Json.toString?",
      "BLT.toExStrBlock",
      "BLT.toExStrTx",
      "B8L.toExStrTx",
      "Receipt.toBLT",
      "Tx.isTypeFour",
      "Tx.isTypeThree",
      "B8L.toByteArray",
      "Sta.toStrings",
      "KeySet.toStrings",
      "Lean.Json.toAcct"
    ], 
    EMPTY, 
    TREE
  ),
  rep(TREE, DECLS).



% main :- 
%   read_file_to_lines('basic.lean', BASIC),
%   read_file_to_lines('evm.lean', EVM),
%   read_file_to_lines('common.lean', COMMON),
%   read_file_to_lines('weth.lean', WETH),
%   read_file_to_lines('backed.lean', BACKED),
%   append([BASIC, EVM, COMMON, WETH, BACKED], REV),
%   reverse(REV, L0),
%   exclude(inert, L0, L1),
%   maplist(break, L1, L2),
%   %maplist(check_tokens, TOKENSS).
%   maplist(exclude(primitive), L2, LINES),
%   rb_new(EMPTY),
%   add_all(["null", "transact_inv_backed", "printDeployerCode", "withoutPosition"], EMPTY, TREE),
%   loop(TREE, LINES).